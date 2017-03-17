module sha1(input logic clk, reset_n, start,
            input logic [31:0] message_addr, size, output_addr,
           output logic done, mem_clk, mem_we,
           output logic [15:0] mem_addr,
           output logic [31:0] mem_write_data,
            input logic [31:0] mem_read_data);

			
	logic [15:0] block_total, read_total;	//number of blocks to process
	logic [7:0] t, read_count, block_count, write_count;
	logic [31:0] read_addr,write_addr;
	logic [31:0] one_bit_zero_bit, all_ones;
	logic [31:0] a, b, c, d, e, w_t;	//algorithm variables for sha1
	
	logic [31:0] w[0:15];		//array to store wt
	
	logic [31:0] H0, H1, H2, H3, H4, hash0, hash1, hash2, hash3, hash4;
	
	assign H0 = 32'h67452301;
	assign H1 = 32'hefcdab89;
	assign H2 = 32'h98badcfe;
	assign H3 = 32'h10325476;
	assign H4 = 32'hc3d2e1f0;
	
		
	assign all_ones = 32'hFFFFFFFF;
	assign one_bit_zero_bit = 32'b1;
	
	enum logic [2:0] {SETUP=3'b000, HASH_W_SHA1=3'b010, WRITE_HASH_SHA1=3'b011, READ_DELAY_SHA1 = 3'b100} state;
	
	
	function logic[31:0] changeEndian(input logic [31:0] value);
		//Convert from little_endian to big_endian
		changeEndian = {value[7:0], value[15:8], value[23:16], value[31:24]};
	endfunction
		
	function logic[15:0] calcNumBlocks(input logic [31:0] size_of_message);
		//Calculates the number of 512 bit blocks needed to hash the message
		logic [31:0] num_blocks, size_bits;
		
		num_blocks = 0;
		size_bits = size_of_message * 8;			//convert size to bits
		size_bits = size_bits + 64 + 1;	//add the number bits needed for sha-1
	

		num_blocks = size_bits/512;		//split into 512 bit blocks
		num_blocks = num_blocks + 1;	//add 1 to accomodate for truncation
		calcNumBlocks = num_blocks;
	
	endfunction
	
	
	function logic [159:0] hashOp(input logic [31:0] a, b, c, d, e, w,
								   input logic [7:0] t);
		//algorithm to sha1, takes in abcde and w, spits out new abcde
					
		logic [31:0] k, F, a1, b1, c1, d1, e1, T;
		F=0;
		k=0;
	
		if ((0 <= t) && (t <= 19)) 
			begin
				k = 32'h5a827999;
				F = (b & c) ^ ((~b) & d);
			end
			
		else if ((20 <= t) && (t <= 39)) 
			begin
				k = 32'h6ed9eba1;
				F = b ^ c ^ d;
			end
			
		else if ((40 <= t) && (t <= 59))
			begin
				k = 32'h8f1bbcdc;
				F = (b & c) ^ (b & d) ^ (c & d);
			end

		else if ((60 <= t) && (t <= 79))
			begin
				k = 32'hca62c1d6;
				F = b ^ c ^ d;
			end
		
	
		T = rotateLeft(a,5) + F + w + k + e;
		
		a1 = T;
		b1 = a;
		c1 = rotateLeft(b,30);
		d1 = c;
		e1 = d;

		$display("\nhashOp values:\n");
		$display("t = %d\n", t);
		$display("w_hash = %h\n", w);
		$display("a1 = %h\n", a1);
		$display("b1 = %h\n", b1);
		$display("c1 = %h\n", c1);
		$display("d1 = %h\n", d1);
		$display("e1 = %h\n", e1);
		$display("e1 = %h\n", e1);
		$display("F = %h\n", F);
		$display("k = %h\n", k);

	
		hashOp = {a1,b1,c1,d1,e1};
		
	endfunction
	
	function logic [159:0] addHash(input logic[159:0] origHash, input logic[159:0] newHash);
		//Adds two hash values
		logic[31:0] a2,b2,c2,d2,e2;
		a2 = origHash[159:128] + newHash[159:128];
		b2 = origHash[127:96] + newHash[127:96];
		c2 = origHash[95:64] + newHash[95:64];
		d2 = origHash[63:32] + newHash[63:32];
		e2 = origHash[31:0] + newHash[31:0];
		
		/*
		$display("\n----------------\n");
		$display("OrighHash = %h\n",OrigHash);
		$display("NewHash = %h\n", NewHash);
		$display("a2 = %h\n",a2);
		$display("b2 = %h\n",b2);
		$display("c2 = %h\n",c2);
		$display("d2 = %h\n",d2);
		$display("e2 = %h\n",e2);
		*/
		
		addHash = {a2,b2,c2,d2,e2};
		
	endfunction
		
		
	
	
	function logic [31:0] rotateLeft(input logic[31:0] rotate_this, input logic[4:0] rotate_amount);
		//
		rotateLeft = ((rotate_this << rotate_amount) | (rotate_this >> 32-rotate_amount));
		
	endfunction
	
	
	function logic [31:0] calcNumReads(input logic[31:0] size_of_message);
		//Calculate number of times needed to read from memory
		logic[15:0] num_reads;
		num_reads = size_of_message/4;
		if (size_of_message%4 != 0)
			begin
				num_reads = num_reads+1;
			end
			
		calcNumReads = num_reads;
		
	endfunction

	
	
	logic [1:0] delay;
	
	assign block_total = calcNumBlocks(size);
	assign read_total = calcNumReads(size);
	
	always_ff @(posedge clk, negedge reset_n)
	begin
		if (!reset_n) begin
			state <= SETUP;
		end else
		
			case(state)
				SETUP:
					if(start) begin
					
						read_addr <= message_addr;		//read_addr gets the first location of the message
						mem_addr <= message_addr;		//tell testbench where to read from
						write_addr <= output_addr;
						mem_we <= 1'b0;					//tell tesbench we want to read
						
						t <= 0;							//start t at 0
						read_count <= 0;
						write_count <= 0;
						block_count <= 0;
												
						a<=H0;							//initialize a,b,c,d,e to constants H0 to H4
						b<=H1;
						c<=H2;
						d<=H3;
						e<=H4;
						
						hash0<=H0;						//initialize hash0 to hash4 to constants H0 to H4
						hash1<=H1;
						hash2<=H2;
						hash3<=H3;
						hash4<=H4;
						
						state <= HASH_W_SHA1;

						delay <= 0;
					end		
						
				READ_DELAY_SHA1:
					//state used solely to delay one clock cycle before reading
					begin
						delay<=1;
						mem_addr <= read_addr;
						read_addr <= read_addr+1;
						state <= HASH_W_SHA1;
						$display("DELAYED");
					end
				
				HASH_W_SHA1:
					begin
						if(t<16) begin

							if(read_count < read_total) begin

								if (delay!=1) begin
									state <= READ_DELAY_SHA1;
									read_addr <= read_addr + 1;
									$display("about to delay");

								end else begin
								
									//if on last read and the message is not divisible into words
									if((read_count == read_total-1) && (size%4 != 0)) begin
										
								
										//math to add the 1
										w[t] <= ((changeEndian(mem_read_data)) | one_bit_zero_bit<<(8*(4-size%4)-1)) & all_ones<<(8*(4-size%4)-1);
										{a,b,c,d,e} <= hashOp(a,b,c,d,e,((changeEndian(mem_read_data)) | one_bit_zero_bit<<(8*(4-size%4)-1)) & all_ones<<(8*(4-size%4)-1),t);
										
									end else begin
										w[t] <= changeEndian(mem_read_data);		//otherwise keep reading
										{a,b,c,d,e} <= hashOp(a,b,c,d,e,changeEndian(mem_read_data),t);
										
										$display("t: %d\n", t);
										$display("Data reading: %h\n", changeEndian(mem_read_data));
									end 
									
									mem_addr <= read_addr;	//tell testbench which address you're reading from	
									read_addr <= read_addr +1;	//increment the address you're reading from
									read_count <= read_count + 1;	
									state <= HASH_W_SHA1;
									t <= t+1;
								end

							end else if(read_count >= read_total) begin		//if you're done reading
								read_count <= read_count + 1;
								t <= t+1;
								state <= HASH_W_SHA1;
								if ((read_count == read_total) && (size%4 == 0)) begin //condition to padd 1000000...
									
									w[t] <= one_bit_zero_bit<<31;
									{a,b,c,d,e} <= hashOp(a,b,c,d,e,one_bit_zero_bit<<31,t);
									
								end else if(block_count == (block_total-1) && t == 15) begin //condition to pad size
								
									w[t] <= size*8; //size*8 = size representation in bits
									{a,b,c,d,e} <= hashOp(a,b,c,d,e,size*8,t);
									
								end else begin
									w[t] <= 32'b0;	//pad with 0s
									{a,b,c,d,e} <= hashOp(a,b,c,d,e,32'b0,t);
								end
							end

						end else if ((t>=16) & (t<79)) begin	//creating w[16] to w[79]
						
							if (t==16) begin
								block_count<=block_count+1;		//after finishing a block
								delay <= 0;
								mem_addr <= mem_addr - 1;		//fix the offset
								read_addr <= mem_addr - 1;
							end
							t <= t+1;
							
							//for(int i = 0; i<15; i++) w[i] <= w[i+1];

							w[15] <= rotateLeft((w[16-3] ^ w[16-8] ^ w[16-14] ^ w[16-16]),1);
							{a,b,c,d,e} <= hashOp(a,b,c,d,e,rotateLeft((w[16-3] ^ w[16-8] ^ w[16-14] ^ w[16-16]),1),t);
							
							for(int i = 0; i<15; i++) w[i] <= w[i+1];	//shift all w registers
							
							
						end else if (t==79) begin
							{hash0,hash1,hash2,hash3,hash4} <= addHash({hash0,hash1,hash2,hash3,hash4}, hashOp(a,b,c,d,e,rotateLeft((w[16-3] ^ w[16-8] ^ w[16-14] ^ w[16-16]),1),t));
												{a,b,c,d,e} <= addHash({hash0,hash1,hash2,hash3,hash4}, hashOp(a,b,c,d,e,rotateLeft((w[16-3] ^ w[16-8] ^ w[16-14] ^ w[16-16]),1),t));

							if (block_count!=block_total) begin
								t <= 0;
								state <= HASH_W_SHA1;
								
							end else if (block_count == block_total) begin
								mem_addr <= write_addr;
								mem_we <= 1; 
								state <= WRITE_HASH_SHA1;
							end
						
						end

					end
					
				WRITE_HASH_SHA1:
					begin
						case(write_count)
							0: begin
								mem_addr <= output_addr;
								mem_write_data <= hash0;
								
							end
							
							1: begin
								mem_addr <= output_addr +1;
								mem_write_data <= hash1;
							end
							
							2: begin 
								mem_addr <= output_addr +2;
								mem_write_data <= hash2;
							end
							
							3: begin
								mem_addr <= output_addr +3;
								mem_write_data <= hash3;
							end
							
							4: begin 
								mem_addr <= output_addr +4;
								mem_write_data <= hash4;
							end
									
						endcase
						
						write_count<=write_count+1;
						
						if(write_count < 5) begin
							state <= WRITE_HASH_SHA1;
						end else begin
							state <= SETUP;	//done writing on 5th cycle
						end
					end
												
			endcase
	end
	
	assign done = (write_count==(5+1));		//ensures done = 1 after 5th cycle
	assign mem_clk = clk;
				
					
endmodule