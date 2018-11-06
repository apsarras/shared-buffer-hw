/**
 * @info Generic And-Or Multiplexer
 *
 * @author Anastasios Psarras (a.psarras4225@gmail.com)
 *
 * @license MIT license -- check license.md
 *
 * @brief Generic multiplexer implemented by an AND-OR tree, selected by at-most-one-hot signal ('sel_i').
 *        Contains combinational logic only. 
 *
 * @param N  number of inputs
 * @param DW common data width for each input and the output
 */
 
module and_or_mux
#(
    parameter int N     = 4,
    parameter int DW    = 16
)
(
    input  logic[N-1:0][DW-1:0] data_i,
    input  logic[N-1:0]         sel_i,
    output logic[DW-1:0]        data_o
);

logic tmp;

always_comb begin: mux
    for(int w=0; w < DW; w=w+1) begin
        tmp = 0;
        for(int i=0; i < N; i=i+1) begin
            tmp = tmp | ( sel_i[i] & data_i[i][w] );
        end
        data_o[w] = tmp;
    end
end

endmodule
