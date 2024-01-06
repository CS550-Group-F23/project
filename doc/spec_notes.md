# Systolic spec

- Input parameter declarations
    - Can describe matrices or vectors.
- Cell behavior declarations
    - 

# systolic array design choices

can describe the inputs as a single row of the matrix
and then add the shift registers to offset the input inside the systolic array
control unit supplies one row at a time


# systolic spec description

general info user provides:

- input arrays: number of dimensions, name
- index dimensions: essentially the dimensions of the systolic array (i, j)
- cell specification:
    - list of ports on each cell
    - CellPort class with only a name, ports defined separately
    - adt with input port list and output port list
    - internal register inside cell can be modeled as an output port and an input port
    - every output port has an Expr that describes a general purpose computation, based on the value at the cell's ports (so you can only express the output of the cell as an expression of what is at the input ports)
- input specification:
    - SystemPort class, defines a name and a schedule that, given the system index dimensions, how is the input fed over time
- connectivity specification:
    - "space schedule" over the system index dimensions how are things connected

compiler constructs a function for each port on the cell
also a function for each system port, but the cell ports simply call these (e.g. in the base case)
the function for output cell ports is given by the expression provided by the user, this is a simple printing process
the function for the input cell ports is given by the connectivity expression, this is TBD