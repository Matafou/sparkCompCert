
package body proc1 is

   M: Integer := 27;
   
   procedure P1 (ARG: in out Integer; ARG2: in Boolean) is
      N : Boolean := True;
   begin
      ARG := ARG + M;
   end;

end proc1;
