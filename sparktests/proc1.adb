
package body proc1 is

   M: Integer := 27;
   
   procedure P1 (ARG: in out Integer; ARG2: in Integer) is
      N : Boolean := True;
   begin
      ARG := ARG + M;
      ARG := ARG + ARG2;
   end;

end proc1;
