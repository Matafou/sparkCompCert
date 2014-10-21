
package body proc1 is

   procedure P1 (ARG: in out Integer; ARG2: in Integer) is
      N : Boolean := True;
   begin
      ARG := ARG + 7;
   end;

end proc1;
