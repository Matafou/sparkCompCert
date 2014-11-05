with Ada.Text_IO;
with Ada.Integer_Text_IO;
use Ada.Text_IO;
use Ada.Integer_Text_IO;

package body G is

   procedure G (X: in out Integer) is
      X2:  Integer := 1;

      procedure L (Y: in Integer) is
	 Y2: Integer := 1;
      begin
         X2 := X2 * Y;
         if Y < X then L(Y+1); end if;
      end;

   begin
      L(X2);
      Put(X2);
      X := X2;
   end;

end;

