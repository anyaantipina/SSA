export function w $main(l %fmt) {
@b1
  %x =w copy 1
  jnz %x, @b3, @b4
@b2
  jmp @b4
@b3
  jmp @b5
@b4
  jmp @b5
@b5
  jnz %x, @b6, @b7
@b6
  jmp @b7
@b7
  jnz %x, @b8, @b5
@b8
  ret 0
}
