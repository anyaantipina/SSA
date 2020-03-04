export function w $main(l %fmt) {
@start
  %p =l alloc4 4
  %t =w call $scanf(l %fmt, l %p)
  %x =w loadw %p
  jnz %x, @block1, @block3
@block1
  %x =w sub %x, 3
  jnz %x, @block2, @end
@block2
  %x =w sub %x, 2
@block3
  %x =w add %x, 7
  jnz %x, @block1, @block2
@end
  ret %x
}
