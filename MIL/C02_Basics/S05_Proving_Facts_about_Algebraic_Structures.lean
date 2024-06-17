import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  have : ∀ a b : α, a ⊓ b ≤ b ⊓ a := by
    intro a b
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  apply le_antisymm
  repeat apply this

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf
    · show x ⊓ y ⊓ z ≤ x
      apply le_trans
      apply inf_le_left
      apply inf_le_left
    · show x ⊓ y ⊓ z ≤ y ⊓ z
      apply le_inf
      · show x ⊓ y ⊓ z ≤ y
        apply le_trans
        apply inf_le_left
        apply inf_le_right
      · show x ⊓ y ⊓ z ≤ z
        apply le_trans
        apply inf_le_right
        exact le_refl z
  · show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    apply le_inf
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply inf_le_inf
      · exact le_refl x
      · apply inf_le_left
    · show x ⊓ (y ⊓ z) ≤ z
      apply le_trans
      apply inf_le_right
      apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  have : ∀ a b : α, a ⊔ b ≤ b ⊔ a := by
    intro a b
    apply sup_le
    apply le_sup_right
    apply le_sup_left
  apply le_antisymm
  repeat apply this

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry -- similiar to the one above

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · show x ⊓ (x ⊔ y) ≤  x
    apply inf_le_left
  · show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    · exact le_refl x
    · show x ≤ x ⊔ y
      exact le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · show x ⊔ x ⊓ y ≤ x
    apply sup_le
    · exact le_refl x
    · show x ⊓ y ≤ x
      exact inf_le_left
  · show x ≤ x ⊔ x ⊓ y
    exact le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, inf_comm (a ⊔ b) a, absorb1, inf_comm (a ⊔ b) c, h, ← sup_assoc, inf_comm c a, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  show a ⊓ (b ⊔ c) = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c)
  rw [sup_comm (a ⊓ b) a]
  show a ⊓ (b ⊔ c) = (a ⊔ a ⊓ b) ⊓ (a ⊓ b ⊔ c)
  rw [absorb2]
  show a ⊓ (b ⊔ c) = a ⊓ (a ⊓ b ⊔ c)
  rw [sup_comm (a ⊓ b) c]
  show a ⊓ (b ⊔ c) = a ⊓ (c ⊔ a ⊓ b)
  rw [h, ← inf_assoc]
  show a ⊓ (b ⊔ c) = a ⊓ (c ⊔ a) ⊓ (c ⊔ b)
  rw [sup_comm c a]
  show a ⊓ (b ⊔ c) = a ⊓ (a ⊔ c) ⊓ (c ⊔ b)
  rw [absorb1]
  show a ⊓ (b ⊔ c) = a ⊓ (c ⊔ b)
  rw [sup_comm c b]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have : a - a ≤ b - a := by apply sub_le_sub_right h
  rw [sub_self] at this
  apply this

example (h: 0 ≤ b - a) : a ≤ b := by
  have : a - a ≤ b - a := by rw [← sub_self] at h; exact h
  exact (sub_le_sub_iff_right a).mp this

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have : 0 ≤ b - a := by exact sub_nonneg_of_le h
  have : 0 ≤ (b - a) * c := by apply mul_nonneg this h'
  have : 0 ≤ b * c - a * c := by rw [sub_mul] at this; exact this
  exact sub_nonneg.mp this

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have : dist x x ≤ dist x y + dist y x := by apply dist_triangle x y x
  rw [dist_self x, dist_comm y x] at this
  linarith [this]

end
