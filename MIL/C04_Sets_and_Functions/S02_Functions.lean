import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  simp

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, yeq⟩
  rw [← h yeq]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  simp
  intro
  simp

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yu
  simp
  rcases h y with ⟨x, rfl⟩
  use x

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yfs
  rcases yfs with ⟨x, xs, rfl⟩
  have : x ∈ t := h xs
  use x

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro
  apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  simp

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor <;> use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, ⟨x₁s, fxeq⟩⟩, ⟨x₂, ⟨x₂t, rfl⟩⟩⟩
  have xeq : x₁ = x₂ := h fxeq
  rw [← xeq] at x₂t
  use x₁
  exact ⟨⟨x₁s, x₂t⟩, fxeq⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  rintro y ⟨⟨x, ⟨xs, rfl⟩⟩, h⟩
  use x
  constructor
  · constructor
    · exact xs
    · by_contra! xt
      simp at h
      let hx := h x xt
      contradiction
  · simp

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  simp; rfl

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  apply Subset.antisymm
  · rintro y ⟨⟨x, xs, rfl⟩, yv⟩
    use x
    exact ⟨⟨xs, yv⟩, rfl⟩
  · rintro y ⟨x, ⟨xs, yv⟩, rfl⟩
    exact ⟨⟨x, xs, rfl⟩, yv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, yu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, yu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, yu⟩
  exact ⟨⟨x, xs, rfl⟩, yu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | yu)
  · left
    use x
  · right
    exact yu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp; constructor
  · rintro ⟨x, ⟨i, xAi⟩, rfl⟩
    use i, x
  · rintro ⟨i, ⟨x, xAi, rfl⟩⟩
    exact ⟨x, ⟨⟨i, xAi⟩, rfl⟩⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, xAi, rfl⟩
  simp
  intro i
  simp at xAi
  exact ⟨x, xAi i, rfl⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, xAi, rfl⟩
  use x
  constructor
  · intro i2
    rcases h i2 with ⟨x2, xAi2, fxeq⟩
    have : x2 = x := injf fxeq
    rw [this] at xAi2
    exact xAi2
  · rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x; simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x; simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnonneg y ynonneg h
  calc
    x = (√x) ^ 2 := Eq.symm (sq_sqrt xnonneg)
    _ = (√y) ^ 2 := by rw [h]
    _ = y := sq_sqrt ynonneg

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg e
  simp at e
  calc
    x = sqrt (x ^ 2) := Eq.symm (sqrt_sq xnonneg)
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := sqrt_sq ynonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; simp; constructor
  · rintro ⟨x, _, rfl⟩
    exact sqrt_nonneg x
  · intro ynonneg
    use (y ^ 2)
    exact ⟨sq_nonneg y, sqrt_sq ynonneg⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; simp; constructor
  · rintro ⟨x, rfl⟩
    exact sq_nonneg x
  · intro ynonneg
    use sqrt y
    exact sq_sqrt ynonneg

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h x
    apply h
    apply inverse_spec
    use x
  · intro h x₁ x₂ eq
    rw [← h x₁, ← h x₂, eq]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    apply inverse_spec
    apply h
  · intro h y
    use inverse f y
    apply h

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

end
