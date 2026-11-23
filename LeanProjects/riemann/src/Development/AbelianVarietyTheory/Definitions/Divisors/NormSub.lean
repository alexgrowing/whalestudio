import Mathlib

noncomputable section

namespace GlobalTheory.LKTorus

variable (k : Type) [Field k] {A : Type} [CommRing A] [Algebra k A]

def simT (c : A →ₐ[k] A) : Subgroup Aˣ where
  carrier := {x | ∃ t : kˣ, (x : A) * c x = algebraMap k A t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    simp only [Units.val_mul, map_mul]
    rw [show (x : A) * y * (c x * c y) = (x * c x) * (y * c y) by ring, hs, ht]
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have h1 : ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * algebraMap k A s = 1 := by
      rw [← hs, show ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * ((x : A) * c x)
          = (((x⁻¹ : Aˣ) : A) * x) * c (((x⁻¹ : Aˣ) : A) * x) by rw [map_mul]; ring]
      simp
    calc ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)
        = ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * (algebraMap k A s * algebraMap k A ((s⁻¹ : kˣ) : k)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = algebraMap k A ((s⁻¹ : kˣ) : k) := by rw [← mul_assoc, h1, one_mul]

def fixU (c : A →ₐ[k] A) : Subgroup Aˣ where
  carrier := {a | c a = a}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h : c ((a⁻¹ : Aˣ) : A) * a = 1 := by
      conv_lhs => rw [← ha]
      rw [← map_mul]
      simp
    calc c ((a⁻¹ : Aˣ) : A) = c ((a⁻¹ : Aˣ) : A) * a * ((a⁻¹ : Aˣ) : A) := by simp
      _ = ((a⁻¹ : Aˣ) : A) := by rw [h, one_mul]

def normSub (c : A →ₐ[k] A) : Subgroup (fixU k c) :=
  Subgroup.closure {a : fixU k c | ∃ (t : kˣ) (x : Aˣ), ((a : Aˣ) : A) = algebraMap k A t * (x * c x)}

def H1 (c : A →ₐ[k] A) : Type := fixU k c ⧸ normSub k c

instance (c : A →ₐ[k] A) : CommGroup (H1 k c) := by
  unfold H1
  infer_instance

end GlobalTheory.LKTorus
