import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct

namespace GlobalTheory.CentTorus

def simR (R : Type) [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A) : Subgroup Aˣ where
  carrier := {x | ∃ t : Rˣ, (x : A) * c x = algebraMap R A t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    simp only [Units.val_mul, map_mul]
    rw [show (x : A) * y * (c x * c y) = (x * c x) * (y * c y) by ring, hs, ht]
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have h1 : ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * algebraMap R A s = 1 := by
      rw [← hs, show ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * ((x : A) * c x)
          = (((x⁻¹ : Aˣ) : A) * x) * c (((x⁻¹ : Aˣ) : A) * x) by rw [map_mul]; ring]
      simp
    calc ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)
        = ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * (algebraMap R A s * algebraMap R A ((s⁻¹ : Rˣ) : R)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = algebraMap R A ((s⁻¹ : Rˣ) : R) := by rw [← mul_assoc, h1, one_mul]

theorem mem_simR {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {c : A →ₐ[R] A} {x : Aˣ} :
    x ∈ simR R c ↔ ∃ t : Rˣ, (x : A) * c x = algebraMap R A t := Iff.rfl

abbrev extC (R : Type) [CommRing R] [Algebra ℚ R] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    R ⊗[ℚ] L →ₐ[R] R ⊗[ℚ] L :=
  Algebra.TensorProduct.map (AlgHom.id R R) c

def diagRat (p : ℕ) [Fact p.Prime] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    Subgroup (simR (AfP p) (extC (AfP p) c) × GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)) :=
  ((GlobalTheory.LKTorus.simT ℚ c).map
    ((Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] AfP p ⊗[ℚ] L) : L →* AfP p ⊗[ℚ] L)).prod
      (Units.map ((Algebra.TensorProduct.includeRight : L →ₐ[ℚ] ℚ_[p] ⊗[ℚ] L) : L →* ℚ_[p] ⊗[ℚ] L)))).comap
    ((simR (AfP p) (extC (AfP p) c)).subtype.prodMap (GlobalTheory.LKTorus.simT ℚ_[p] (extC ℚ_[p] c)).subtype)

variable {p : ℕ} [Fact p.Prime]

abbrev algF {G : HTGroup p} (P : Pair G) : Subalgebra G.F G.C := Algebra.adjoin G.F {(P.γ : G.C)}

end GlobalTheory.CentTorus
