import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfNorm

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev OR : Subring (Fv F v ⊗[F] E) := Orb.oRing (E := E) v (Orb.oSub (E := E) v)

def IsRes (ϖ : Fv F v) {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) : Prop :=
  Function.Surjective π ∧ (∀ x : OR (E := E) v, π x = 0 ↔ (x : Fv F v ⊗[F] E) ∈ PO (E := E) v ϖ) ∧
    ∀ x y : OR (E := E) v, (y : Fv F v ⊗[F] E) = sigR (Fv F v) σ x → π y = τ (π x)

theorem hR_add_right (x y z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + z) = hR (Fv F v) σ J x y + hR (Fv F v) σ J x z := by
  simp only [hR, hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem coord_eq (e : Fin n → Fin n → Fv F v ⊗[F] E) (he1 : gramR (Fv F v) σ J e = 1)
    (c : Fin n → Fv F v ⊗[F] E) (j : Fin n) : hR (Fv F v) σ J (e j) (∑ i, c i • e i) = c j := by
  rw [Orb.hR_sum_right σ J v]
  have h : ∀ i, hR (Fv F v) σ J (e j) (e i) = (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) j i := by
    intro i; rw [← he1]; rfl
  simp only [h, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem bas_mem {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (j : Fin n) :
    e j ∈ latLoc (E := E) v Λ := by
  refine (he _).2 ⟨Pi.single j 1, fun i => ?_, ?_⟩
  · by_cases h : i = j
    · subst h; simpa using (Orb.oSub (E := E) v).1
    · simpa [Pi.single_apply, h] using Orb.oev_zero (E := E) v
  · simp [Pi.single_apply, ite_smul]

theorem expand {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {x : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) :
    x = ∑ j, hR (Fv F v) σ J (e j) x • e j := by
  obtain ⟨c, -, rfl⟩ := (he x).1 hx
  simp only [coord_eq σ J v e he1]

theorem ffGram_one {K : Type} [CommRing K] (τ : K →+* K) {a : ℕ} (X : Fin a → Fin n → K) (i j : Fin a) :
    ffGram τ (1 : Matrix (Fin n) (Fin n) K) X i j = ∑ p, τ (X i p) * X j p := by
  simp only [ffGram, ffH, Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem gY_mem {a : ℕ} {Y : TupV (E := E) v n a} (hG : GoodY σ J ψ v Λ a Y) (i j : Fin a) :
    gramR (Fv F v) σ J Y i j ∈ OR (E := E) v :=
  (hG.2.2.1 (Y j)).1 (hG.2.2.2.2.2.1.1 j) (Y i) (hG.2.2.2.2.2.1.1 i)

end PI.OmLocU.Red
