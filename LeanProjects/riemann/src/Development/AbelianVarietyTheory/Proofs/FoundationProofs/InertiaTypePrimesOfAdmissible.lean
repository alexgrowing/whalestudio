import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
open Formalism.MainNotions.N
open scoped Matrix Pointwise

namespace GlobalTheory.InertiaTypePrimes

section General

variable {Γ R : Type} [Group Γ] [CommRing R] {r : ℕ}

theorem mem_ker_mapRep_iff (J : Ideal R) (ρ : Γ →* GL (Fin r) R) (g : Γ) :
    g ∈ (mapRep (Ideal.Quotient.mk J) ρ).ker ↔
      ∀ a b, (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (Ideal.Quotient.mk J).mapMatrix ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem isOpen_ker_mapRep [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (ρ : Γ →* GL (Fin r) R)
    (hρ : Continuous fun g => ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)) :
    IsOpen ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) := by
  have : ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) = ⋂ a, ⋂ b,
      (fun g => (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_mapRep_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hJ.preimage ?_
  exact (hρ.sub continuous_const).matrix_elem a b

theorem pow_sub_one_mem (I : Ideal R) (l m : ℕ) (hl : (l : R) ∈ I) (Y : Matrix (Fin r) (Fin r) R)
    (hY : ∀ a b, (Y - 1) a b ∈ I ^ (m + 1)) (a b : Fin r) : (Y ^ l - 1) a b ∈ I ^ (m + 2) := by
  have h1 : (Ideal.Quotient.mk I).mapMatrix Y = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk I).mapMatrix, ← map_sub]
    ext a b
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using Ideal.pow_le_self (Nat.succ_ne_zero m) (hY a b)
  have h2 : (Ideal.Quotient.mk I).mapMatrix (∑ i ∈ Finset.range l, Y ^ i) = 0 := by
    have h0 : ((l : ℕ) : R ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hl
    simp only [map_sum, map_pow, h1, one_pow, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (R ⧸ I), h0, zero_smul]
  have h3 : ∀ a b, (∑ i ∈ Finset.range l, Y ^ i) a b ∈ I := fun a b => by
    have := congrFun (congrFun h2 a) b
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
      Ideal.Quotient.eq_zero_iff_mem] using this
  rw [← mul_geom_sum, Matrix.mul_apply, pow_succ I (m + 1)]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (hY a c) (h3 c b)

def eigenStab (ρ : Γ →* GL (Fin r) R) (χ : Γ →* Rˣ) (x : Fin r → R) : Subgroup Γ where
  carrier := {g | ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) *ᵥ x = ((χ g : Rˣ) : R) • x}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hh,
      Matrix.mulVec_smul, hg, smul_smul, mul_comm]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h := congrArg (fun y => ((χ g⁻¹ : Rˣ) : R) •
      (((ρ g⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) *ᵥ y)) hg
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul, smul_smul, ← Units.val_mul, ← map_mul,
      inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec, one_smul] at h
    exact h.symm

end General

theorem isWild_of_isWildAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω) (h : IsWildAt A σ) : IsWild A σ := by
  have h1 : ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x := fun x hx => by
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
    rw [e, map_mul]
    exact mul_lt_of_lt_one_left h0 (h x hx)
  have h2 : ∀ x : Ω, A.valuation (σ x) = A.valuation x := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact Valuation.map_eq_of_sub_lt _ (h1 x hx)
  refine ⟨⟨?_, fun x hx => ?_⟩, h1⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← h2, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (h1 x hx0).trans_le hx

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {r : ℕ} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

end Wild

end GlobalTheory.InertiaTypePrimes
