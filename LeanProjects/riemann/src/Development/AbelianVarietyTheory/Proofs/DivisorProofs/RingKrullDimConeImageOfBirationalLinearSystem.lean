import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.ConeDim

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {N : ℕ}

theorem isAlgebraic_of_closure_eq_top (y : Fin N → Ω) (hy : y ≠ 0)
    (hgen : Subfield.closure (Set.range (algebraMap k Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤)
    (A : Subalgebra k (Polynomial Ω)) (hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A) :
    Algebra.IsAlgebraic A (Polynomial Ω) := by
  classical
  let ι : Polynomial Ω →+* FractionRing (Polynomial Ω) := algebraMap _ _
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let L : Subfield (FractionRing (Polynomial Ω)) := Subfield.closure (ι '' (A : Set (Polynomial Ω)))
  have hA : ∀ a ∈ A, ι a ∈ L := fun a ha => Subfield.subset_closure ⟨a, ha, rfl⟩
  have hne : ∀ j, y j ≠ 0 → ι (Polynomial.X * Polynomial.C (y j)) ≠ 0 := fun j hj =>
    (map_ne_zero_iff ι hι).2 (mul_ne_zero Polynomial.X_ne_zero (Polynomial.C_ne_zero.2 hj))
  let M : Subfield Ω := L.comap (ι.comp Polynomial.C)
  have hM : M = ⊤ := by
    refine top_unique (hgen ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨i, j, rfl⟩)
    · show ι (Polynomial.C (algebraMap k Ω c)) ∈ L
      rw [← Polynomial.algebraMap_apply]
      exact hA _ (A.algebraMap_mem c)
    · show ι (Polynomial.C (y i / y j)) ∈ L
      by_cases hj : y j = 0
      · rw [hj, div_zero, Polynomial.C_0, map_zero]
        exact zero_mem L
      · have e : ι (Polynomial.C (y i / y j)) =
            ι (Polynomial.X * Polynomial.C (y i)) / ι (Polynomial.X * Polynomial.C (y j)) := by
          rw [eq_div_iff (hne j hj), ← map_mul]
          congr 1
          rw [mul_left_comm, ← Polynomial.C_mul, div_mul_cancel₀ _ hj]
        rw [e]
        exact div_mem (hA _ (hXy i)) (hA _ (hXy j))
  have hC : ∀ c, ι (Polynomial.C c) ∈ L := fun c => by
    have h : c ∈ M := hM ▸ Subfield.mem_top c
    exact h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have hX : ι Polynomial.X ∈ L := by
    have e : ι Polynomial.X = ι (Polynomial.X * Polynomial.C (y j)) * ι (Polynomial.C (y j)⁻¹) := by
      rw [← map_mul, mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hj, Polynomial.C_1, mul_one]
    rw [e]
    exact mul_mem (hA _ (hXy j)) (hC _)
  have hall : ∀ p, ι p ∈ L := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact mul_mem (hC c) (pow_mem hX n)
  have hcl : Subring.closure (ι '' (A : Set (Polynomial Ω))) ≤ (A.toSubring.map ι) :=
    Subring.closure_le.2 (by rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
  refine ⟨fun p => ?_⟩
  obtain ⟨_, ha₀, _, hb₀, hab⟩ := Subfield.mem_closure_iff.1 (hall p)
  obtain ⟨a, ha, rfl⟩ := hcl ha₀
  obtain ⟨b, hb, rfl⟩ := hcl hb₀
  by_cases hb0 : b = 0
  · rw [hb0, map_zero, div_zero, eq_comm, map_eq_zero_iff ι hι] at hab
    rw [hab]
    exact isAlgebraic_zero
  · have e : b * p = a := by
      apply hι
      rw [map_mul, ← hab, mul_div_cancel₀ _ ((map_ne_zero_iff ι hι).2 hb0)]
    refine ⟨Polynomial.C (⟨b, hb⟩ : A) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : A), fun h => hb0 ?_, ?_⟩
    · have := congrArg (fun q => Polynomial.coeff q 1) h
      simp at this
      exact congrArg Subtype.val this
    · simp [e]

theorem ringKrullDim_imageIdeal_of_birational : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety →
    S.BasePointFree → S.Birational →
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = ((S.D + 1 : ℕ) : WithBot ℕ∞) := by
  intro k _ S h hb ⟨η, hη, hr⟩
  have := HeightExists.isIntegral h
  let Ω := S.Y.residueField η
  letI : Algebra k Ω := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt Ω := ⟨resPt η, S.comp_str _⟩
  set y : Fin S.N → Ω := S.coords (resPt η) with hy
  have hI : S.imageIdeal = coneIdeal k y :=
    imageIdeal_eq_coneIdeal_of_generic k Ω S x (by rw [ptOf_resPt]; exact hη) 1 y one_ne_zero
      (one_smul _ _).symm
  have hD : Algebra.trdeg k Ω = S.D :=
    (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth η
      fun z hz => (hz.antisymm (hη.specializes trivial)).eq).2
  rw [hI]
  have := isPrime_coneIdeal (K := k) y
  refine ringKrullDim_eq_of_trdeg_eq k _ ?_
  let f := Ideal.kerLiftAlg (coneMap k y)
  have hf : Function.Injective f := Ideal.kerLiftAlg_injective _
  let A := f.range
  let e := AlgEquiv.ofInjective f hf
  have hQA : Algebra.trdeg k (MvPolynomial (Fin S.N) k ⧸ coneIdeal k y) = Algebra.trdeg k A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self f (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := ConeDim.isAlgebraic_of_closure_eq_top y (hb.coords_ne_zero _) hr A hXy
  have : FaithfulSMul k A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (Polynomial Ω), ← trdeg_add_eq k Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, hD]
  norm_cast

end GlobalTheory.Adelic.ConeDim
