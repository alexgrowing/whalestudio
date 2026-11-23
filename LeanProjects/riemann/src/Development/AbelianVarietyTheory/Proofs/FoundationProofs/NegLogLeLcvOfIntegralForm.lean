import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.LocBasis
import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem vw_gramR_locBasis_ge {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
    (Γ : Matrix (Fin d) (Fin d) K) (s : ℕ) (hs : 0 < s) (L : Submodule (𝓞 K) (Fin d → K))
    (hint : ∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ Γ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range)
    (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K) (hf : IsLocBasis L w f)
    (hG : gramR Γ f ≠ 0) : 0 ≤ (d : ℤ) * vw w (s : K) + vw w (gramR Γ f) := by
  classical
  have hmem : ∀ a, ∃ t ∈ ReductionFirst.Tw w, t • f a ∈ L := by
    intro a
    have h1 : f a ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range f)) :=
      ⟨1, (Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal).one_mem, by
        rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
    rw [hf.2] at h1
    obtain ⟨t, ht, h⟩ := h1
    exact ⟨t, ReductionFirst.hcompl_le_Tw w ht, h⟩
  choose t ht htL using hmem
  have hT : (∏ a, t a) ∈ ReductionFirst.Tw w := Submonoid.prod_mem _ fun a _ => ht a
  have hTL : ∀ a, (∏ b, t b) • f a ∈ L := by
    intro a
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a), mul_smul]
    exact L.smul_mem _ (htL a)
  obtain ⟨T, hTdef⟩ : ∃ T, T = ∏ a, t a := ⟨_, rfl⟩
  rw [← hTdef] at hT
  simp only [← hTdef] at hTL
  choose Q hQ using fun a b => hint _ (hTL a) _ (hTL b)
  have hmap : (Matrix.of Q).map (algebraMap (𝓞 K) K) =
      ((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) •
        (Matrix.of fun a b => star (f a) ⬝ᵥ Γ.mulVec (f b)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hQ a b, ReductionFirst.smul_coe, ReductionFirst.smul_coe, star_smul, Matrix.mulVec_smul, smul_dotProduct,
      dotProduct_smul, ReductionFirst.cO_coe, smul_eq_mul, smul_eq_mul]
    ring
  have hdet : algebraMap (𝓞 K) K (Matrix.of Q).det =
      ((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) ^ d * gramR Γ f := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_smul, Fintype.card_fin]
    rfl
  have hnn : 0 ≤ vw w (((s : K) * (((cO K T : 𝓞 K) : K) * (T : K))) ^ d * gramR Γ f) := by
    rw [← hdet]; exact ReductionFirst.vw_int_nonneg w _
  have hT0 := ReductionFirst.Tw_ne_zero hT
  have hT0' := ReductionFirst.Tw_ne_zero (ReductionFirst.cO_mem_Tw hT)
  have hs0 : (s : K) ≠ 0 := by exact_mod_cast hs.ne'
  rw [ReductionFirst.vw_mul w (pow_ne_zero _ (mul_ne_zero hs0 (mul_ne_zero hT0' hT0))) hG, ReductionFirst.vw_pow,
    ReductionFirst.vw_mul w hs0 (mul_ne_zero hT0' hT0), ReductionFirst.vw_mul w hT0' hT0, ReductionFirst.vw_unit w T hT.1,
    ReductionFirst.vw_unit w _ hT.2] at hnn
  simpa using hnn

theorem neg_log_le_lcv_of_integral_form :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) → ∀ (Γ : Matrix (Fin d) (Fin d) K) (s : ℕ), 0 < s → Γ.det ≠ 0 → (∏ v : InfinitePlace K, ‖v.embedding Γ.det‖ ≤ ∏ v : InfinitePlace K, (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re) → ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K L → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ Γ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((d : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ d X hX Γ s hs hΓ hle L hL hint
  classical
  have hli : LinearIndependent K (fun i => (Pi.single i 1 : Fin d → K)) := by
    have : (fun i => (Pi.single i 1 : Fin d → K)) = ⇑(Pi.basisFun K (Fin d)) := by
      funext i; simp [Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun K (Fin d)).linearIndependent
  obtain ⟨hfin, hlcv⟩ := covolume_via_basis K d X hX L hL _ hli
  obtain ⟨hGfin, hGpf⟩ := prod_formula' K _ hΓ
  obtain ⟨hsfin, hspf⟩ := Formalism.PairingDivisionLocalBalance.sum_valuation_nat K s
  obtain ⟨I, hI⟩ : ∃ I : HeightOneSpectrum (𝓞 K) → ℝ, I = fun w => lw w *
      (idx w (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) L : ℝ) :=
    ⟨_, rfl⟩
  rw [← hI] at hfin hlcv

  have hpos : ∀ v : InfinitePlace K,
      0 < (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    intro v
    rw [Rb.gramStd]
    exact (Rb.pos_real (Rb.metMat_posDef X v (hX v)).det_pos).2
  have hpos' : ∀ v : InfinitePlace K, 0 < ‖v.embedding Γ.det‖ := fun v =>
    norm_pos_iff.mpr ((map_ne_zero _).mpr hΓ)
  have hmean : ∑ v : InfinitePlace K, Real.log ‖v.embedding Γ.det‖ ≤
      ∑ v, Real.log (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    rw [← Real.log_prod (fun v _ => (hpos' v).ne'), ← Real.log_prod (fun v _ => (hpos v).ne')]
    exact Real.log_le_log (Finset.prod_pos fun v _ => hpos' v) hle
  have hinf : ∑ᶠ w, lw w * (vw w Γ.det : ℝ) ≤ (2 / (Module.finrank ℚ K : ℝ)) *
      ∑ v, Real.log (gram X v (fun i => (Pi.single i 1 : Fin d → K))).det.re := by
    rw [← hGpf]
    exact mul_le_mul_of_nonneg_left hmean (by positivity)

  have hloc : ∀ w : HeightOneSpectrum (𝓞 K),
      0 ≤ (d : ℝ) * (lw w * (vw w (s : K) : ℝ)) + lw w * (vw w Γ.det : ℝ) + I w + I (conjPl w) := by
    intro w
    obtain ⟨hmul, hstar, hlw, -, -, -, -⟩ := valuation_basic_properties K w
    obtain ⟨f, hf⟩ := semilocal_basis_exists K d L hL w
    let γ : Matrix (Fin d) (Fin d) K := Matrix.of fun k i => f i k
    have hew : (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin d → K)) = f := by
      funext i j
      simp [γ, Finset.sum_apply, Pi.single_apply]
    have hdet : γ.det ≠ 0 := by
      have hu : IsUnit (Matrix.of f) := Matrix.linearIndependent_rows_iff_isUnit.mp hf.1
      have : γ = (Matrix.of f)ᵀ := by ext k i; rfl
      rw [this, Matrix.det_transpose]
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    have hlb : IsLocBasis L w (fun i => ∑ k, γ k i • (Pi.single k (1 : K) : Fin d → K)) := by
      rw [hew]; exact hf
    obtain ⟨hi1, hi2⟩ := index_change_formula K d L hL _ hli w γ hlb
    have hgc : gramR Γ f = star γ.det * γ.det * Γ.det := by
      rw [← hew, ← Rb.gramR_std Γ]
      exact gram_matrix_change K d d _ _ γ
    have hG : gramR Γ f ≠ 0 := by
      rw [hgc]; exact mul_ne_zero (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hΓ
    have h := vw_gramR_locBasis_ge Γ s hs L hint w f hf hG
    rw [hgc, hmul _ _ (mul_ne_zero (star_ne_zero.mpr hdet) hdet) hΓ,
      hmul _ _ (star_ne_zero.mpr hdet) hdet, hstar] at h
    have h' : (0 : ℝ) ≤ (d : ℝ) * (vw w (s : K) : ℝ) +
        ((vw (conjPl w) γ.det : ℝ) + (vw w γ.det : ℝ) + (vw w Γ.det : ℝ)) := by exact_mod_cast h
    have hl0 : 0 ≤ lw w := div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have := mul_nonneg hl0 h'
    rw [hI]
    simp only
    rw [hi1, hi2, hlw]
    linarith
  have hinj : Function.Injective (conjPl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K)) :=
    fun a b h => by rw [← ValuationRepresentative.conjPl_conjPl a, h, ValuationRepresentative.conjPl_conjPl b]
  have hfc : (Function.support fun w => I (conjPl w)).Finite := hfin.preimage hinj.injOn
  have hsfin' : (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
      (d : ℝ) * (lw w * (vw w (s : K) : ℝ))).Finite :=
    hsfin.subset (Function.support_mul_subset_right _ _)
  have h12 := (hsfin'.union hGfin).subset (Function.support_add _ _)
  have h123 := (h12.union hfin).subset (Function.support_add _ _)
  have htot := finsum_nonneg hloc
  rw [finsum_add_distrib h123 hfc, finsum_add_distrib h12 hfin, finsum_add_distrib hsfin' hGfin,
    finite_sum_conjugation K I, ← mul_finsum' _ _ hsfin, hspf] at htot
  rw [hlcv]
  linarith

end GlobalTheory.TestLat
