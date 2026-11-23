import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GoodRDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem memO_iff {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff, Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K), map_one]

theorem iotaF_mem_cof (D : Formalism.BasicNotions.D7) (x : D.host.F) :
    ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιF x ∈ 𝒪[(D.s.atP p).Fp] := by
  have hfin := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 D.host.F) x
  refine hfin.eventually_cofinite_notMem.mono fun p hp => ?_
  rw [memO_iff, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one]
  exact not_lt.mp hp

theorem vec_mem_of {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : ∀ i j, M i j ∈ R) (hd : M.det ≠ 0) (hdi : (M.det)⁻¹ ∈ R) (c : ι → K)
    (hc : ∀ j, Matrix.vecMul c M j ∈ R) : ∀ i, c i ∈ R := by
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)
  have hc' : c = Matrix.vecMul (Matrix.vecMul c M) M⁻¹ := by
    rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hMinv : ∀ i j, M⁻¹ i j ∈ R := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    refine R.mul_mem ?_ ?_
    · simpa [Ring.inverse_eq_inv'] using hdi
    · rw [Matrix.adjugate_apply, Matrix.det_apply]
      refine R.sum_mem fun σ _ => ?_
      refine R.zsmul_mem (R.prod_mem fun k _ => ?_) _
      rw [Matrix.updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      · exact hM _ _
  intro i
  rw [hc', Matrix.vecMul, dotProduct]
  exact R.sum_mem fun j _ => R.mul_mem (hc j) (hMinv j i)

theorem iotaE_mem_of_int (D : Formalism.BasicNotions.D7) (p : PlF D) {w : D.host.E} (hw : IsIntegral ℤ w) :
    (D.s.atP p).ιE w ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  exact (hw.map (D.s.atP p).ιE.toIntAlgHom).tower_top

theorem alg_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) {c : (D.s.atP p).Fp} (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  exact isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (x := ⟨c, hc⟩)

theorem exists_theta (D : Formalism.BasicNotions.D7) :
    ∃ θ : D.host.E, IsIntegral ℤ θ ∧ θ ∉ (algebraMap D.host.F D.host.E).range := by
  haveI := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hc : (NumberField.InfinitePlace.mk φ).IsComplex := NumberField.IsTotallyComplex.isComplex _
  have hnr : ¬ NumberField.ComplexEmbedding.IsReal φ := by
    rwa [← NumberField.InfinitePlace.isReal_mk_iff, NumberField.InfinitePlace.not_isReal_iff_isComplex]
  obtain ⟨x, hx⟩ : ∃ x, star (φ x) ≠ φ x := by
    by_contra h
    push_neg at h
    exact hnr (RingHom.ext h)
  have hxF : x ∉ (algebraMap D.host.F D.host.E).range := by
    rintro ⟨f, rfl⟩
    exact hx ((NumberField.mem_maximalRealSubfield_iff _).1 f.2 φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  by_cases ha : algebraMap (𝓞 D.host.E) D.host.E a ∈ (algebraMap D.host.F D.host.E).range
  · refine ⟨algebraMap (𝓞 D.host.E) D.host.E b, NumberField.RingOfIntegers.isIntegral_coe b, fun hbF => hxF ?_⟩
    obtain ⟨f1, hf1⟩ := ha
    obtain ⟨f2, hf2⟩ := hbF
    exact ⟨f1 / f2, by rw [map_div₀, hf1, hf2]⟩
  · exact ⟨algebraMap (𝓞 D.host.E) D.host.E a, NumberField.RingOfIntegers.isIntegral_coe a, ha⟩

theorem epsilonDual_almost_all : EpDualCof := by
  intro D
  haveI := D.host.isCMField_hostE
  have h2 : Module.finrank D.host.F D.host.E = 2 :=
    (NumberField.IsCMField.isQuadraticExtension D.host.E).finrank_eq_two
  haveI : FiniteDimensional D.host.F D.host.E := Module.finite_of_finrank_eq_succ h2
  obtain ⟨θ, hθ, hθF⟩ := exists_theta D
  have hli : LinearIndependent D.host.F ![(1 : D.host.E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hθF
      refine ⟨-s / t, ?_⟩
      have hta : algebraMap D.host.F D.host.E t ≠ 0 := (map_ne_zero _).mpr ht
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      rw [map_div₀, map_neg, div_eq_iff hta]
      linear_combination -hst
    subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
    exact ⟨hst, rfl⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h2])
  have hb : ∀ i, b i = ![(1 : D.host.E), θ] i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hbint : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    rw [hb]
    fin_cases i
    · exact isIntegral_one
    · exact hθ
  have hdisc : (Algebra.traceMatrix D.host.F b).det ≠ 0 := Algebra.discr_not_zero_of_basis D.host.F b
  have hev : ∀ᶠ p in Filter.cofinite,
      (∀ i j, (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b i j) ∈ 𝒪[(D.s.atP p).Fp]) ∧
        (D.s.atP p).ιF ((Algebra.traceMatrix D.host.F b).det)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
    have h1 : ∀ᶠ p in Filter.cofinite,
        ∀ i j, (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b i j) ∈ 𝒪[(D.s.atP p).Fp] := by
      simp only [Filter.eventually_all]
      exact fun i j => iotaF_mem_cof D _
    exact h1.and (iotaF_mem_cof D _)
  refine hev.mono fun p hp z hz => ?_
  obtain ⟨hT, hTd⟩ := hp
  have hbL : ∀ i, PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 i = (D.s.atP p).ιE (b i) := fun i =>
    PI.ProdFormulaE.Base.basisE_apply (D.s.atP p) b h2 i
  have hM : ∀ i j, Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
      (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 i * PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j) =
      (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b i j) := by
    intro i j
    rw [hbL, hbL, ← map_mul, PI.ProdFormulaE.Base.trace_ιE (D.s.atP p) h2, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply]
  have hdet : ((Algebra.traceMatrix D.host.F b).map (D.s.atP p).ιF).det =
      (D.s.atP p).ιF (Algebra.traceMatrix D.host.F b).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hc := vec_mem_of 𝒪[(D.s.atP p).Fp] ((Algebra.traceMatrix D.host.F b).map (D.s.atP p).ιF)
    (fun i j => hT i j) (by rw [hdet]; exact (map_ne_zero _).mpr hdisc)
    (by rw [hdet, ← map_inv₀]; exact hTd)
    (fun i => (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).repr z i) (fun j => by
      have hsum : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
          (z * PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j) =
          ∑ i, (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).repr z i *
            Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep
              (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 i * PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j) := by
        conv_lhs => rw [← (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).sum_repr z]
        rw [Finset.sum_mul, map_sum]
        simp only [smul_mul_assoc, map_smul, smul_eq_mul]
      have hmem := hz (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2 j)
        (by rw [hbL]; exact iotaE_mem_of_int D p (hbint j))
      rw [hsum] at hmem
      simp only [hM] at hmem
      simpa [Matrix.vecMul, dotProduct, Matrix.map_apply] using hmem)
  rw [← (PI.ProdFormulaE.Base.basisE (D.s.atP p) b h2).sum_repr z]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (alg_mem_O D p (hc i)) (by rw [hbL]; exact iotaE_mem_of_int D p (hbint i))

end PI.UnitaryGroupMassFormula.CntFormula
