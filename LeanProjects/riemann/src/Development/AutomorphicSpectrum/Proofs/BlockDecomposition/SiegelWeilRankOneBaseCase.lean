import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZeroStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix
open PositivityTheory.SiegelWeilFormula.Densx PositivityTheory.Rg.Base1

namespace GlobalTheory.CompanionTheory.Base1

private theorem isClosed_nonnegReal : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

private theorem mul_mem_nonnegReal {z w : ℂ} (hz : z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re})
    (hw : w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) : z * w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  obtain ⟨hz0, hz1⟩ := hz
  obtain ⟨hw0, hw1⟩ := hw
  refine ⟨by simp [Complex.mul_im, hz0, hw0], ?_⟩
  simp only [Complex.mul_re, hz0, hw0, mul_zero, sub_zero]
  exact mul_nonneg hz1 hw1

private theorem tprod_mem_nonnegReal {ι : Type*} (f : ι → ℂ)
    (hf : ∀ i, f i ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}) :
    ∏' i, f i ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  by_cases hm : Multipliable f
  · refine isClosed_nonnegReal.mem_of_tendsto hm.hasProd (Eventually.of_forall fun s => ?_)
    exact Finset.prod_induction f (fun z => z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re})
      (fun _ _ => mul_mem_nonnegReal) (by simp) (fun i _ => hf i)
  · rw [tprod_eq_one_of_not_multipliable hm]
    simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem factor_mem (v : HeightOneSpectrum (𝓞 F)) {s : ℝ} (hs : 1 < s) :
    (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∈
      {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} := by
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  have hc : (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ)) = ((q ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq0]
    simp [hq]
  have hle : q ^ (-s) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm v.asIdeal) with h | h
    · have : q = 0 := by simp [hq, h]
      rw [this, Real.zero_rpow (by linarith)]
      exact zero_le_one
    · exact Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 h) (by linarith)
  have hnn : 0 ≤ q ^ (-s) := Real.rpow_nonneg hq0 _
  rw [hc]
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs
  · refine ⟨by simp, ?_⟩
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.one_im, Complex.ofReal_im]
    linarith
  · refine ⟨by simp, ?_⟩
    simp only [one_mul, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith

theorem lamLim_nonneg {Λ : ℂ} (h : IsLamLim F E Λ) : Λ.im = 0 ∧ 0 ≤ Λ.re := by
  refine isClosed_nonnegReal.mem_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact tprod_mem_nonnegReal _ fun v => factor_mem v hs

theorem lamLim_unique {Λ Λ' : ℂ} (h : IsLamLim F E Λ) (h' : IsLamLim F E Λ') : Λ = Λ' :=
  tendsto_nhds_unique h h'

variable (F E) in

theorem exists_half_lamLim : ∃ c : ℝ≥0, ∀ Λ : ℂ, IsLamLim F E Λ → ((c : ℝ) : ℂ) = Λ / 2 := by
  by_cases h : ∃ Λ, IsLamLim F E Λ
  · obtain ⟨Λ₀, h₀⟩ := h
    obtain ⟨him, hre⟩ := lamLim_nonneg h₀
    refine ⟨Real.toNNReal (Λ₀.re / 2), fun Λ hΛ => ?_⟩
    rw [lamLim_unique hΛ h₀, Real.coe_toNNReal _ (by linarith)]
    apply Complex.ext <;> simp [him]
  · exact ⟨0, fun Λ hΛ => absurd ⟨Λ, hΛ⟩ h⟩

theorem baseOne_of_parts : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  intro hP hS hH hC F E _ _ _ _ _ σ hcm J hJ T hT hd d b li lam hli hlam μ 𝓕 hμ h𝓕 mi m hmi hm
  obtain ⟨β, rfl, hβ, he⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hβ0 : β ≠ 0 := hβ hd
  simp only [he]
  have hsph : {X : Fin 1 → Fin 1 → E | gramE σ J X = fun _ _ => algebraMap F E β} = sph σ J β := rfl
  rw [hsph]
  obtain ⟨c, hc⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ0
  by_cases h0 : mi (hermScal (Ainf F) σ (algebraMap F _ β)) = 0 ∨
      ∃ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β))) = 0
  · obtain ⟨c', hc'⟩ := exists_half_lamLim F E
    refine ⟨c', ?_, hc'⟩
    rw [(GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 1 _ c _ _).2.1 hc h0]
    exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 1 0 c' _ _).2.2 hc.1 hc.2.1 h0
  push Not at h0
  have hmne : ∀ v, m v (hermScal (Fv F v) σ (algebraMap F _ β)) ≠ 0 := fun v hz =>
    h0.2 v (by rw [hz, smul_zero])
  have hne : (sph σ J β).Nonempty :=
    hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β hβ0 h0.1 hmne
  have hall : ∀ β' : F, β' ≠ 0 → EP b μ 𝓕 mi m β' c := by
    intro β' hβ'
    by_cases hn : (sph σ J β').Nonempty
    · exact hS F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β β' hβ0 hβ' hne hn c hc
    · obtain ⟨c', hc'⟩ := hP F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β' hβ'
      have hz : mi (hermScal (Ainf F) σ (algebraMap F _ β')) = 0 ∨
          ∃ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β'))) = 0 := by
        by_contra hz
        push Not at hz
        exact hn (hH F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β' hβ' hz.1
          fun v hv => hz.2 v (by rw [hv, smul_zero]))
      have ht : thetaMeas σ J μ 𝓕 (sph σ J β') = 0 := by
        have he' : IsEmpty (sph σ J β') := Set.not_nonempty_iff_eq_empty.1 hn ▸ inferInstance
        simp [thetaMeas]
      unfold EP
      rw [ht]
      exact (GlobalTheory.T.euler_product_measure_zero F E σ hcm d b 1 1 0 c _ _).2.2 hc'.1 hc'.2.1 hz
  exact ⟨c, hc, hC F E σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm c hall⟩

end GlobalTheory.CompanionTheory.Base1
