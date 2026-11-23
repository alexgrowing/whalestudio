import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.OneBlockIdealEqComapProjIdeal
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroMore
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsFormOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousAeval
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ chartLat)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionInjectivityEquivalence

theorem val_ne_zero {P : ArithVariety n} {f : MvPolynomial (Coord n) ℤ} (hf : f ∉ P.ideal) :
    val P f ≠ 0 := by
  rw [← funFieldEquiv_mkF, Ne, map_eq_zero_iff _ (funFieldEquiv P).injective]
  exact fun h ↦ hf ((P.mkF_eq_zero_iff f).mp h)

theorem sectionVal_ne_zero {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a)
    (he : e.num ∉ P.ideal) : sectionVal e ≠ 0 :=
  div_ne_zero (val_ne_zero he) (val_ne_zero e.den_not_mem)

theorem toFun_ne_zero {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a)
    (he : e.num ∉ P.ideal) : e.toFun ≠ 0 := by
  rw [toFun_eq_symm_sectionVal, Ne, map_eq_zero_iff _ (funFieldEquiv P).symm.injective]
  exact sectionVal_ne_zero e he

theorem supNormLE_cast {P : ArithVariety n} {A B : HermLine n} (h : A = B) (s : IntegralSection P A.deg)
    {C : ℝ} (hs : s.SupNormLE A C) : (s.cast (congrArg HermLine.deg h)).SupNormLE B C := by
  subst h
  exact hs

theorem mkF_div_chartPow_mem {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    P.mkF f / P.chartPow c (fun k ↦ (δ k : ℤ)) ∈ P.chartRing c := by
  have h := P.chart_homogeneous c hc hf
  have hpow : P.chartPow c (fun k ↦ (δ k : ℤ)) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k := by
    simp only [ArithVariety.chartPow, zpow_natCast]
  have hne : ∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ fun h0 ↦ hc k ((P.mkF_eq_zero_iff _).mp h0)
  rw [hpow, ← h, mul_div_cancel_left₀ _ hne]
  refine MvPolynomial.eval₂_mem (fun i _ ↦ intCast_mem _ _) fun v ↦ ?_
  exact Subring.subset_closure ⟨v, rfl⟩

theorem chartPow_add (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (u v : ι → ℤ) : P.chartPow c (u + v) = P.chartPow c u * P.chartPow c v := by
  simp only [ArithVariety.chartPow, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  exact zpow_add₀ (fun h0 ↦ hc k ((P.mkF_eq_zero_iff _).mp h0)) _ _

theorem sectionVal_mem_chartLat {P : ArithVariety n} {b : ι → ℤ} (σ : IntegralSection P b) (τ : ℕ)
    (a : ι → ℤ) (hb : ∀ k, b k = (τ : ℤ) * a k) : sectionVal σ ∈ chartLat (genPt P) a τ := by
  intro c hc
  have hlive : P.IsLive c := fun k hk ↦ hc k (by
    show val P (X ⟨k, c k⟩) = 0
    rw [← funFieldEquiv_mkF, (P.mkF_eq_zero_iff _).mpr hk, map_zero])
  obtain ⟨d, ε, ⟨δ, hε, hδ⟩, hmem⟩ := σ.regular c hlive
  have hmk := SectionSmall.mkF_eq_of_mem σ hmem
  have hX : P.mkF (chartMonomial c d) = P.chartPow c (fun k ↦ (d k : ℤ)) := by
    simp only [chartMonomial, map_prod, map_pow, ArithVariety.chartPow, zpow_natCast]
  have hXne : P.chartPow c (fun k ↦ (d k : ℤ)) ≠ 0 := by
    unfold ArithVariety.chartPow
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ fun h1 ↦ hlive k ((P.mkF_eq_zero_iff _).mp h1)
  have hδ' : (fun k ↦ (δ k : ℤ)) = b + fun k ↦ (d k : ℤ) := funext fun k ↦ hδ k
  have key : σ.toFun / P.chartPow c b = P.mkF ε / P.chartPow c (fun k ↦ (δ k : ℤ)) := by
    rw [hδ', chartPow_add P hlive, hmk, hX, mul_div_mul_right _ _ hXne]
  have hm := mkF_div_chartPow_mem hlive hε
  rw [← key, ← funFieldEquiv_mem_chartRing_iff, funFieldEquiv_div_chartPow, funFieldEquiv_toFun] at hm
  have hb' : -b = fun k ↦ -((τ : ℤ) * a k) := funext fun k ↦ by rw [Pi.neg_apply, hb k]
  rw [hb'] at hm
  exact hm

theorem funFieldEquiv_aeval {P : ArithVariety n} (D : AddBlockData P) (F : MvPolynomial (Fin (D.m + 1)) ℤ) :
    funFieldEquiv P (aeval (AddBlockData.toObjects D).elt F) = aeval D.x F := by
  have hZ : ∀ (R : Type) [Ring R] [Algebra ℤ R], algebraMap ℤ R = Int.castRingHom R :=
    fun _ _ _ ↦ RingHom.ext_int _ _
  show funFieldEquiv P (eval₂ (algebraMap ℤ P.FunField) (fun j : Fin (D.m + 1) ↦ (funFieldEquiv P).symm (D.x j)) F) =
    eval₂ (algebraMap ℤ (FunField P)) D.x F
  rw [hZ, hZ]
  induction F using MvPolynomial.induction_on with
  | C r =>
    rw [eval₂_C, eval₂_C]
    exact map_intCast (funFieldEquiv P) r
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p j hp =>
    simp only [eval₂_mul, eval₂_X, map_mul, hp]
    exact congrArg _ (RingEquiv.apply_symm_apply _ _)

theorem localChange_of_vectorSpace (hA : GroundTheory.Heights₂.Heights.SectionInjectivity.Statement)
    (hS : GroundTheory.Heights₂.Heights.SmallSections.Statement) : SectionInjectivity.Statement := by
  intro ι _ _ n P M k q a C hkq ha e he0 heC D hD G Γ m
  have hsv : sectionVal e ≠ 0 := sectionVal_ne_zero e he0
  refine ⟨fun s₁ _ s₂ _ h ↦ mul_right_cancel₀ (pow_ne_zero _ hsv) h, fun s hs ↦ ?_⟩
  obtain ⟨F, hF, rfl, hbd⟩ := hs
  set N := twistPow M (q - k) a C with hN
  set D₁ := AddBlockData.toObjects D
  obtain ⟨sF, hsF⟩ := (hS ι n P D₁).1 m F hF
  have hsmall := (hS ι n P D₁).2 N hD.symm G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ Γ.isHomogGenerators
    m F hF
  have hpts : D₁.extPoints = conePoints D.ext ℂ := AddBlockEq.addBlockEquiv_symm_conePoints D
  have hbd₁ : ∀ w ∈ D₁.extPoints,
      ‖eval₂ (Int.castRingHom ℂ) (D₁.newPart w) F‖ ≤ D₁.plusMetric N G.d G.g Γ.f Γ.δ w ^ m := by
    intro w hw
    rw [hpts] at hw
    exact hbd w hw
  set t := a * m with ht
  set L := ((M.pow (q - k)).mul (HermLine.standard n)).pow t with hL
  have hdeg : m • D₁.deg = L.deg := by
    show m • D.deg = _
    rw [hD, twistPow_deg]
    funext b
    simp only [hL, HermLine.pow, HermLine.mul, Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply, ht]
    push_cast
    ring
  set sA := sF.cast hdeg
  have hsA : sA.SupNormLE L (-(t * C)) := by
    intro z hz c d' ε hform hzc
    have hmk : P.mkF ε = sF.toFun * P.mkF (chartMonomial c d') :=
      SectionSmall.mkF_eq_of_mem sF hform.2
    rw [hsF] at hmk
    have hb := (hsmall ε (chartMonomial c d') hmk).2 hbd₁ z hz
    have hμ := norm_pos_iff.mpr (GroundTheory.Heights₂.Heights.SectionInjectivity.evalCone_chartMonomial_ne_zero hzc d')
    have hLz := L.metric_pos z hz.1
    have hNm : N.metric z ^ m = Real.exp (-(t * C)) * L.metric z := by
      rw [hN, twistPow_metric, mul_pow, ← Real.exp_nat_mul, hL, hermLine_pow_metric, hermLine_pow_metric,
        ← pow_mul, ht]
      congr 2
      push_cast
      ring
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ _ := hb
      _ = _ := by rw [hNm]; ring
  set e' := e.cast (congrArg HermLine.deg (powDivStd_eq M k)) with he'_def
  have he' : e'.SupNormLE ((M.pow k).mul (HermLine.standard n).inv) C := supNormLE_cast (powDivStd_eq M k) e heC
  have he'0 : e'.toFun ≠ 0 := toFun_ne_zero e' he0
  obtain ⟨s', hs'val, hs'sup⟩ := (hA ι n P M k q hkq e' C he'0 he' t).1 sA hsA
  have h1 : funFieldEquiv P sA.toFun = aeval D.x F := by
    show funFieldEquiv P sF.toFun = _
    rw [hsF]
    exact funFieldEquiv_aeval D F
  have h2 : funFieldEquiv P e'.toFun = sectionVal e := funFieldEquiv_toFun e
  have hx : aeval D.x F * sectionVal e ^ t = sectionVal s' := by
    rw [← funFieldEquiv_toFun s', hs'val, map_mul, map_pow, h1, h2]
  rw [hx]
  refine ⟨sectionVal_mem_chartLat s' (a * q * m) M.deg fun b ↦ ?_, ?_⟩
  · show ((q * t) • M.deg) b = _
    simp only [Pi.smul_apply, nsmul_eq_mul, ht]
    push_cast
    ring
  · intro g f dg df _ _ _ hval z hz
    have hmk : P.mkF g = s'.toFun * P.mkF f := by
      apply (funFieldEquiv P).injective
      rw [map_mul, funFieldEquiv_mkF, funFieldEquiv_mkF, funFieldEquiv_toFun]
      exact hval
    have h := (SectionSmall.proof ι n P (M.pow (q * t)) s').1 0 hs'sup g f hmk z hz
    rw [Real.exp_zero, one_mul, hermLine_pow_metric] at h
    rwa [show q * t = a * q * m by rw [ht]; ring] at h

end SectionInjectivityEquivalence

theorem SectionInjectivity.equiv_of (hS : GroundTheory.Heights₂.Heights.SmallSections.Statement) :
    GroundTheory.Heights₂.Heights.SectionInjectivity.Statement ↔ SectionInjectivity.Statement :=
  ⟨fun hA ↦ SectionInjectivityEquivalence.localChange_of_vectorSpace hA hS, fun _ ↦ GroundTheory.Heights₂.Heights.SectionInjectivity.proof⟩

theorem SectionInjectivity.equiv : GroundTheory.Heights₂.Heights.SectionInjectivity.Statement ↔ SectionInjectivity.Statement :=
  SectionInjectivity.equiv_of (GroundTheory.Heights₂.Heights.SmallSections.proof GroundTheory.Heights₂.Heights.ChartFormsAlt.proof)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
