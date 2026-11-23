import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.KaehlerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)

noncomputable section

section Linear

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def Family.weight (F : Family A) {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]
    (φ₀ φc : Λ →ₗ[ℝ] (X → ℝ)) (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ) (lam : Λ) : X → ℝ :=
  fun x => φ₀ lam x + ∑ i, c lam i * (F.sys i).ph t x + φc lam x

theorem Family.weight_isLinearMap (F : Family A) {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]
    (φ₀ φc : Λ →ₗ[ℝ] (X → ℝ)) (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ) :
    IsLinearMap ℝ (F.weight φ₀ φc c t) where
  map_add a b := by
    funext x
    simp only [Family.weight, map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul s a := by
    funext x
    simp only [Family.weight, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring

theorem Family.chernForm_isLinearMap (F : Family A) {Λ : Type*} [AddCommGroup Λ] [Module ℝ Λ]
    (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ) (x y : X) :
    IsLinearMap ℝ fun lam => (F.chernForm (c lam) t).φ x y := by
  have h : ∀ lam, (F.chernForm (c lam) t).φ x y =
      ∑ i, c lam i * ((F.R i).θ + LocPot.ofFun ((F.sys i).ph t)).φ x y :=
    fun lam => lincomb_φ _ _ _ _ _
  constructor
  · intro a b
    rw [h (a + b), h a, h b, map_add, ← Finset.sum_add_distrib]
    simp only [Pi.add_apply, add_mul]
  · intro s a
    rw [h (s • a), h a, map_smul, smul_eq_mul, Finset.mul_sum]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

end Linear

section Currents

variable {D : ℕ} {X : Type} [TopologicalSpace X]

theorem levi_add_const' {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℝ) (c : ℝ) (z w : ι → ℂ) :
    levi (fun y => f y + c) z w = levi f z w := by
  have : fderiv ℝ (fun y => f y + c) = fderiv ℝ f := funext fun _ => fderiv_add_const c
  simp only [levi, this]

theorem System.curr_isSmoothPotForm {A : FinHolAtlas D X} {R : RegChartData A} (S : System R)
    (hr : ∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) (Om : KaehlerForm A)
    (h1 : LeviLe A Set.univ 1 (thetaOmega R) 1 Om.pot)
    (h2 : LeviLe A Set.univ (-1) Om.pot 1 (thetaOmega R)) (t : ℝ) (ht : 0 < t)
    (hl : S.ell₀ ≤ ell t) (he : errE S.C t ≤ 1) :
    IsSmoothPotForm A R.Yo R.r Om (|R.C| + |S.C|) (thetaOmega R) (S.uT t) := by
  have hsm : A.Smooth (S.uT t) := fun j => (S.smooth t ht hl j).sub contDiffOn_const
  refine ⟨⟨ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ R.θ_pot R.om_pot, h1, h2,
    fun j => (hsm j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ _))),
    fun x _ => sub_nonpos.2 (S.ph_le t ht hl x), ?_, ?_, Or.inl hsm⟩, hsm⟩
  · intro x hx
    have hL : 1 ≤ Real.log (R.r x) := by
      have := Real.log_le_log (Real.exp_pos 1) (hr x hx)
      rwa [Real.log_exp] at this
    have ha := S.le_ph t ht hl x hx
    have hb := R.le_φ x hx
    have hc := mul_le_mul_of_nonneg_right (le_abs_self R.C) (zero_le_one.trans hL)
    have hd := mul_le_mul_of_nonneg_left hL (abs_nonneg S.C)
    have he' := le_abs_self S.C
    show -((|R.C| + |S.C|) * Real.log (R.r x)) ≤ S.ph t x - S.C
    nlinarith
  · intro x k y hy w
    set f : (Fin D → ℂ) → ℝ := (fun z => R.θ.φ x z + S.ph t z) ∘ (A.chart k).symm with hfdef
    set g : (Fin D → ℂ) → ℝ := R.om.φ x ∘ (A.chart k).symm with hgdef
    have hyθ : (A.chart k).symm y ∈ R.θ.U x := hy.2.2.1.1
    have hyω : (A.chart k).symm y ∈ R.om.U x := hy.2.2.1.2
    have hf : ContDiffAt ℝ 2 f y := by
      have hθ := R.θ_pot.1 x k
      have hp := (S.smooth t ht hl k).mono
        (Set.inter_subset_inter_right _ (Set.preimage_mono (Set.subset_univ (R.θ.U x))))
      exact ((hθ.add hp).contDiffAt (((A.chart k).isOpen_inter_preimage_symm
        (R.θ.isOpen_U x)).mem_nhds ⟨hy.1, hyθ⟩)).of_le (WithTop.coe_le_coe.2 le_top)
    have hg : ContDiffAt ℝ 2 g y :=
      ((R.om_pot.1 x k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm
        (R.om.isOpen_U x)).mem_nhds ⟨hy.1, hyω⟩)).of_le (WithTop.coe_le_coe.2 le_top)
    have hfun : (potForm (thetaOmega R) (S.uT t)).φ x ∘ (A.chart k).symm =
        fun y' => (f y' + 1 * g y') + -S.C := by
      funext y'
      show (R.θ.φ x _ + R.om.φ x _) + (S.ph t _ - S.C) = _
      simp only [hfdef, hgdef, Function.comp_apply]
      ring
    rw [hfun, levi_add_const', ReciprocityTheory.AnForm.levi_add_smul 1 hf hg w, one_mul]
    have hge := S.thGe t ht hl x k y ⟨hy.1, hyθ, hyω⟩ w
    have hgnn : 0 ≤ levi g y w := by
      by_cases hw : w = 0
      · subst hw
        simp [levi]
      · exact (R.om_pos x k y ⟨hy.1, hyω⟩ w hw).le
    have hprod := mul_nonneg (sub_nonneg.2 he) hgnn
    show 0 ≤ levi f y w + levi g y w
    nlinarith

end Currents

def LinearWeights.Statement : Prop :=
  (∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (F : Family A)
      (Λ : Type) [AddCommGroup Λ] [Module ℝ Λ] (φ₀ φc : Λ →ₗ[ℝ] (X → ℝ))
      (c : Λ →ₗ[ℝ] (Fin F.m → ℝ)) (t : ℝ),
      IsLinearMap ℝ (F.weight φ₀ φc c t) ∧
        ∀ x y : X, IsLinearMap ℝ fun lam => (F.chernForm (c lam) t).φ x y) ∧
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (R : RegChartData A)
    (S : System R), (∀ x ∈ R.Yo, Real.exp 1 ≤ R.r x) →
    ∃ (Om : KaehlerForm A) (C₁ : ℝ), ∀ t, 0 < t → S.ell₀ ≤ ell t → errE S.C t ≤ 1 →
      IsSmoothPotForm A R.Yo R.r Om C₁ (thetaOmega R) (S.uT t)

theorem LinearWeights.proof (hK : KaehlerBound.Statement) : LinearWeights.Statement := by
  refine ⟨fun A F Λ _ _ φ₀ φc c t => ⟨F.weight_isLinearMap φ₀ φc c t,
    fun x y => F.chernForm_isLinearMap c t x y⟩, ?_⟩
  intro D X _ A R S hr
  obtain ⟨Om, h1, h2⟩ := hK A R
  exact ⟨Om, |R.C| + |S.C|, fun t ht hl he => S.curr_isSmoothPotForm hr Om h1 h2 t ht hl he⟩

section Inhabitants

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
