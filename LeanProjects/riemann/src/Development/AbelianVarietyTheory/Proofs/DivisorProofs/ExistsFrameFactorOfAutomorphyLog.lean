import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer.FrameFn

theorem analyticAt_lin {g : ℕ} (w : Fin g → ℂ) (p : Tot Empty g) :
    AnalyticAt ℂ (fun q : Tot Empty g ↦ (Real.pi : ℂ) * (q.2 ⬝ᵥ w)) p := by
  refine analyticAt_const.mul ?_
  unfold dotProduct
  refine Finset.analyticAt_fun_sum _ fun i _ ↦ AnalyticAt.mul ?_ analyticAt_const
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin g ↦ ℂ) i).analyticAt p.2).comp analyticAt_snd

theorem isUnit_of_fn_ne {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} (f : Hol W)
    (h : ∀ p ∈ W, f.fn p ≠ 0) : IsUnit f := by
  have ha : AnalyticOnNhd ℂ (fun q ↦ (f.fn q)⁻¹) (W : Set E) := fun q hq ↦ (f.analytic q hq).inv (h q hq)
  refine IsUnit.of_mul_eq_one (b := Hol.mk (fun q ↦ (f.fn q)⁻¹) ha) (Hol.ext_fn fun p hp ↦ ?_)
  rw [Hol.fn_mul _ _ hp, Hol.fn_mk _ ha hp, mul_inv_cancel₀ (h p hp), ← Hol.ev_apply p hp, map_one]

theorem exists_frame_factor_log : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k) := by
  intro A _ g L u M u' _ hex H χ hAH K r hr j hj
  obtain ⟨-, -, hχ, hfac⟩ := hAH
  have hE : ∀ k (p : Tot Empty g) (hp : p ∈ K.W k),
      spMap (Hol.ev p hp).toRingHom ≫ r.x k = (u'.ex p.2).left := fun k p hp ↦ by
    rw [hex]; exact hr k p hp
  have hmem : ∀ k (U : A.left.Opens), ⊤ ≤ r.x k ⁻¹ᵁ U → ∀ p ∈ K.W k, ⊤ ≤ (u'.ex p.2).left ⁻¹ᵁ U :=
    fun k U hU p hp ↦ by
      rw [← hE k p hp]; exact (evalAt_fn_eq_valAt' (K.W k) (r.x k) U hU 0 p hp).1
  have hΛ : ∀ l : u.Λ, (l : Fin g → ℂ) ∈ u'.Λ := fun l ↦ (u'.ker _).1 (by rw [hex]; exact (u.ker _).2 l.2)
  have hper : ∀ (z : Fin g → ℂ) (l : u.Λ), u'.ex (z + l) = u'.ex z := fun z l ↦ by
    rw [u'.ex_add, (u'.ker _).2 (hΛ l), _root_.mul_one]
  have hfr : ∀ k, AnalyticOnNhd ℂ (fun p : Tot Empty g ↦ u'.fr (j k) p.2) (K.W k) := fun k p hp ↦
    (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn (u'.hol (M.U (j k)) 0).1 (u'.fr_hol (j k)) p.2
      (hmem k _ (hj k) p hp)).comp analyticAt_snd
  let G : u.Λ → Tot Empty g → ℂ := fun l q ↦ (Real.pi : ℂ) * (q.2 ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))
  let e : u.Λ → Tot Empty g → ℂ := fun l q ↦ χ ⟨l, hΛ l⟩ * Complex.exp (G l q +
    Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))))
  have hG : ∀ l p, AnalyticAt ℂ (G l) p := fun l p ↦ analyticAt_lin _ p
  have he : ∀ l p, AnalyticAt ℂ (e l) p := fun l p ↦ analyticAt_const.mul ((hG l p).add analyticAt_const).cexp
  have hlaw : ∀ (l : u.Λ) i (p : Tot Empty g), ⊤ ≤ (u'.ex p.2).left ⁻¹ᵁ M.U i →
      u'.fr i p.2 = e l p * u'.fr i (p.2 + l) := fun l i p h ↦ hfac ⟨l, hΛ l⟩ i p.2 h
  obtain ⟨fr, vfr⟩ : ∃ fr : ∀ k, Hol (K.W k), ∀ k, ∀ p ∈ K.W k, (fr k).fn p = u'.fr (j k) p.2 :=
    ⟨fun k ↦ Hol.mk _ (hfr k), fun k p hp ↦ Hol.fn_mk _ _ hp⟩
  obtain ⟨a, va⟩ : ∃ a : u.Λ → ∀ k, Hol (K.W k), ∀ l k, ∀ p ∈ K.W k, (a l k).fn p = e l p :=
    ⟨fun l k ↦ Hol.mk (e l) fun p _ ↦ he l p, fun l k p hp ↦ Hol.fn_mk _ _ hp⟩
  obtain ⟨lg, vl⟩ : ∃ lg : u.Λ → ∀ k, Hol (K.W k), ∀ l k, ∀ p ∈ K.W k, (lg l k).fn p = G l p :=
    ⟨fun l k ↦ Hol.mk (G l) fun p _ ↦ hG l p, fun l k p hp ↦ Hol.fn_mk _ _ hp⟩
  refine ⟨fr, a, lg, fun k ↦ ?_, fun l k' k h hh ↦ ?_, fun l k ↦ ?_, fun l k c ↦ ?_,
    fun l m k'' k' h ↦ ?_, fun l m k'' k' h ↦ ?_, fun l m k ↦ ?_⟩
  · refine isUnit_of_fn_ne _ fun p hp ↦ ?_
    rw [vfr _ p hp]
    exact u'.fr_ne _ _ (hmem k _ (hj k) p hp)
  · refine Hol.ext_fn fun p hp ↦ ?_
    have h1 := hmem k' _ hh p hp
    rw [Hol.fn_mul _ _ hp, Hol.fn_mul _ _ hp, Charts.fn_sh h _ hp, vfr _ p hp, va _ _ p hp,
      vfr _ _ (K.maps h p hp), (evalAt_fn_eq_valAt' (K.W k') (r.x k') _ hh _ p hp).2, hE k' p hp,
      u'.fr_compat _ _ _ h1, hlaw l (j k) p (fun q hq ↦ (h1 hq).2)]
    exact (_root_.mul_assoc _ _ _).symm
  · refine isUnit_of_fn_ne _ fun p hp ↦ ?_
    rw [va _ _ p hp]
    refine mul_ne_zero (fun h0 ↦ ?_) (Complex.exp_ne_zero _)
    have := hχ ⟨l, hΛ l⟩
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · refine Hol.ext_fn fun p hp ↦ ?_
    have hd : HasFDerivAt (e l) _ p :=
      (((hG l p).differentiableAt.hasFDerivAt.add_const _).cexp).const_mul (χ ⟨l, hΛ l⟩)
    rw [Hol.fn_mul _ _ hp, dw, Hol.fn_der _ _ hp, Hol.fn_der _ _ hp, va _ _ p hp,
      Hol.fderiv_fn_congr _ (va l k) hp, Hol.fderiv_fn_congr _ (vl l k) hp, hd.fderiv]
    simp only [smul_apply, smul_eq_mul, e]
    ring
  · refine Hol.ext_fn fun p hp ↦ ?_
    rw [Hol.fn_mul _ _ hp, Charts.fn_sh h _ hp, va _ _ p hp, va _ _ p hp, va _ _ _ (K.maps h p hp)]
    have h0 := hmem k'' _ (hj k'') p hp
    have h1 := hlaw (l + m) _ p h0
    have h2 := hlaw m _ p h0
    have h3 := hlaw l (j k'') ((fibFam u).shift m p) (by
      change ⊤ ≤ (u'.ex (p.2 + m)).left ⁻¹ᵁ _
      rw [hper]; exact h0)
    have h4 : u'.fr (j k'') (p.2 + (l + m : u.Λ)) ≠ 0 := u'.fr_ne _ _ (by rw [hper]; exact h0)
    have h5 : ((fibFam u).shift m p).2 + (l : Fin g → ℂ) = p.2 + (l + m : u.Λ) := by
      change p.2 + (m : Fin g → ℂ) + l = p.2 + ((l : Fin g → ℂ) + m)
      abel
    rw [h5] at h3
    refine mul_right_cancel₀ h4 ?_
    rw [← h1, h2, mul_comm (e l _), _root_.mul_assoc (e m p), ← h3]
    rfl
  · refine Hol.ext_fn fun p hp ↦ ?_
    rw [Hol.fn_add _ _ hp, Charts.fn_sh h _ hp, vl _ _ p hp, vl _ _ _ (K.maps h p hp), K.fn_cst _ _ hp,
      Hol.fn_algebraMap _ (K.base _ p hp)]
    change (Real.pi : ℂ) * ((p.2 + (m : Fin g → ℂ)) ⬝ᵥ _) = (Real.pi : ℂ) * (p.2 ⬝ᵥ _) + _
    rw [add_dotProduct, mul_add]
  · refine Hol.ext_fn fun p hp ↦ ?_
    rw [Hol.fn_add _ _ hp, vl _ _ p hp, vl _ _ p hp, vl _ _ p hp]
    simp only [G, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add, mul_add]

end GlobalTheory.AnPer.FrameFn
