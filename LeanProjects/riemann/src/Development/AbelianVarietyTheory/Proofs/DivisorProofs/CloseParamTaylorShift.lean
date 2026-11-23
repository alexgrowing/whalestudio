import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSumSubValueEqSumSqZero

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnPer.close_paramTaylor_shift : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) (F₀ : Fam I₀ g Λ), (0 : I → ℂ) ∈ F.V → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D) (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → (∀ i, t i = ∑ j, n j i) → ∀ (K : Charts F) (K₀ : Charts F₀) (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (Ta : Hol (K.W k) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀)) (Ta' : Hol (K.W k') →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀')), (∀ (h : Hol (K.W k)) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → (∀ (h : Hol (K.W k')) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀'), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta' h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀'))) (Ta'.toRingHom.comp (Charts.sh h)) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀))).comp Ta).toRingHom) := by
  intro I I₀ _ _ _ g D _ _ Λ _ F F₀ h0 hτ J N hN t r n hn hnn ht K K₀ l k k' k₀ k₀' h h₀ hW Ta Ta' hTa hTa'
  have htJ : ∀ i, t i ∈ J := fun i ↦ by rw [ht]; exact J.sum_mem fun j _ ↦ hn j i
  have hnil : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0 := fun s ↦ hN _ fun a ↦ htJ _
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l 0 h0
  obtain ⟨n', h1, h2, h3⟩ := GlobalTheory.PeriodFamily.taylor_sum_sub_value_eq_sum_sqZero J N hN r n hn hnn (fun (a : Fin g) z ↦ F.τ l z a)
    fun a ↦ analyticAt_pi_iff.1 hτa a
  have et : (fun i ↦ ∑ j, n j i) = t := funext fun i ↦ (ht i).symm
  rw [et] at h3
  obtain ⟨-, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hm : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k := fun p hp ↦ K.maps h _ (hW p hp)
  refine GlobalTheory.AnPer.close_of_sliceTaylor J N hN t htJ r n' h1 h2 (K.W k) (K₀.W k₀') (fun p : Tot I₀ g ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hm _ _ (fun f p hp ↦ ?_) fun f p hp ↦ ?_
  · refine (hTa' (Charts.sh h f) p hp).trans ?_
    have e : (fun z : I → ℂ ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := by fun_prop
      filter_upwards [hc.continuousAt.eventually ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
        using Charts.fn_sh h f hz
    rw [hcongr _ _ e, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (F.τ l) p.2 hτa (f.analytic _ (hm p hp))]
    simp only [h3]
  · have hp' := K₀.maps h₀ p hp
    have e : ∀ x : D ⊗[ℂ] Hol (K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀)) x) =
        Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev (F₀.shift l p) hp')) (fun _ _ ↦ Commute.all _ _) x := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul d c =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
          Hol.ev_apply, Hol.fn_comap _ _ _ _ hp, AlgHom.id_apply]
    refine (e (Ta f)).trans ((hTa f _ hp').trans ?_)
    have e2 : (F₀.shift l p).2 = p.2 + F.τ l 0 := by simp only [Fam.shift, hτ]
    rw [e2, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hm p hp))]
    simp only [hconst, sub_self]
