import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def slTayCoef {W : Opens (Tot I g)} (h : Hol W) (k : ℕ) (s : Fin k → I) (p : Tot Empty g) : ℂ :=
  (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 fun b ↦ Pi.single (s b) 1

theorem slTayCoef_analytic {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    AnalyticOnNhd ℂ (slTayCoef h k s) W₀ := fun p hp ↦ by
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  have hG := (analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA).1
  exact analyticAt_const.mul (hG.comp analyticAt_snd)

def slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (h : Hol W) (k : ℕ) (s : Fin k → I) : Hol W₀ :=
  Hol.mk (slTayCoef h k s) (slTayCoef_analytic hW h k s)

theorem isTay_expand {R : Type} [CommRing R] [Algebra ℂ R] {N : ℕ} {t : I → R} {W : Opens (Tot I g)}
    {W₀ : Opens (Tot Empty g)} (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W)
    {ρ : Hol W →+* R ⊗[ℂ] Hol W₀} (hρ : IsTay N t ρ) (h : Hol W) :
    ρ h = ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I, (∏ b, t (s b)) ⊗ₜ[ℂ] slTayHol hW h k s := by
  refine tensor_hol_ext_of_values W₀ R _ _ fun p hp ↦ ?_
  have e := hρ h p hp
  change evT R p hp (ρ h) = evT R p hp _
  rw [e, map_sum]
  unfold GlobalTheory.PeriodFamily.taylor
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, slTayHol, Hol.fn_mk _ _ hp,
    Algebra.smul_def, mul_comm]
  rfl

theorem dw_slTayHol {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (a : Fin g) (h : Hol W) (k : ℕ) (s : Fin k → I) :
    dw a (slTayHol hW h k s) = slTayHol hW (dw a h) k s := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hA : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hD⟩ := analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k (fun b ↦ Pi.single (s b) 1) hA
  have e1 : slTayCoef h k s = (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) ∘ Prod.snd := rfl
  have hG' : DifferentiableAt ℂ (fun w : Fin g → ℂ ↦ (k.factorial : ℂ)⁻¹ *
      iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 fun b ↦ Pi.single (s b) 1) p.2 :=
    hG.differentiableAt.const_mul _
  have hev : (fun z : I → ℂ ↦ fderiv ℂ h.fn (z, p.2) ((0 : I → ℂ), Pi.single a 1)) =ᶠ[𝓝 0]
      fun z ↦ (dw a h).fn (z, p.2) := by
    have hc : Continuous fun z : I → ℂ ↦ ((z, p.2) : Tot I g) := continuous_id.prodMk continuous_const
    filter_upwards [hc.continuousAt.eventually_mem (W.isOpen.mem_nhds (hW p hp))] with z hz
    rw [dw, Hol.fn_der _ _ hz]
  rw [slTayHol, slTayHol, Hol.fn_mk _ _ hp, dw, Hol.fn_der _ _ hp,
    Hol.fderiv_fn_congr _ (F := slTayCoef h k s) (fun q hq ↦ Hol.fn_mk _ _ hq) hp, e1,
    fderiv_comp p hG' differentiableAt_snd, fderiv_snd,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', fderiv_const_mul hG.differentiableAt,
    ContinuousLinearMap.smul_apply, hD, smul_eq_mul]
  unfold slTayCoef
  congr 1
  exact (Filter.EventuallyEq.iteratedFDeriv ℂ hev k).eq_of_nhds ▸ rfl

theorem isTay_dw_lTensor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h) := by
  intro I _ _ g R _ _ N t W W₀ hW ρ hρ a h
  rw [isTay_expand hW hρ (dw a h), isTay_expand hW hρ h, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [LinearMap.lTensor_tmul, ← dw_slTayHol hW a h k s]
  rfl

end GlobalTheory.AnPer
