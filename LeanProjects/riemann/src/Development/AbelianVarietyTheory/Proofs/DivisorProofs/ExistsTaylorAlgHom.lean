import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace TensorProduct GlobalTheory.AnPer

namespace GlobalTheory.TaylorHom

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)}

theorem eventually_mem {w : Fin g → ℂ} (h : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, w) : Tot I g) ∈ W := by
  have hc : Continuous fun z : I → ℂ ↦ ((z, w) : Tot I g) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds h)

theorem analyticAt_slice (h : Hol W) {w : Fin g → ℂ} (hw : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    AnalyticAt ℂ (fun z : I → ℂ ↦ h.fn (z, w)) 0 := by
  have hp : AnalyticAt ℂ (fun z : I → ℂ ↦ ((z, w) : Tot I g)) 0 :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := h.fn) (f := fun z : I → ℂ ↦ ((z, w) : Tot I g)) (h.analytic _ hw) hp

def coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W) : Hol W₀ :=
  Hol.mk (fun p ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v) fun p hp ↦
    AnalyticAt.comp (g := fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) (f := Prod.snd)
      (GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v (h.analytic _ (hW p hp))).1 analyticAt_snd

theorem fn_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    {p : Tot I₀ g} (hp : p ∈ W₀) : (coef hW k v h).fn p = iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v := by
  unfold coef
  exact Hol.fn_mk _ _ hp

theorem dw_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    (a : Fin g) : dw a (coef hW k v h) = coef hW k v (dw a h) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hH : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hG'⟩ := GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v hH

  have hL : (dw a (coef hW k v h)).fn p =
      fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) p.2 (Pi.single a 1) := by
    rw [show dw a (coef hW k v h) =
        Hol.der ((0, Pi.single a 1) : Tot I₀ g) (coef hW k v h) from rfl, Hol.fn_der _ _ hp,
      Hol.fderiv_fn_congr (F := fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) _
        (fun q hq ↦ fn_coef hW k v h hq) hp]
    have hc := (hG.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_snd (p := p))).fderiv
    rw [show (fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) =
        (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) ∘ Prod.snd from rfl, hc]
    rfl
  have hR : (coef hW k v (dw a h)).fn p =
      iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1)) 0 v := by
    rw [fn_coef hW k v (dw a h) hp]
    have hev : (fun z : I → ℂ ↦ (dw a h).fn (z, p.2)) =ᶠ[𝓝 0]
        fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1) := by
      filter_upwards [eventually_mem (hW p hp)] with z hz
      exact Hol.fn_der _ _ hz
    exact congrFun (congrArg DFunLike.coe ((hev.iteratedFDeriv (𝕜 := ℂ) k).eq_of_nhds)) v
  rw [hL, hR]
  exact hG' _

variable [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D]

def poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W) : D ⊗[ℂ] Hol W₀ :=
  ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I,
    ((k.factorial : ℂ)⁻¹ • ∏ a, t (s a)) ⊗ₜ[ℂ] coef hW k (fun a ↦ Pi.single (s a) 1) h

theorem ev_poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W)
    (p : Tot I₀ g) (hp : p ∈ W₀) :
    Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
      (poly hW N t h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2) := by
  simp only [poly, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
    Algebra.ofId_apply, Hol.ev_apply, fn_coef hW _ _ h hp, GlobalTheory.PeriodFamily.taylor]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

theorem exists_taylor_algHom : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot I₀ g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∃ Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : Tot I₀ g) (hp : p ∈ W₀),
      Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
        (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) ∧
      ∀ a h, Ta (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (Ta h) := by
  intro I I₀ _ _ _ g D _ _ N t ht W W₀ hW

  have slice_eq : ∀ {p : Tot I₀ g} (_ : p ∈ W₀) {F : (I → ℂ) → ℂ} (x : Hol W),
      (∀ z, ((z, p.2) : Tot I g) ∈ W → x.fn (z, p.2) = F z) →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ x.fn (z, p.2)) = GlobalTheory.PeriodFamily.taylor N t F := by
    intro p hp F x hx
    apply GlobalTheory.PeriodFamily.taylor_congr_germ
    filter_upwards [eventually_mem (hW p hp)] with z hz
    exact hx z hz
  have hconst : ∀ c : ℂ, poly hW N t (algebraMap ℂ (Hol W) c) = algebraMap ℂ (D ⊗[ℂ] Hol W₀) c := by
    intro c
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [ev_poly, AlgHom.commutes, slice_eq hp (F := fun _ ↦ c) _ fun z hz ↦ Hol.fn_algebraMap c hz,
      GlobalTheory.PeriodFamily.taylor_const_fun]
  have hadd : ∀ x y : Hol W, poly hW N t (x + y) = poly hW N t x + poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_add, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) + y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_add x y hz,
      GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  have hmul : ∀ x y : Hol W, poly hW N t (x * y) = poly hW N t x * poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_mul, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) * y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_mul x y hz,
      GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  refine ⟨{ toFun := poly hW N t
            map_one' := by simpa only [map_one] using hconst 1
            map_mul' := hmul
            map_zero' := by simpa only [map_zero] using hconst 0
            map_add' := hadd
            commutes' := hconst }, fun h p hp ↦ ev_poly hW N t h p hp, fun a h ↦ ?_⟩
  show poly hW N t (dw a h) = LinearMap.lTensor D (dw a).toLinearMap (poly hW N t h)
  simp only [poly, map_sum, LinearMap.lTensor_tmul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← dw_coef]
  rfl

end GlobalTheory.TaylorHom
