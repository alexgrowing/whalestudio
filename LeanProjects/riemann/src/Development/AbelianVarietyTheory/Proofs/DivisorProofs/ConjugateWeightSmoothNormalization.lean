import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem isRatSec_one_pull_triv (V : Cover Y) :
    IsRatSec ((LB.triv V.X).pull V.j) (fun _ => 1) := fun a b h => by
  have hL := LB.isLB_pull (LB.isLB_triv V.X) V.j
  obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
  have := congrArg (fun u : Γ(V.G, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
  rw [Units.val_one, map_one] at this
  exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm

theorem norms_triv_fnB : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y), Norms V (HermLB.triv V.p) (fun _ => 1) (fun _ _ => 0) (fun _ _ _ => 0) ∧ ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → a σ y = -(u _ y' / 2)) → Norms V (ArInt.fnB u hu hc) (fun _ => 1) a (fun _ _ _ => 0) := by
  intro F _ _ Y V
  have hcx {σ : F →+* ℂ} (z : CxPts (V.π ≫ Y.str) σ) :
      Real.log ‖ratVal (V.φ 1 * ((1 : V.G.functionFieldˣ) : V.G.functionField)) z‖ = 0 := by
    rw [map_one, Units.val_one, mul_one]
    have e := ratVal_fnOf (y := z) CxPts.mem_ptsIn_top trivial 1
    rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    rw [e, norm_one, Real.log_one]
  have hfin {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) :
      0 = Real.log (e.w (valAt z (V.φ 1 * ((1 : V.G.functionFieldˣ) : V.G.functionField)))) := by
    rw [map_one, Units.val_one, mul_one, GlobalTheory.TrueGeo.Res.valAt_one, map_one, Real.log_one]
  refine ⟨⟨fun _ => 1, isRatSec_one_pull_triv V, fun i x _ => ?_, fun σ z y y' i _ _ _ => ?_,
    fun v e y z yt i _ _ _ => hfin e z⟩, fun u hu hc a ha => ⟨fun _ => 1, isRatSec_one_pull_triv V,
    fun i x _ => ?_, fun σ z y y' i e₁ e₂ _ => ?_, fun v e y z yt i _ _ _ => hfin e z⟩⟩
  · rw [map_one, Units.val_one, mul_one]; exact unitAt_one x
  · rw [hcx]
    show (0 : ℝ) = 0 - 0 / 2
    ring
  · rw [map_one, Units.val_one, mul_one]; exact unitAt_one x
  · rw [hcx, ha σ z y y' e₁ e₂]
    show -(u _ y' / 2) = 0 - u _ y' / 2
    ring

end GlobalTheory.CoverNorm
