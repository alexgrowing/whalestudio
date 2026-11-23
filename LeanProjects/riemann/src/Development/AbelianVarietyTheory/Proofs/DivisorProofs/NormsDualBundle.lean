import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem Norms.dual : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn)
    (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ),
    Norms V L f a l → Norms V L.dual (fun x => (f x)⁻¹) (fun σ y => -a σ y) (fun v e y => -l v e y) := by
  intro F _ _ Y V L f a l h
  obtain ⟨r, hr, hun, hcx, hfin⟩ := h
  have key : ∀ (i : (L.B.pull V.j).ι) (g : Y.Fn),
      V.φ g⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField) = (V.φ g * r i)⁻¹ := by
    intro i g
    rw [map_inv₀, Units.val_inv_eq_inv_val, mul_inv]
  refine ⟨fun i => (r i)⁻¹, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have e := hr i j hij
    have e' : fnOf _ hij (((CechPic.dual L.B).pull V.j).g i j).val = (fnOf _ hij ((L.B.pull V.j).g i j).val)⁻¹ :=
      (congrArg (fun u : Γ(V.G, (L.B.pull V.j).U i ⊓ (L.B.pull V.j).U j)ˣ => fnOf _ hij u.val)
        (GlobalTheory.LineNorm.Neg.pull_dual_g L.B V.j i j)).trans (map_units_inv _ _)
    refine Eq.trans ?_ (congrArg (· * _) e').symm
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e, mul_inv]
    rfl
  · intro i x hx
    show UnitAt x (V.φ (f (V.π x))⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField))
    rw [key i (f (V.π x))]
    exact (hun i x hx).inv
  · intro σ z y y' i e1 e2 hi
    have H := hcx σ z y y' i e1 e2 hi
    rw [show (L.dual.φ _).φ (i PUnit.unit) y' = -((L.φ _).φ (i PUnit.unit) y') from rfl]
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e1]
      rfl
    have hx : under z ∈ (L.B.pull V.j).U i := hi
    have hU := hun i _ hx
    rw [hπ] at hU
    have one : ratVal (1 : V.G.functionField) z = 1 := by
      have e := ratVal_fnOf (y := z) CxPts.mem_ptsIn_top trivial 1
      rw [map_one] at e
      rw [e]
      exact CxPts.ev_one CxPts.mem_ptsIn_top
    have k3 : ratVal (V.φ (f (under y)) * (r i : V.G.functionField))⁻¹ z *
        ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z = 1 := by
      rw [← ratVal_mul hU.inv.regAt hU.regAt, inv_mul_cancel₀ hU.ne_zero, one]
    have h0 : ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z ≠ 0 := right_ne_zero_of_mul_eq_one k3
    have h0' : ratVal (V.φ (f (under y)) * (r i : V.G.functionField))⁻¹ z ≠ 0 := left_ne_zero_of_mul_eq_one k3
    have k4 := congrArg (fun t : ℂ => Real.log ‖t‖) k3
    simp only [norm_mul, norm_one, Real.log_one] at k4
    rw [Real.log_mul (norm_ne_zero_iff.2 h0') (norm_ne_zero_iff.2 h0)] at k4
    show -a σ y = Real.log ‖ratVal (V.φ (f (under y))⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField)) z‖ - _
    rw [key i (f (under y))]
    linarith
  · intro v e y z yt i e1 e2 hi
    have H := hfin v e y z yt i e1 e2 hi
    have hmem : below z ∈ (L.B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← e2]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e1]
      rfl
    have hU := hun i _ hmem
    rw [hπ] at hU
    show -l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1))⁻¹ * (((r i)⁻¹ : V.G.functionFieldˣ) : V.G.functionField))))
    rw [key i (f (below y.1)), GlobalTheory.LineNorm.Neg.valAt_inv hU, map_inv₀, Real.log_inv, H]

end GlobalTheory.CoverNorm
