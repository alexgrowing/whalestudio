import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem norms_mul_unit : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ)
    (c : Y.X → Y.Fn), (∀ x, UnitAt x (c x)) → Norms V L f a l →
    Norms V L (fun x => c x * f x) (fun σ y => Real.log ‖ratVal (c (under y)) y‖ + a σ y)
      (fun v e y => Real.log (e.w (valAt y.1 (c (below y.1)))) + l v e y) := by
  intro F _ _ Y V L f a l c hc h
  obtain ⟨r, hr, hu, hcx, hfin⟩ := h
  have split : ∀ (i : (L.B.pull V.j).ι) (g : Y.Fn) (h : Y.Fn),
      V.φ (g * h) * (r i : V.G.functionField) = V.φ g * (V.φ h * (r i : V.G.functionField)) := by
    intro i g h
    rw [map_mul, mul_assoc]
  refine ⟨r, hr, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_, fun v e y z yt i e₁ e₂ hi => ?_⟩
  · rw [split]
    exact (V.unitAt_φ (hc (V.π x))).mul (hu i x hx)
  · have H := hcx σ z y y' i e₁ e₂ hi
    have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu i _ hi
    rw [hπ] at hU
    have hC : UnitAt (V.π (under z)) (c (under y)) := by rw [hπ]; exact hc _
    have hCφ := V.unitAt_φ hC
    have n1 : ratVal (c (under y)) y ≠ 0 := by
      rw [← V.ratVal_φ z y e₁ (hc _).regAt]
      exact ratVal_ne_zero (y := z) hCφ
    have n2 : ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z ≠ 0 := ratVal_ne_zero (y := z) hU
    beta_reduce
    rw [split, ratVal_mul hCφ.regAt hU.regAt, V.ratVal_φ z y e₁ (hc _).regAt, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 n1) (norm_ne_zero_iff.2 n2), H]
    ring
  · have H := hfin v e y z yt i e₁ e₂ hi
    have hmem : below z ∈ (L.B.pull V.j).U i := by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit) := by
        rw [← e₂]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hπ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU := hu i _ hmem
    rw [hπ] at hU
    have hC : UnitAt (V.π (below z)) (c (below y.1)) := by rw [hπ]; exact hc _
    have hCφ := V.unitAt_φ hC
    have n1 : e.w (valAt y.1 (c (below y.1))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero (hc _))
    have n2 : e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff e.w).2 (SmallSec.valAt_ne_zero hU)
    beta_reduce
    rw [split, SmallSec.valAt_mul hCφ.regAt hU.regAt, V.valAt_φ z hC.regAt, e₁, map_mul,
      Real.log_mul n1 n2, H]

end GlobalTheory.CoverNorm
