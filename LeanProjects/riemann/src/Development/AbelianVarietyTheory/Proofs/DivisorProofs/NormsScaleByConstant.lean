import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNormConst

open GlobalTheory.Cartier GlobalTheory.CxPts

theorem norms_const_mul : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : F), c ≠ 0 → Norms V L f a l →
    Norms V L f (fun σ y => a σ y + Real.log ‖σ c‖)
      (fun v e y => l v e y + Real.log (NumberField.HeightOneSpectrum.adicAbv F v c)) := by
  intro F _ _ Y V L f a l c hc ⟨r, hr, hu, hinf, hfin⟩
  have hcu (x : V.G) := IndScale.unitAt_constFn (V.π ≫ Y.str) x hc
  let cu : V.G.functionFieldˣ := Units.mk0 (Cartier.constFn (V.π ≫ Y.str) c) (hcu (genericPoint V.G)).ne_zero
  have hcv : (cu : V.G.functionField) = Cartier.constFn (V.π ≫ Y.str) c := rfl
  refine ⟨fun i => r i * cu, fun i j h => ?_, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · simp only [Units.val_mul]
    rw [hr i j h, mul_assoc]
  · rw [Units.val_mul, ← mul_assoc]
    exact (hu i x hx).mul (hcu x)
  · have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu i _ hi
    rw [hπ] at hU
    beta_reduce
    rw [hinf σ z y y' i e₁ e₂ hi, Units.val_mul, ← mul_assoc, hcv,
      ratVal_mul hU.regAt (hcu _).regAt, IndScale.ratVal_constFn, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hU)) (norm_ne_zero_iff.2 ((map_ne_zero σ).2 hc))]
    ring
  · have hz : below z ∈ (L.B.pull V.j).U i := Set.mem_iInter.2 fun _ => by
      change (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ L.B.U (i PUnit.unit)
      rw [← e₂]
      exact hi (x := spMap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))) trivial
    have hπ : V.π (below z) = below y.1 := by
      show _ = y.1 _
      rw [← e₁]
      rfl
    have hU := hu i _ hz
    rw [hπ] at hU
    have hy : z ≫ (V.π ≫ Y.str) = spMap (algebraMap F (AlgebraicClosure F)) := by
      rw [← Category.assoc, e₁]
      exact y.2
    beta_reduce
    rw [hfin v e y z yt i e₁ e₂ hi, Units.val_mul, ← mul_assoc, hcv,
      OfModel.valAt_mul _ hU.regAt (hcu _).regAt, IndScale.valAt_constFn _ _ z hy, map_mul, e.w_alg,
      Real.log_mul (e.w.ne_zero (IndScale.valAt_ne_zero _ hU)) (AbsoluteValue.ne_zero _ hc)]

end GlobalTheory.CoverNormConst

end
