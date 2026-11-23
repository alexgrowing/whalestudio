import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratorDominantRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_generator_dominant_root : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (j : Fin ((T.M c).A a).n),
  ∀ y ∈ (((T.M c).A a).chart j).target, (((T.M c).A a).chart j).symm y ∉ (T.M c).Z a →
  ∀ u : D.what₂.Tau → Fin O.Y.N → ℝ, GlobalTheory.FlagPoly.Dom u → ∀ f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn,
    (∀ x, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under ((h.man c).pt a ((((T.M c).A a).chart j).symm y))) (f x)) →
  ∃ (T' : Type) (_ : Fintype T') (p q : T' → ℕ) (ι : Type) (_ : Fintype ι) (U : Set (ι → ℂ))
    (ψ : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ) ⊕ Fin (p τ)) (Fin (q τ) ⊕ Fin (p τ)) ℂ) (a' b' : T' → ℝ)
    (Y' : Set (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ)) (π : (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ι → ℂ)
    (AW : ∀ τ, (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (lam : ∀ τ, Fin (p τ + q τ) → ℝ),
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsHodgeFrame U (ψ τ)) ∧ (∀ τ, 0 < a' τ) ∧ (∀ τ, 0 < b' τ) ∧
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y' U π (AW τ)) ∧ (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y' U π (Aω τ)) ∧
    (∀ τ, Antitone (lam τ)) ∧ y ∈ Y' ∧ ContDiffAt ℝ 2 (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam) y ∧ 0 < GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam y ∧
    ∀ w, ReciprocityTheory.AnForm.levi (fun v => ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 *
        GlobalTheory.Mean4O.lnN (O.met.hm c none ((h.man c).ε a) (O.ex x)) (f x) ((h.man c).pt a ((((T.M c).A a).chart j).symm v))) y w =
      -ReciprocityTheory.AnForm.levi (fun v => Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x)) (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω lam v)) y w / 2 := by
  first | exact @GlobalTheory.HodgeLocal.hodge_potential_local | exact GlobalTheory.HodgeLocal.hodge_potential_local | (intros; apply GlobalTheory.HodgeLocal.hodge_potential_local <;> assumption)
