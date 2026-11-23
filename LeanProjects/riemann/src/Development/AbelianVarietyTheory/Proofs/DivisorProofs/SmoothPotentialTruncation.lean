import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricFlagCompactification
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam

theorem GlobalTheory.ArDegIndep.psiOf_smooth : Hypotheses2 → HypothesesH → OnObj fun D O A T H h =>
    ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ R : ℝ, 2 ≤ R → ∀ (u : Wt O.Y) (c : O.Y.Comp), (T.M c).Smooth (psiOf h x' R u c) := by
  intro _ _ D O hO _ A T H h x' R hR u c a
  obtain ⟨x, P, hc⟩ := hO
  let I := h.man c
  have hm : ∀ n, (metsOf x' O.Φ c (some R) (I.ε a) n).SmoothOn Set.univ := fun n => by
    have := (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x'.eigMetAt _ (some R)) Set.univ
      isOpen_univ (ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ x' _ R hR (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x' _)) n).2
    exact ⟨fun _ _ => this.1 trivial, fun g => (this.2 g).mono fun y hy => ⟨trivial, hy.2⟩⟩
  have h0 : ∀ n, (O.met.h0 c (I.ε a) n).SmoothOn Set.univ := fun n => by
    rw [hc.h0_eq]
    have := (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMet _) Set.univ isOpen_univ
      (x.smoothOn_eigMet _) n).2
    exact ⟨fun _ _ => this.1 trivial, fun g => (this.2 g).mono fun y hy => ⟨trivial, hy.2⟩⟩
  have hg : ((O.var c).an (I.ε a)).SmoothOn Set.univ (chgWith O (metsOf x' O.Φ) c (some R) u (I.ε a)) := by
    intro i
    refine (ContDiffOn.sum (s := Finset.univ) fun r _ => (contDiffOn_const (c := u r.1 r.2)).mul
      (GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio (hm (O.ex r)) (h0 (O.ex r)) i)).congr fun v _ => ?_
    simp [chgWith]
  have key := GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I (O.dim_eq c) a isOpen_univ hg
    (f := psiOf h x' R u c a) fun z _ => rfl
  simpa [FinHolAtlas.Smooth] using key
