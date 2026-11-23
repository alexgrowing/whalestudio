import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodge
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open scoped ContDiff

open GlobalTheory.Mean4 GlobalTheory.Mean4O in

theorem GlobalTheory.InterpChgSmooth.smooth_phR : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ =>
    ∀ c u σ (R : ℝ), 2 ≤ R → ((T.M c).A σ).Smooth ((T.F c).phR R u σ) := by
  intro _ _ D O hO _ A T H h c u a R hR
  obtain ⟨x, P, hc⟩ := hO
  let I := h.man c
  have hm : ∀ n, (O.met.hm c (some R) (I.ε a) n).SmoothOn Set.univ := fun n => by
    rw [hc.hm_eq]
    exact (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMetAt _ (some R)) Set.univ isOpen_univ
      (ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ x _ R hR (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x _)) n).2
  have h0 : ∀ n, (O.met.h0 c (I.ε a) n).SmoothOn Set.univ := fun n => by
    rw [hc.h0_eq]
    exact (FlagCpt.smoothOn_met_of_eigMet _ _ _ _ _ _ _ _ _ _ _ (O.Φ.C c) (I.ε a) (x.eigMet _) Set.univ isOpen_univ
      (x.smoothOn_eigMet _) n).2
  have hg : ((O.var c).an (I.ε a)).SmoothOn Set.univ (O.chg c (some R) u (I.ε a)) := by
    intro i
    refine (ContDiffOn.sum (s := Finset.univ) fun r _ => (contDiffOn_const (c := u r.1 r.2)).mul
      (GlobalTheory.HodgeChgSmooth.smoothOn_lnRatio (hm (O.ex r)) (h0 (O.ex r)) i)).congr fun v _ => ?_
    simp [Setup.chg]
  have key := GlobalTheory.HodgeChgSmooth.smoothOn_of_manIs I (O.dim_eq c) a isOpen_univ hg
    (f := (T.F c).phR R u a) fun z _ => (h.an c).phR R hR u a z
  intro j
  simpa using key j

end
