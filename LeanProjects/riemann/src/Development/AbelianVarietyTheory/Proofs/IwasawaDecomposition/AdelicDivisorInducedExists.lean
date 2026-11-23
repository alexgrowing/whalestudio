import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AltSumMultilinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArakelovTopUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleModelsOfHtBoundStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueCx

namespace GlobalTheory.ShFam.Pad.ArTopLine

theorem mSmooth_metsOf_none_zero {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Letter S.Dw → ℤ) (hn : n = 0) :
    (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k none σ n) := by
  subst hn
  have e : metsOf x Φ k none σ 0 = refMet x Φ k σ 0 := by
    simp only [metsOf, refMet, FlagCpt.met, FlagCpt.genSq, Pi.zero_apply, zpow_zero, Finset.prod_const_one]
    first | rfl | congr 1
  rw [e]
  exact (GlobalTheory.T.family_metrics_smooth D A N j S κ s x Φ k σ 0).2.1

end GlobalTheory.ShFam.Pad.ArTopLine

open GlobalTheory.ShFam.Pad.ArTopLine in

theorem GlobalTheory.ShFam.Pad.induced_adlOf_line : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (R : ℝ), 2 ≤ R → ∀ w : Sym D.host.E →₀ ℤ, (∀ a ∈ w.support, {q | a.1 q = true}.Finite ∧ a.2.1 = some R) → ∃ (M : GlobalTheory.TrueGeo.Model (Φ.C k).Y) (L : GlobalTheory.HermLB M.p) (m : ℕ+), (adlOf (Φ.C k) (metsOf x Φ k) w).Induced M L m 0 := by
  intro hHT D A N j S κ s x Φ k R hR w hw
  obtain ⟨M, L, m, r, hL, hP, hfin⟩ :=
    GlobalTheory.T.exists_model_presenting_divisor hHT D A N j S κ s Φ (GlobalTheory.T.admissible_models_of_ht_bound hHT D A N j S κ) k w fun a ha => (hw a ha).1
  have hsm : ∀ σ, (cxSt D.what₂.LL).mSmooth _ σ _ ((adlOf (Φ.C k) (metsOf x Φ k) w).m σ) := by
    intro σ
    show (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (parOf w) σ (expo S.Dw w))
    by_cases hne : w.support.Nonempty
    · have hpar : parOf w = some R := by
        unfold parOf
        rw [dif_pos hne]
        exact (hw _ hne.choose_spec).2
      rw [hpar]
      exact (GlobalTheory.T.family_metrics_smooth D A N j S κ s x Φ k σ (expo S.Dw w)).1 R hR
    · have hw0 : w = 0 := Finsupp.support_eq_empty.1 (Finset.not_nonempty_iff_eq_empty.1 hne)
      have hpar : parOf w = none := by
        unfold parOf
        rw [dif_neg hne]
      rw [hpar]
      refine mSmooth_metsOf_none_zero x Φ k σ _ ?_
      subst hw0
      funext z
      simp [expo]
  obtain ⟨L', hL'⟩ := GlobalTheory.T.metric_conjugation_invariant D.what₂.LL (Φ.C k).Y (adlOf (Φ.C k) (metsOf x Φ k) w) M L hL m r hP rfl hsm
    (fun σ σ' p p' a hp hpa => (GlobalTheory.T.metric_conjugation_symmetry D A N j S κ s x Φ k σ σ' (expo S.Dw w) p p' a hp hpa).1 (parOf w))
    hfin
  exact ⟨M, L', m, hL'⟩
