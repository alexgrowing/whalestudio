import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsIrrOfEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyGrpData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesHarishChandra
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinLoc

open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

theorem kFin_rank_zero {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h0 : V.rank = 0) :
    kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ),
      GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  have hsub : ∀ g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ, g = g' := fun g g' =>
    Matrix.ext fun i _ => absurd i.2 (by omega)
  have hσ1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  have hσ : ∀ g, M.σ τ g = 1 := fun g => by rw [hsub g 1, hσ1]
  have hrep : ∀ g, M.rep τ g = 1 := fun g => hσ _
  refine ⟨fun x _ => Submodule.subset_span ?_, fun _ => 0, ⟨fun X _ v => ?_, fun X _ v w => by simp⟩, ?_⟩
  · intro k Xs _
    simp only [hrep, ContinuousLinearMap.one_apply]
    exact contDiff_const
  · simp only [hrep, ContinuousLinearMap.one_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact hasDerivAt_const _ _
  · haveI : CompleteSpace (M.H τ) := (M.ds τ).1

    have hline : ∀ x y : M.H τ, x ≠ 0 → ∃ c : ℂ, c • x = y := fun x y hx => by
      have hcl : IsClosed ((ℂ ∙ x : Submodule ℂ (M.H τ)) : Set (M.H τ)) := Submodule.closed_of_finiteDimensional _
      rcases (M.ds τ).2.2.2.1 _ hcl (fun g _ v hv => by rwa [hσ, ContinuousLinearMap.one_apply]) with hb | ht
      · exact absurd ((Submodule.span_singleton_eq_bot).1 hb) hx
      · exact Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top)
    have hK : ∀ x y : kFin M τ, x ≠ 0 → ∃ c : ℂ, c • x = y := fun x y hx => by
      obtain ⟨c, hc⟩ := hline x y (fun e => hx (Subtype.ext e))
      exact ⟨c, Subtype.ext hc⟩
    refine ⟨fun N _ => ?_, fun T _ => ?_⟩
    · by_cases hN : N = ⊥
      · exact Or.inl hN
      · right
        obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
        refine eq_top_iff.2 fun y _ => ?_
        obtain ⟨c, rfl⟩ := hK x y hx0
        exact N.smul_mem c hxN
    · by_cases hz : ∀ x : kFin M τ, x = 0
      · exact ⟨0, LinearMap.ext fun x => by rw [hz x]; simp⟩
      · push_neg at hz
        obtain ⟨x, hx0⟩ := hz
        obtain ⟨c, hc⟩ := hK x (T x) hx0
        refine ⟨c, LinearMap.ext fun y => ?_⟩
        obtain ⟨d, rfl⟩ := hK x y hx0
        rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]

theorem kFin_smooth_absIrr (hH : GlobalTheory.Published.HarishChandraModules) (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) :
    kFin M τ ≤ M.sm τ ∧ ∃ a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ),
      GlobalTheory.Chain.IoLift.IsKAct M τ a ∧ GlobalTheory.Chain.IoLift.AbsIrr (fun X : lieAt V τ => a X) := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · exact kFin_rank_zero M τ h0
  obtain ⟨p, q, e, he⟩ : ∃ p q : ℕ, ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.RealPar.BlockOrd e (M.ε τ) :=
    ⟨_, _, GlobalTheory.RealPar.exists_blockOrd (M.ε τ) rfl rfl⟩
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard
  have hn : 1 ≤ p + q := hcard ▸ hpos
  let T : GrpData p q := Classical.choice (GlobalTheory.DetSqrtCover.nonempty_grpData p q)
  let P : GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters.SignedPar V.rank :=
    ⟨M.lam τ, M.ε τ, GlobalTheory.DSParam.isHCParam_of_isDS _ _ _ _ _ (M.enum τ).1 (M.ds τ)⟩
  have hsc : SignCompat (M.ε τ) e := by
    rintro (a | a)
    · exact he.1 a
    · exact he.2.1 a
  obtain ⟨R, U, -, hU⟩ := GlobalTheory.CoverModel.exists_pull T (fun U hU => ((hH.1 p q hn T).1 U hU).2.1) P
    (e := e) he (σ := M.σ τ) (M.ds τ)
  have hM : Matches R M τ (plainMat e) 0 U :=
    GlobalTheory.CoverModel.matches_of_grp hH (s := RingHom.id ℂ) (fun _ => rfl) R M τ
      (GlobalTheory.CoverModel.isFormIso_plainMat hsc) 0 U (fun g x => by simp [hU, plainMat])
  obtain ⟨hs, a, ha⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D V S M τ _ _ T R _ 0 _ hM
  have hAI := ((hH.1 p q hn T).1 R.U ⟨R.nontriv, R.irred⟩).2.2 R.HK R.ι ⟨R.ι_inj, R.ι_range, R.der⟩
  exact ⟨hs, a, ha, GlobalTheory.KFinIrr.absIrr_kFin D V S M τ _ _ T R _ 0 U.toLinearEquiv a hM hAI.2 hAI.1 ha⟩

end GlobalTheory.KFinLoc

end
