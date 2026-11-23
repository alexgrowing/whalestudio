import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointRowWeightDualWeylModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightBoundsDualWeylModuleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointRowWeightAntitoneOfMaxPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRowCoefMemCoefAlgebraOfDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeighStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem GlobalTheory.HighWt.simpleSubquot_embeds : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∃ mu : ι → ℕ → ℕ, (∀ τ, Antitone (res N (mu τ)) ∧ ∑ a : Fin N, mu τ a = ∑ a : Fin N, lam τ a ∧ (∀ a : Fin N, lam τ (N - 1) ≤ mu τ a ∧ mu τ a ≤ lam τ 0) ∧ ∃ (e : alg O N lam) (z : Gm), IsProj O N lam τ (res N (mu τ)) e ∧ e • z ≠ 0) ∧ Embeds O N lam mu ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam Gm _ _ hs hsub
  classical
  haveI : Nontrivial Gm := IsSimpleModule.nontrivial (alg O N lam) Gm
  obtain ⟨w0, hw0⟩ := GlobalTheory.T.exists_jointRowWeight_dualWeylModule O N ι lam Gm inferInstance
  have hB := GlobalTheory.T.jointRowWeight_bounds_dualWeylModule O N ι lam hlam Gm
  let S : Set (ι → Fin N → ℕ) := {w | GlobalTheory.HighWt.JointWt O N lam Gm w}
  have hfin : S.Finite := by
    refine Set.Finite.subset (Set.Finite.pi (t := fun τ => Set.pi Set.univ fun _ : Fin N => Set.Iic (lam τ 0))
      fun τ => Set.Finite.pi fun _ => Set.finite_Iic _) ?_
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies]
    intro τ a
    exact ((hB w hw τ).2 a).2
  obtain ⟨w, hwS, hmax⟩ := hfin.toFinset.exists_max_image (GlobalTheory.HighWt.pot N) ⟨w0, hfin.mem_toFinset.2 hw0⟩
  rw [Set.Finite.mem_toFinset] at hwS
  have hmax' : ∀ w', GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w :=
    fun w' h' => hmax w' (hfin.mem_toFinset.2 h')
  have hanti := GlobalTheory.T.jointRowWeight_antitone_of_maxPotential O N ι lam Gm w hwS hmax'
  refine ⟨GlobalTheory.HighWt.extW N w, fun τ => ?_, GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight O N ι lam ϖ hϖ hlam GlobalTheory.T.highest_weight_base_change (GlobalTheory.T.genericRowCoef_mem_coefAlgebra_of_domain O N ι lam) Gm hs hsub w hanti hwS hmax'⟩
  rw [GlobalTheory.HighWt.res_extW]
  refine ⟨hanti τ, ?_, ?_, ?_⟩
  · have := (hB w hwS τ).1
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using this
  · intro a
    simpa [GlobalTheory.HighWt.extW, Fin.is_lt] using (hB w hwS τ).2 a
  · obtain ⟨a, ha, -⟩ := GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam τ (w τ)
    obtain ⟨z, hz, hfix⟩ := hwS
    let e : alg O N lam := ⟨a, Algebra.subset_adjoin (Or.inr ⟨τ, w τ, ha⟩)⟩
    refine ⟨e, z, ha, ?_⟩
    rw [hfix τ e ha]
    exact hz

end
