import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmooth

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spLift

variable {Γ V W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_eigen_lift {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) {L : Subgroup Γ} (hL : IsCompact (L : Set Γ)) (χ : Γ → ℂ)
    (u : V) (hu : f u ≠ 0) (hχ : ∀ g ∈ L, σ g (f u) = χ g • f u) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ L, ρ g v = χ g • v :=
  _root_.UpperTheory.Reformulated.B.DYka2.main hρ f hL χ u hu hχ

end UpperTheory.TNZ.Grp.P_spLift

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spLift {n : ℕ} (G : Grp k n) : G.SpecialLiftProp := by
  intro W X _ _ _ _ ρ σ hρ hsq hη
  obtain ⟨S, f, hf⟩ := hsq
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨u, rfl⟩ := hf y
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g | S.toRepresentation g v = v} = {g | ρ g (v : W) = v} := by
      ext g
      simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  have hL : IsCompact ((leviK k (fun a : Fin G.s => Fin (G.d a))) :
      Set (Levi k fun a : Fin G.s => Fin (G.d a))) := by
    rw [leviK, Subgroup.coe_pi]
    exact isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  obtain ⟨v, hv, hvη⟩ := P_spLift.exists_eigen_lift hS f hL G.eta u hy hyη
  refine ⟨(v : W), fun h => hv (Subtype.ext h), fun m hm => ?_⟩
  exact congrArg Subtype.val (hvη m hm)

end UpperTheory.TNZ.Grp
