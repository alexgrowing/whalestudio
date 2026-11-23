import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

namespace P_spTwBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_detAbsPow (N : ℕ) (s : ℂ) : IsSmoothChar (detChar (Fin N) (absPow k s)) :=
  (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow k s)).detChar

theorem hasDetVec_twist_absPow {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (s : ℂ) (h : HasDetVec ρ η) :
    HasDetVec (GlobalTheory.SmGL.twist ρ (detChar (Fin N) (absPow k s))) η := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.LocGL.detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) hg, hv g hg,
    Units.val_one, one_smul]

end P_spTwBasic

theorem step_spTwBasic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.NonzeroBasicTwistOfSpecialForm := by
  intro Y _ _ τ a hs hi hd
  unfold twD
  exact ⟨GlobalTheory.SmGL.isSmooth_twist hs (P_spTwBasic.isSmoothChar_detAbsPow _ _),
    GlobalTheory.LocGL.isIrreducible_twist hi _, P_spTwBasic.hasDetVec_twist_absPow _ _ _ hd⟩

end UpperTheory.TNZ.Grp
