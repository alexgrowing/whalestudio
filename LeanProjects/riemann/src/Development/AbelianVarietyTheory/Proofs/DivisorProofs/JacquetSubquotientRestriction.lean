import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalBlockLeviSemisimpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientSemisimpleRestrictionStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock

noncomputable section

namespace GlobalTheory.MidIrr

theorem exists_smIrr_subquotient_map : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N l n : ℕ) (h : l + n ≤ N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (Q : Representation ℂ (GL (Fin n) k) W),
      IsSubquotient Q ((jacU (tripPlace h) π).comp (midHom k l n N)) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (η : Representation ℂ (GL (Fin n) k) Y) (f : Q.IntertwiningMap η), f ≠ 0 →
      ∃ ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) k), IsSubquotient ρ.ρ ((jacU (tripPlace h) π).comp (midHom k l n N)) ∧
        ∃ g : ρ.ρ.IntertwiningMap η, g ≠ 0 := by
  intro hBZ k _ _ _ _ N l n h V _ _ π hπ hfl W _ _ Q hQ Y _ _ η f hf
  set e := tripPlace h with he
  have hL : HasFiniteLength (jacU e π) :=
    (GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff (jacU e π) (deltaHalf k _)⁻¹).1
      ((hBZ k).2.1 _ _ _ e V π hπ hfl)
  have hsm : IsSmooth ((jacU e π).comp (midHom k l n N)) :=
    isSmooth_comp (isSmooth_jacU e hπ) _ (continuous_mulSingle (A := fun j : Fin 3 => GL (Fin (tripSizes l n N j)) k) 1)
  obtain ⟨S, p, hp⟩ := hQ
  let F : S.toRepresentation.IntertwiningMap η := f.comp p
  have hF : F ≠ 0 := by
    intro h0
    apply hf
    ext w
    obtain ⟨x, rfl⟩ := hp w
    exact congrArg (fun G : S.toRepresentation.IntertwiningMap η => G x) h0
  obtain ⟨R, hRi, hRle⟩ := GlobalTheory.T.subquotient_semisimple_restriction _ _ (midHom k l n N) _ (jacU e π) hL
    (fun Z _ _ τ hτ hi => GlobalTheory.T.cuspidal_block_levi_semisimple hBZ k l n N Z τ (hτ.isSmooth (isSmooth_jacU e hπ)) hi) S Y η F hF

  let T : Subrepresentation S.toRepresentation :=
    ⟨R.toSubmodule.comap F.toLinearMap, fun g x hx => by
      show F (S.toRepresentation g x) ∈ R.toSubmodule
      rw [F.isIntertwining]
      exact R.apply_mem_toSubmodule g hx⟩
  let q : T.toRepresentation.IntertwiningMap R.toRepresentation :=
    ⟨(F.toLinearMap.restrict (p := T.toSubmodule) (q := R.toSubmodule) fun x hx => hx), fun g => by
      ext x
      exact F.isIntertwining _ _ g x⟩
  have hq : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hRle hy
    exact ⟨⟨x, show F x ∈ R.toSubmodule from hx ▸ hy⟩, Subtype.ext hx⟩
  have h1 : IsSubquotient R.toRepresentation S.toRepresentation := ⟨T, q, hq⟩
  have h2 : IsSubquotient S.toRepresentation ((jacU e π).comp (midHom k l n N)) :=
    IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun g => rfl⟩ Subtype.val_injective
  have h3 := h1.trans h2
  refine ⟨⟨R.toSubmodule, R.toRepresentation, h3.isSmooth hsm, hRi⟩, h3,
    ⟨R.toSubmodule.subtype, fun g => rfl⟩, fun h0 => ?_⟩
  have hsub : Subsingleton R.toSubmodule := ⟨fun a b => by
    have ha := congrArg (fun G : R.toRepresentation.IntertwiningMap η => G a) h0
    have hb := congrArg (fun G : R.toRepresentation.IntertwiningMap η => G b) h0
    exact Subtype.ext ((ha.trans hb.symm : (a : Y) = b))⟩
  haveI : IsSimpleOrder (Subrepresentation R.toRepresentation) := hRi
  apply (bot_ne_top : (⊥ : Subrepresentation R.toRepresentation) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim _ _

end GlobalTheory.MidIrr

end
