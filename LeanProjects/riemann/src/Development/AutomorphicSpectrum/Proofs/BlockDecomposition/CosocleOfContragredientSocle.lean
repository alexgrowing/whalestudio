import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CosocleContra

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isIrreducible_quot_of_isCoatom {L : Subrepresentation π} (hL : IsCoatom L) :
    (ProjLine.quot L).IsIrreducible := by
  have h1 : L.toSubmodule ≠ ⊤ := fun e => hL.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (ProjLine.quot L)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π :=
    ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hLT : L ≤ T' := fun v hv => by
    have h0 : L.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
    show L.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [h0]
    exact zero_mem _
  rcases eq_or_lt_of_le hLT with e | e
  · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := hy
    rw [← e] at hv
    exact (Submodule.Quotient.mk_eq_zero _).2 hv
  · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := (hL.2 _ e) ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    exact hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullContra (S : Subrepresentation π) : (contra (ProjLine.quot S)).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show (ProjLine.quot S).dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v =>
          LinearMap.congr_fun (show (ProjLine.quot S).dual g l.1 = l.1 from hg) (S.toSubmodule.mkQ v))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem pullContra_injective (S : Subrepresentation π) : Function.Injective (pullContra S) := fun a b h =>
  Subtype.ext (LinearMap.ext fun y => by
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem pullContra_apply_eq_zero (S : Subrepresentation π) (l : smoothPart (ProjLine.quot S).dual) {v : V}
    (hv : v ∈ S) : (pullContra S l).1 v = 0 := by
  have h0 : S.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
  show l.1 (S.toSubmodule.mkQ v) = 0
  rw [h0, map_zero]

theorem eq_of_isCoatom_of_mem_range {S S' : Subrepresentation π} (hS : IsCoatom S) (hS' : IsCoatom S')
    {w : smoothPart π.dual} (hw : w ≠ 0) (h : w ∈ (pullContra S).range) (h' : w ∈ (pullContra S').range) :
    S = S' := by
  by_contra hne
  have top := hS.sup_eq_top_of_ne hS' hne
  obtain ⟨l, rfl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  refine hw (Subtype.ext (LinearMap.ext fun v => ?_))
  have hv : v ∈ (S ⊔ S').toSubmodule := by
    rw [top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have h1 := pullContra_apply_eq_zero S l ha
  have h2 := pullContra_apply_eq_zero S' l' hb
  have h3 : (pullContra S l).1 b = 0 := (congrArg (fun y : smoothPart π.dual => y.1 b) hl').symm.trans h2
  show (pullContra S l).1 (a + b) = 0
  rw [map_add, h1, h3, add_zero]

end General

theorem isCosocle_of_isSocle_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  intro k _ _ _ _ hA N V _ _ π hπ hfl τ' hτ
  obtain ⟨hi, f, hf, hat⟩ := hτ
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k N
  have hat0 : IsAtom f.range := isAtom_range hi f hf
  have hsm : ∀ S : Subrepresentation π, IsSmooth (ProjLine.quot S) := fun S =>
    (IsSubquotient.of_surjective (ProjLine.quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, IsCoatom S → (pullContra S).range = f.range := fun S hS => by
    have hirr := isIrreducible_quot_of_isCoatom hS
    exact hat _ (isAtom_range (GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (hsm S) hirr) hirr) _
      (pullContra_injective S))
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    refine hat0.1 (eq_bot_iff.2 ?_)
    rintro _ ⟨x, rfl⟩
    exact (h x).symm ▸ zero_mem (⊥ : Subrepresentation (contra π)).toSubmodule
  haveI : WellFoundedGT (Subrepresentation π) := ((hasFiniteLength_iff_wellFounded π).1 hfl).1
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := fun e => hx (Subtype.ext (LinearMap.ext fun v => by
    have hv : v ∈ (⊥ : Subrepresentation π) := e ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
    rw [hv0, map_zero]
    rfl))
  obtain ⟨L, hL, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation π)).resolve_left hbt
  have huniq : ∀ S : Subrepresentation π, IsCoatom S → S = L := fun S hS =>
    eq_of_isCoatom_of_mem_range hS hL hx ((key S hS).symm ▸ ⟨x, rfl⟩) ((key L hL).symm ▸ ⟨x, rfl⟩)
  have hall : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤ := fun S => by
    rcases eq_top_or_exists_le_coatom S with h | ⟨M, hM, hSM⟩
    · exact Or.inr h
    · exact Or.inl (huniq M hM ▸ hSM)
  have hc := ProjLine.isCosocle_quot hL.1 hall
  exact ⟨⟨_, ProjLine.quot L, hsm L, hc.1⟩, hc⟩

end GlobalTheory.CompanionTheory.CosocleContra

end
