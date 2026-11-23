import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
import Formalism.LocalToGlobal.GaloisLevelStructure.Checks

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def finTypSetoid (Occ : Set (NG.FinTyp L n)) : Setoid Occ where
  r π π' := π.1.Iso π'.1
  iseqv := ⟨fun π => NG.IsoRep.refl _, fun {π _} h => NG.IsoRep.symm π.1.stable h, fun h h' => NG.IsoRep.trans h h'⟩

abbrev FinTypCls (Occ : Set (NG.FinTyp L n)) : Type := Quotient (finTypSetoid Occ)

def finTypRep (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : NG.FinTyp L n := (Quotient.out c).1

theorem finTypRep_mem (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : finTypRep Occ c ∈ Occ := (Quotient.out c).2

theorem finTypRep_inj {Occ : Set (NG.FinTyp L n)} {c c' : FinTypCls Occ}
    (h : (finTypRep Occ c).Iso (finTypRep Occ c')) : c = c' := by
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound h

theorem finTypRep_mk_iso {Occ : Set (NG.FinTyp L n)} (π : Occ) :
    (finTypRep Occ (Quotient.mk (finTypSetoid Occ) π)).Iso π.1 :=
  Quotient.mk_out (s := finTypSetoid Occ) π

def constSp (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Submodule ℂ (GAf L n → ℂ) :=
  Submodule.span ℂ {fun _ => (1 : ℂ)}

theorem mem_constSp {f : GAf L n → ℂ} : f ∈ constSp L n ↔ ∃ a : ℂ, f = fun _ => a := by
  rw [constSp, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by funext x; simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, by funext x; simp⟩

def finTypConst (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : NG.FinTyp L n where
  S := constSp L n
  stable h f hf := by
    obtain ⟨a, rfl⟩ := mem_constSp.mp hf
    exact mem_constSp.mpr ⟨a, rfl⟩
  smooth f hf := by
    obtain ⟨a, rfl⟩ := mem_constSp.mp hf
    exact ⟨1, one_pos, fun _ _ => rfl⟩
  ne := by
    intro h
    have h1 : (fun _ => (1 : ℂ)) ∈ constSp L n := Submodule.subset_span rfl
    rw [h, Submodule.mem_bot] at h1
    have := congrFun h1 1
    simp at this
  irr S' hle _ := by
    by_cases hb : S' = ⊥
    · exact Or.inl hb
    · right
      obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
      obtain ⟨a, rfl⟩ := mem_constSp.mp (hle hf)
      have ha : a ≠ 0 := by
        rintro rfl
        exact hf0 rfl
      refine le_antisymm hle ?_
      rw [constSp, Submodule.span_le, Set.singleton_subset_iff]
      have e : (fun _ => (1 : ℂ)) = a⁻¹ • (fun _ : GAf L n => a) := by
        funext x
        simp [ha]
      rw [SetLike.mem_coe, e]
      exact S'.smul_mem _ hf

end Gen

end Formalism.L2.Col
