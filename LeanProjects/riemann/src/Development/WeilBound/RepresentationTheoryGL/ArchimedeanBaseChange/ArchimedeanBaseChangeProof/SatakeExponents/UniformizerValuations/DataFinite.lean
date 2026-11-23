import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.One

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def RunOut (π : Submodule ℂ (UA E n → ℂ)) (S T : Finset (HeightOneSpectrum (𝓞 E))) (D : Pre E n) : Prop :=
  Base π D ∧ (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧ ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w

def RunOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S T : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ D : Pre E n, RunOut π S T D

def Pre.Agree (D D' : Pre E n) : Prop :=
  (∃ e : Fin D.c ≃ Fin D'.c, ∀ i w, D.cls i w = D'.cls (e i) w) ∧ ∀ τ, ∑ i, D.m i τ = ∑ i, D'.m i τ

def DataFinite : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (k : ℕ) (L : Fin k → Pre E n), ∀ (T : Finset (HeightOneSpectrum (𝓞 E))) (D : Pre E n), RunOut π S T D →
      ∃ j, D.Agree (L j)

def RunAgree : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ))
  (S T : Finset (HeightOneSpectrum (𝓞 E))) (D D' : Pre E n), D.Agree D' → RunOut π S T D → RunOut π S T D'

theorem runFin_of (h1 : RunOne) (h2 : DataFinite) (h3 : RunAgree) : RunFin := by
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨k, L, hL⟩ := h2 E hE n hn π hπ S hS
  classical

  let good : Fin k → Prop := fun j => ∃ T D, RunOut π S T D ∧ D.Agree (L j)
  have hg : ∀ j, good j → RunOut π S ∅ (L j) := fun j ⟨T, D, hD, hA⟩ =>
    let h := h3 E n π S T D (L j) hA hD
    ⟨h.1, h.2.1, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  let idx := {j : Fin k // good j}
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin idx
  refine ⟨m, fun i => L (e.symm i).1, fun i => ⟨(hg _ (e.symm i).2).1, (hg _ (e.symm i).2).2.1⟩, fun T => ?_⟩
  obtain ⟨D, hD⟩ := h1 E hE n hn π hπ S T hS
  obtain ⟨j, hj⟩ := hL T D hD
  refine ⟨e ⟨j, T, D, hD, hj⟩, ?_⟩
  show ∀ w ∈ T, IsUnramU π w → ¬IsSplitAt w → InertAt π (L (e.symm (e ⟨j, T, D, hD, hj⟩)).1) w
  rw [Equiv.symm_apply_apply]
  exact (h3 E n π S T D (L j) hj hD).2.2

end PositivityTheory.Rg.BcB.F

end
