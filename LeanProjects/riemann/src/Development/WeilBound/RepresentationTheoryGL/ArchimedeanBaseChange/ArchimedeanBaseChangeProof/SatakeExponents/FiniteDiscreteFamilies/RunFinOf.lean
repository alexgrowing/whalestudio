import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def PreEquiv (D D' : Pre E n) : Prop :=
  ∃ e : Fin D.c ≃ Fin D'.c, (∀ i w, D.cls i w = D'.cls (e i) w) ∧ ∀ i τ, D.m i τ = D'.m (e i) τ

def IsLevel (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E))) : Prop :=
  (∀ w, IsOpen (K w : Set (GL (Fin n) (w.adicCompletion E)))) ∧ ∀ᶠ w in Filter.cofinite, GlobalTheory.LFun.KGL w n ≤ K w

def HasKType {N : ℕ} (W : Submodule ℂ (Kinf E N → ℂ)) (V : Submodule ℂ (Sm E N)) : Prop :=
  ∃ φ ∈ V, φ ≠ 0 ∧ ∀ g, (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W

def FinFam : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
  (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
  (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)) (m : (E →+* ℂ) → Multiset ℂ),
  IsLevel K → (∀ N, FiniteDimensional ℂ (W N)) → ∃ (k : ℕ) (D : Fin k → Pre E n), ∀ D' : Pre E n,
    (∀ τ, ∑ i, D'.m i τ = m τ) → (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D'.h w (D'.σ · w)) (K w)) →
    (∀ i, HasKType (W (D'.N i)) (D'.V i)) → ∃ j, PreEquiv (D j) D'

def RunT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S.card ≤ 1 →
    ∃ (K : ∀ w : HeightOneSpectrum (𝓞 E), Subgroup (GL (Fin n) (w.adicCompletion E)))
      (W : ∀ N : ℕ, Submodule ℂ (Kinf E N → ℂ)), IsLevel K ∧ (∀ N, FiniteDimensional ℂ (W N)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∃ D : Pre E n, Base π D ∧ (∀ w ∈ S, IsSplitAt w → D.SplitAt π w) ∧
        (∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → InertAt π D w) ∧
        (∀ w, GlobalTheory.LGrp.IsSpherical (locProd D.h w (D.σ · w)) (K w)) ∧ ∀ i, HasKType (W (D.N i)) (D.V i)

theorem runFin_of (hR : RunT) (hF : FinFam) (hW : WeightEx) (hQ : PermSat) : RunFin := by
  classical
  intro E _ _ _ hE n hn π hπ S hS
  obtain ⟨K, W, hK, hW', hT⟩ := hR E hE n hn π hπ S hS
  choose lam hlam using hW E n π hπ
  obtain ⟨k, D, hD⟩ := hF E n K W (fun τ => infOfWeight (lam τ)) hK hW'
  choose DT hDT using hT
  have hj : ∀ T, ∃ j, PreEquiv (D j) (DT T) := fun T =>
    hD (DT T) (fun τ => (hDT T).1.1 τ (lam τ) (hlam τ)) (hDT T).2.2.2.1 (hDT T).2.2.2.2
  let T' : Fin k → Finset (HeightOneSpectrum (𝓞 E)) := fun j =>
    if h : ∃ T, PreEquiv (D j) (DT T) then h.choose else ∅
  refine ⟨k, fun j => DT (T' j), fun j => ⟨(hDT _).1, (hDT _).2.1⟩, fun T => ?_⟩
  obtain ⟨j, hjT⟩ := hj T
  have h : ∃ T, PreEquiv (D j) (DT T) := ⟨T, hjT⟩
  obtain ⟨e1, h1, -⟩ := hjT
  obtain ⟨e2, h2, -⟩ : PreEquiv (D j) (DT (T' j)) := by
    simp only [T', dif_pos h]
    exact h.choose_spec
  refine ⟨j, fun w hw hu hs => ?_⟩
  obtain ⟨B, hB, hα⟩ := (hDT T).2.2.1 w hw hu hs
  refine ⟨B, hQ E n (DT T) (DT (T' j)) (e1.symm.trans e2) w (fun i => ?_) B hB, hα⟩
  have := h1 (e1.symm i) w
  rw [Equiv.apply_symm_apply] at this
  rw [← this, Equiv.trans_apply, h2]

end PositivityTheory.Rg.BcB.F.F5

end
