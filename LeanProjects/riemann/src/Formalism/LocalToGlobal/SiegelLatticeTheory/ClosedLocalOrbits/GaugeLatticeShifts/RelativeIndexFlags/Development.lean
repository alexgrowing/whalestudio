import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.VolumeIndexRepresentationNonzero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RelativeIndexFlags.RelIndexInfRightNeZero

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def loGen (n : ℕ) (K : Type*) [Field K] : Subgroup (Matrix.GeneralLinearGroup (Fin n) K) :=
  Subgroup.closure {a | ∀ i j, (i < j → (a : Matrix (Fin n) (Fin n) K) i j = 0) ∧
    (i = j → (a : Matrix (Fin n) (Fin n) K) i j = 1)}

def UniConjIdx (n : ℕ) (K : Type*) [Field K] : Prop :=
  ∀ (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) (g : Matrix.GeneralLinearGroup (Fin n) K),
    g ∈ loGen n K → X ≤ loGen n K → X.relIndex (cj g X) ≠ 0 → (cj g X).relIndex X ≠ 0 →
      X.relIndex (cj g X) = (cj g X).relIndex X

variable (D : D7) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def VolIdxFinP : Prop :=
  ∀ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
  (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) → ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : MatR D),
    t.relevant → t.generic → NormRep t w F' L U → Formalism.MainNotions.S.Lat.Gval (lf D F0) F' ≠ 0 →
      (stabAut D u u' F0 what₂ t F' L).relIndex (stabInt D u u' δ M w) ≠ 0 ∧
      (stabInt D u u' δ M w).relIndex (stabAut D u u' F0 what₂ t F' L) ≠ 0

def StabAutConjP : Prop :=
  ∀ (t : Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L₁ U₁ L₂ U₂ : MatR D),
    NormRep t w F₁ L₁ U₁ → NormRep t w F₂ L₂ U₂ →
      ∃ g : GLR D, g ∈ loGen (D.R.rS + 1) D.host.E ∧
        stabAut D u u' F0 what₂ t F₂ L₂ = cj g (stabAut D u u' F0 what₂ t F₁ L₁)

theorem stabInt_le_loGen (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (w : Point D.host.E (D.R.rS + 1)) :
    stabInt D u u' δ M w ≤ loGen (D.R.rS + 1) D.host.E := by
  unfold stabInt loGen
  refine Subgroup.closure_mono ?_
  intro a ha
  exact ha.1

theorem volume_index_representation_of_finite (hC : StabAutConjP D u u' F0 what₂) (hFin : VolIdxFinP D u u' F0 what₂)
    (hU : UniConjIdx (D.R.rS + 1) D.host.E) : Formalism.L2.SG.Pf.RelativeIndexFlags.VolumeIndexRepresentationNonzero D u u' F0 what₂ := by
  intro δ M hAg t w F₁ F₂ L₁ U₁ L₂ U₂ hrel hgen h1 hG1 h2 hG2
  obtain ⟨g, hg, he⟩ := hC t w F₁ F₂ L₁ U₁ L₂ U₂ h1 h2
  obtain ⟨a1, a2⟩ := hFin δ M hAg t w F₁ L₁ U₁ hrel hgen h1 hG1
  obtain ⟨b1, b2⟩ := hFin δ M hAg t w F₂ L₂ U₂ hrel hgen h2 hG2
  rw [he] at b1 b2
  change ratio (stabAut D u u' F0 what₂ t F₁ L₁) (stabInt D u u' δ M w) =
    ratio (stabAut D u u' F0 what₂ t F₂ L₂) (stabInt D u u' δ M w)
  rw [he]
  symm
  exact ratio_cj_of _ _ g a1 a2 b1 b2
    (hU _ g hg (stabInt_le_loGen D u u' δ M w))

end Formalism.L2.SG.Pf.RelativeIndexFlags
