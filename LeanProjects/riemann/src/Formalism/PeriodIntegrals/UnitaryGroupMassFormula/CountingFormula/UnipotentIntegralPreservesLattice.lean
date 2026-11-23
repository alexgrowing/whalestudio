import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFDefs

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def fr (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Fin (D.R.rS + 1) → (VS D).V :=
  Fin.snoc (α := fun _ => (VS D).V) x.1 x.2

def act (D : Formalism.BasicNotions.D7) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    (Fin D.R.rS → (VS D).V) × (VS D).V :=
  (fun a => n (x.1 a), n x.2)

def Good (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Prop :=
  (∀ b, fr D x b ∈ Λ) ∧ (∀ a b, brS (VS D) (fr D x b) (F0.fvec a) = Z a b) ∧
  (∀ a b, (VS D).hT (fr D x a) (fr D x b) =
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T' else 0)

def pW (D : Formalism.BasicNotions.D7) (v : (VS D).V) : (VS D).V :=
  v - ∑ a, (VS D).hT (D.sp.hypF a) v • D.sp.hypE a - ∑ a, (VS D).hT (D.sp.hypE a) v • D.sp.hypF a
    + ((VS D).hT D.sp.zm v / (D.sp.T : D.host.E)) • D.sp.zm

def pWf (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : Fin (D.R.rS + 1) → (VS D).V :=
  fun b => pW D (fr D x b)

def alM (D : Formalism.BasicNotions.D7) (x : (Fin D.R.rS → (VS D).V) × (VS D).V) :
    Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E :=
  fun a b => (VS D).hT (D.sp.hypF a) (fr D x b)

def betaZ (D : Formalism.BasicNotions.D7) (Z : MatZ D) : Matrix (Fin D.R.rS) (Fin (D.R.rS + 1)) D.host.E :=
  Z.submatrix Fin.castSucc id

def RankG : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D), GZ T T' Z ≠ 0 →
    ∃ R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E, betaZ D Z * R = 1

def FixedOK (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Prop :=
  Submodule.IsLattice D.host.E Λ ∧ Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ ∧ F0.e = D.sp.hypE ∧ (∀ a, F0.e a ∈ Λ) ∧
    ∃ c : D.host.E, c ≠ 0 ∧ F0.z = c • D.sp.zm

def GoodEZ : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D), ∀ F' ∈ EZ T' F0 Λ Z, Good D T' F0 Λ Z (F'.fl.e, F'.fl.z)

def Stage1 : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∃ Wf : Set (Fin (D.R.rS + 1) → (VS D).V), Wf.Finite ∧
      ∀ x, Good D T' F0 Λ Z x → ∃ n ∈ N0 F0 Λ, pWf D (act D n x) ∈ Wf

def Stage2 : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∀ Wf : Set (Fin (D.R.rS + 1) → (VS D).V), Wf.Finite →
    ∃ Af : Set (Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E), Af.Finite ∧
      ∀ x, Good D T' F0 Λ Z x → pWf D x ∈ Wf →
        ∃ n ∈ N0 F0 Λ, pWf D (act D n x) = pWf D x ∧ alM D (act D n x) * R ∈ Af

def FinK : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), FixedOK D F0 Λ → ∀ (Z : MatZ D)
    (R : Matrix (Fin (D.R.rS + 1)) (Fin D.R.rS) D.host.E), betaZ D Z * R = 1 →
    ∀ (Wf : Set (Fin (D.R.rS + 1) → (VS D).V)) (Af : Set (Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)),
      Wf.Finite → Af.Finite →
      {x | Good D T' F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af}.Finite

theorem fr_act (D : Formalism.BasicNotions.D7) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (Fin D.R.rS → (VS D).V) × (VS D).V)
    (b : Fin (D.R.rS + 1)) : fr D (act D n x) b = n (fr D x b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b <;> simp [fr, act]

theorem unipotentIntegral_fixes_flag (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    (a : Fin (D.R.rS + 1)) : n (F0.fvec a) = F0.fvec a := by
  obtain ⟨-, he, hz⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp [FlagG.fvec, he, hz]

theorem unipotentIntegral_isometry (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    (x y : (VS D).V) : (VS D).hT (n x) (n y) = (VS D).hT x y := by
  obtain ⟨hL, -, -⟩ := hn
  unfold NLam at hL
  obtain ⟨hA, -, -⟩ := hL
  unfold IsAutLam at hA
  exact hA.1 x y

theorem unipotentIntegral_preserves_lattice (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ)
    {v : (VS D).V} (hv : v ∈ Λ) : n v ∈ Λ := by
  obtain ⟨hL, -, -⟩ := hn
  obtain ⟨⟨-, hg⟩, -, -⟩ := hL
  unfold Formalism.HermitianLatticesTheory.gmap at hg
  rw [← hg]
  exact Submodule.mem_map_of_mem hv

theorem good_move (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (Z : MatZ D) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ N0 F0 Λ) :
    Good D T' F0 Λ Z (act D n x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨fun b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [fr_act]
    exact unipotentIntegral_preserves_lattice D F0 Λ hn (h1 b)
  · rw [fr_act, ← unipotentIntegral_fixes_flag D F0 Λ hn a]
    unfold brS
    rw [unipotentIntegral_isometry D F0 Λ hn]
    have h2' := h2 a b
    unfold brS at h2'
    exact h2'
  · rw [fr_act, fr_act, unipotentIntegral_isometry D F0 Λ hn]
    exact h3 a b

end PI.UnitaryGroupMassFormula.CntFormula
