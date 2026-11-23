import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.S

open Formalism.MainNotions

variable {eps : ℝ}

def sC' (Fm : FamP eps) : ℝ := Fm.CkLow

def sCl (Fm : FamP eps) : ℝ :=
  min Fm.CfL (min Fm.Cw (min Fm.CDel (min Fm.CCount (min Fm.Ch0r Fm.Cgap))))

def sCg (Fm : FamP eps) : ℝ := Fm.CYL + 1

def sCb : ℝ := 1 / 4

def sCu : ℝ := 3

def scT : ℝ := 1 / 2

def sCT (Fm : FamP eps) : ℝ := Fm.CTu

def OwnEv (Fm : FamP eps) (P : ℝ → ℝ → ∀ x, Fm.Ix x → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P (sC' Fm) (sCl Fm) x i

theorem OwnEv.mono {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (h : ∀ C' Cl x i, P C' Cl x i → Q C' Cl x i) (hP : OwnEv Fm P) : OwnEv Fm Q := by
  obtain ⟨x0, hx⟩ := hP
  exact ⟨x0, fun x hx' i => h _ _ _ _ (hx x hx' i)⟩

theorem OwnEv.and {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (hP : OwnEv Fm P) (hQ : OwnEv Fm Q) : OwnEv Fm (fun C' Cl x i => P C' Cl x i ∧ Q C' Cl x i) := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun x hx i => ⟨ha x (le_of_max_le_left hx) i, hb x (le_of_max_le_right hx) i⟩⟩

def LargeEv (Fm : FamP eps) (P : ℝ → ℝ → ∀ x, Fm.Ix x → Prop) : Prop :=
  ∃ C'₀ Cl₀ x0 : ℝ, ∀ C' ≥ C'₀, ∀ Cl ≥ Cl₀, ∀ x ≥ x0, ∀ i : Fm.Ix x, P C' Cl x i

theorem LargeEv.mono {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (h : ∀ C' Cl x i, P C' Cl x i → Q C' Cl x i) (hP : LargeEv Fm P) : LargeEv Fm Q := by
  obtain ⟨a, b, c, hx⟩ := hP
  exact ⟨a, b, c, fun C' hC Cl hCl x hx' i => h _ _ _ _ (hx C' hC Cl hCl x hx' i)⟩

theorem LargeEv.and {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (hP : LargeEv Fm P) (hQ : LargeEv Fm Q) : LargeEv Fm (fun C' Cl x i => P C' Cl x i ∧ Q C' Cl x i) := by
  obtain ⟨a, b, c, ha⟩ := hP
  obtain ⟨a', b', c', hb⟩ := hQ
  refine ⟨max a a', max b b', max c c', fun C' hC Cl hCl x hx i => ⟨?_, ?_⟩⟩
  · exact ha C' (le_of_max_le_left hC) Cl (le_of_max_le_left hCl) x (le_of_max_le_left hx) i
  · exact hb C' (le_of_max_le_right hC) Cl (le_of_max_le_right hCl) x (le_of_max_le_right hx) i

theorem le_sC'_sCl {Fm : FamP eps} {K : TransportedAlt} {CH : ℝ} (h : Fm.Large K CH) :
    K.last (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm ∧ K.last (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm := by
  have H := h.2.2.2
  refine ⟨H _ (by simp [sC', FamP.cLast]), ?_⟩
  simp only [sCl, le_min_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact H _ (by simp [FamP.cLast])

end Formalism.MainNotions.S
