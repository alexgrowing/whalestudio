import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust

noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin.SpecProj

theorem le_iSup_of_dichotomy {V ι : Type} [AddCommGroup V] [Module ℂ V] (T : ι → Submodule ℂ V) (A B : Submodule ℂ V)
    (hd : Disjoint A B) (ht : ⨆ P, T P = ⊤) (h : ∀ P, T P ≤ A ∨ T P ≤ B) : A ≤ ⨆ P ∈ {P | T P ≤ A}, T P := by
  intro x hx
  have hle : (⊤ : Submodule ℂ V) ≤ (⨆ P ∈ {P | T P ≤ A}, T P) ⊔ B := by
    rw [← ht]
    refine iSup_le fun P => (h P).elim (fun hP => le_sup_of_le_left ?_) le_sup_of_le_right
    exact le_biSup T (show P ∈ {P | T P ≤ A} from hP)
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle (Submodule.mem_top (x := x)))
  have ha' : a ∈ A := (iSup₂_le fun P hP => hP : (⨆ P ∈ {P | T P ≤ A}, T P) ≤ A) ha
  have hb0 : b = 0 := Submodule.disjoint_def.1 hd b (by rw [← add_sub_cancel_left a b, e]; exact A.sub_mem hx ha') hb
  rw [← e, hb0, add_zero]; exact ha

theorem specPr_of_zSpec_typeTie : ∀ (D : D7) (i : D.nd.Loc), ZSpec D i → TypeTie D i → SpecPr D i := by
  intro D i hZ hT
  have hd := (Idx.Z0 D (D.nd.mu i) (D.nd.j i)).orthogonal_disjoint
  have mono : ∀ {Y Y' : Set (D.nd.X i)}, Y ⊆ Y' → D.nd.eigSum i Y ≤ D.nd.eigSum i Y' := fun h => biSup_mono h
  constructor
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd (D.naut.typeV_top i) (fun P => (hZ P).1) hy))
    rintro x ⟨P, hP, hx⟩
    by_contra hn
    exact D.naut.typeV_ne i P (hd hP (((hZ P).2 x hx).2 hn) |> le_bot_iff.1)
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd.symm (D.naut.typeV_top i) (fun P => (hZ P).1.symm) hy))
    rintro x ⟨P, hP, hx⟩ hn
    exact D.naut.typeV_ne i P (hd (((hZ P).2 x hx).1 hn) hP |> le_bot_iff.1)

end GlobalTheory.EtaJoin.SpecProj
