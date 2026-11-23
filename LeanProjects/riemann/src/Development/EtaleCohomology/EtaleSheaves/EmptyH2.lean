import Development.EtaleCohomology.EtaleSheaves.InjStepPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.EmptyH₂

theorem sec_subsingleton {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] :
    Subsingleton (Sec F Y) := by
  have hT := Sheaf.isTerminalOfBotCover F Y (Scheme.bot_mem_grothendieckTopology (P := @Etale) Y)
  exact (ModuleCat.isZero_iff_subsingleton).1 hT.isZero

theorem h_empty (hH : Hyp) {R : Type} [CommRing R] (F : Shv R) (Y : Scheme.{0}) [IsEmpty Y] (n : ℤ)
    (x : H R (sch.obj Y) F n) : x = 0 := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (hH.a9 R F).1 (sch.obj Y) n hn
    exact Subsingleton.elim _ _
  · obtain ⟨e, -, -⟩ := (hH.a9 R F).2
    have := sec_subsingleton F Y
    rw [← (e Y).apply_symm_apply x, Subsingleton.elim ((e Y).symm x) 0, map_zero]
  · obtain ⟨Z, f, -, -, hf⟩ := hH.a5 R Y F n hn x
    have : IsIso (sch.map f) := inferInstance
    have h1 : pull R (inv (sch.map f) ≫ sch.map f) F n x = 0 := by rw [pull_comp, hf, map_zero]
    simpa [pull_id] using h1

theorem EmptyH_of : LateralTheory.E.InjStepPf.EmptyH := by
  intro hH q X S p U hU i n x
  have : IsEmpty U := ⟨fun u => by
    have h : (u.1 : S) ∈ (U : Set S) := u.2
    rw [hU] at h; exact h⟩
  have : IsEmpty (overO p U) := ⟨fun z => isEmptyElim ((pullback.snd p U.ι).base z)⟩
  exact h_empty hH _ _ n x

end LateralTheory.E.EmptyH₂
