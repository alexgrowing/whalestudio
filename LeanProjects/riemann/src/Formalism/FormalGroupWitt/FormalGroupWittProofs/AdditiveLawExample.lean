import Formalism.FormalGroupWitt.Statement

noncomputable section

namespace Formalism.FG.FormalGroupSubstitution

open MvPowerSeries

theorem subst_X_add_X {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p q : σ) :
    subst a (X p + X q : MvPowerSeries σ R) = a p + a q := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  rw [subst_add ha, subst_X ha, subst_X ha]

theorem subst_X' {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p : σ) :
    subst a (X p : MvPowerSeries σ R) = a p :=
  subst_X (hasSubst_of_constantCoeff_zero h) p

theorem atXv_X (j : Fin 2) :
    Formalism.FG.atXv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vX j := by
  unfold Formalism.FG.atXv
  exact subst_X' _ (fun s => by simp) j

theorem atYv_X (j : Fin 2) :
    Formalism.FG.atYv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vY j := by
  unfold Formalism.FG.atYv
  exact subst_X' _ (fun s => by simp) j

end Formalism.FG.FormalGroupSubstitution

namespace Formalism.FG

open MvPowerSeries Formalism.FG.FormalGroupSubstitution

theorem additive_law_example : Formalism.FG.AddLawExample := by
  unfold AddLawExample
  have hF : ∀ i : Fin 2, constantCoeff
      (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ) = 0 := fun i => by simp
  refine ⟨⟨hF, ?_, ?_, ?_, ?_⟩, ?_, ⟨fun i => by simp, ?_⟩, ⟨hF, ⟨fun j => by simp, ?_⟩, ?_⟩⟩
  · intro i x
    obtain ⟨a, b⟩ := x
    fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [coeff_X, Finsupp.single_eq_single_iff]
  · intro i
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp
  · intro i
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp
  · intro i
    have hin : ∀ j : Fin 2, subst (fun y : Fin 2 × Fin 2 => (v3 (Fin.castSucc y.1) y.2 :
        MvPowerSeries (Fin 3 × Fin 2) ℤ)) (vX j + vY j : MvPowerSeries (Fin 2 × Fin 2) ℤ) =
        v3 0 j + v3 1 j := fun j => by
      rw [subst_X_add_X _ (fun s => by simp)]
      rfl
    have hin' : ∀ j : Fin 2, subst (fun y : Fin 2 × Fin 2 => (v3 y.1.succ y.2 :
        MvPowerSeries (Fin 3 × Fin 2) ℤ)) (vX j + vY j : MvPowerSeries (Fin 2 × Fin 2) ℤ) =
        v3 1 j + v3 2 j := fun j => by
      rw [subst_X_add_X _ (fun s => by simp)]
      rfl
    simp only [hin, hin']
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp),
      subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp only [show ((1 : Fin 2) = 0) = False from by decide,
      if_true, if_false]
    rw [add_assoc]
  · intro i
    rw [subst_X_add_X _ (fun s => by simp)]
    rw [show Fin.rev (0 : Fin 2) = 1 from rfl, show Fin.rev (1 : Fin 2) = 0 from rfl, add_comm]
  · intro i
    rw [subst_X' _ hF]
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp [atXv_X, atYv_X])]
    simp [atXv_X, atYv_X]
  · intro j i
    simp [coeff_X, Finsupp.single_eq_single_iff]
  · intro j
    rw [subst_X' _ hF, atXv_X, atYv_X]

theorem not_a_law_example : Formalism.FG.NotLawExample := by
  unfold NotLawExample
  intro h
  have h2 := h.2.1 0 ((1 : Fin 2), (0 : Fin 1))
  dsimp only at h2
  rw [two_mul] at h2
  simp [coeff_X, Finsupp.single_eq_single_iff] at h2

end Formalism.FG
