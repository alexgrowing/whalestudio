import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d : ℕ}

lemma hasSubst_ev {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => h p.1 p.2)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [h p.1 p.2]; exact IsNilpotent.zero)

lemma ev_X {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS R m d) = a j i := by
  unfold ev
  rw [MvPowerSeries.subst_X (hasSubst_ev a h)]

lemma ev_add {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f + g) = ev a f + ev a g := by
  unfold ev
  exact MvPowerSeries.subst_add (hasSubst_ev a h) f g

lemma ev_mul {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f * g) = ev a f * ev a g := by
  unfold ev
  exact MvPowerSeries.subst_mul (hasSubst_ev a h) f g

lemma ev_C {m n : ℕ} (a : Fin m → Pt R n d) (r : R) : ev a (C r : PS R m d) = C r := by
  unfold ev MvPowerSeries.subst
  letI : UniformSpace R := ⊥
  first
  | (open MvPowerSeries.WithPiTopology in rw [MvPowerSeries.eval₂_C])
  | erw [MvPowerSeries.eval₂_C]
  all_goals first
    | rfl
    | simp [MvPowerSeries.algebraMap_apply]

def addLaw (R : Type) [CommRing R] (d : ℕ) : FGLaw R d where
  F := fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i)
  const := fun i => by simp
  unit := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    rw [ev_add _ h, ev_X _ h, ev_X _ h]
    simp [pt]
  comm := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    rw [ev_add _ h, ev_X _ h, ev_X _ h]
    simp [pt, add_comm]
  assoc := fun i => by
    have h2 : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 0, pt R d 1] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    have h2' : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 1, pt R d 2] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    have e1 : (fun l => ev ![pt R d 0, pt R d 1] (X ((0 : Fin 2), l) + X ((1 : Fin 2), l)) :
        Pt R 3 d) = fun l => X ((0 : Fin 3), l) + X ((1 : Fin 3), l) := by
      funext l; rw [ev_add _ h2, ev_X _ h2, ev_X _ h2]; simp [pt]
    have e2 : (fun l => ev ![pt R d 1, pt R d 2] (X ((0 : Fin 2), l) + X ((1 : Fin 2), l)) :
        Pt R 3 d) = fun l => X ((1 : Fin 3), l) + X ((2 : Fin 3), l) := by
      funext l; rw [ev_add _ h2', ev_X _ h2', ev_X _ h2']; simp [pt]
    rw [e1, e2]
    have h3 : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![fun l => X ((0 : Fin 3), l) +
        X ((1 : Fin 3), l), pt R d 2] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    have h3' : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![pt R d 0, fun l => X ((1 : Fin 3), l) +
        X ((2 : Fin 3), l)] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    rw [ev_add _ h3, ev_X _ h3, ev_X _ h3, ev_add _ h3', ev_X _ h3', ev_X _ h3']
    simp [pt, add_assoc]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
