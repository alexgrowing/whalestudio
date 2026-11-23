import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_id_projective_base_change (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) :
    pb l (𝟙 X) n z = z := by
  show LinearMap.baseChange ℚ_[l] (pullHl l (sch.map (𝟙 X)) n 0) z = z
  rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id, LinearMap.id_apply]

private theorem pb_comp_projective_base_change (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (v : V l C n) : pb l (f ≫ g) n v = pb l f n (pb l g n v) := by
  rw [pb_comp]; rfl

private theorem pb_iso_inj (l : ℕ) [Fact l.Prime] {A B : Scheme.{0}} (e : A ≅ B) (n : ℤ) :
    Function.Injective (pb l e.hom n) := by
  intro x y h
  have h2 := congrArg (pb l e.inv n) h
  rw [← pb_comp_projective_base_change, ← pb_comp_projective_base_change, e.inv_hom_id, pb_id_projective_base_change, pb_id_projective_base_change] at h2
  exact h2

theorem UpperTheory.Gal.KunnethLefschetz.perm_holds :
    UpperTheory.Gal.KunnethLefschetz.Perm := by
  intro l _ X r Y j w hinj g hg φ π θ hc s
  have hval : ∀ t, pb l (j t) w (pb l φ w (g (π s))) =
      pb l (θ t).hom w (pb l (j (π t)) w (g (π s))) := by
    intro t
    rw [← pb_comp_projective_base_change, hc, pb_comp_projective_base_change]
  obtain ⟨z, hz⟩ := hg.line s (pb l (θ s).hom w (pb l (j (π s)) w (g (π s))))
  refine ⟨z, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hz
    exact hg.ne (π s) (pb_iso_inj l (θ s) w (by rw [hz, map_zero]))
  · apply hinj
    funext t
    show pb l (j t) w (pb l φ w (g (π s))) = pb l (j t) w (z • g s)
    rw [hval, map_smul]
    by_cases hts : t = s
    · subst hts
      exact hz
    · rw [hg.off (π s) (π t) (fun h => hts (π.injective h).symm), map_zero,
        hg.off s t (fun h => hts h.symm), smul_zero]
