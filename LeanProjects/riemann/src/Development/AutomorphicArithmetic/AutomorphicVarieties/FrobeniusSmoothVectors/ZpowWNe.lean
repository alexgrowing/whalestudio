import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FlagLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  have h2 : a ≠ a⁻¹ := by
    intro h
    apply ha
    rw [sq]
    nth_rewrite 2 [h]
    simp
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals first | exact h1 | exact Ne.symm h1 | exact h2 | exact Ne.symm h2
  · fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals first | exact h1 | exact Ne.symm h1 | exact h2 | exact Ne.symm h2

theorem UpperTheory.V.Fr.flag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : S.A →+* C) (v : F.V), UpperTheory.V.W.HasFlag ((S.u.map f).r.comp (F.loc0 v)).toHomUnits ((S.u.map f).ψ v) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ f v
  obtain ⟨g, hg⟩ := hF.f3 v
  obtain ⟨hB, hm⟩ := co_B hF hn S
  refine flag_loc _ _ g (fun i j hij => ?_) ?_ (fun s => (S.u.map f).ord v s)
  · have hu : IsUnit (S.ψB v i g - S.ψB v j g) := by
      by_contra hu
      have h1 : S.ψB v i g - S.ψB v j g ∈ S.mB := by
        rw [← hm]
        exact hu
      have h2 : (S.ρ.ψ v i g : S.R) - S.ρ.ψ v j g ∈ maximalIdeal S.R := h1
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      have h4 : ∀ i, res O S.R (S.ρ.ψ v i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
        fun i => S.lift.2.1.2 v i g
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne hn _ hg i j hij (Units.ext h3)
    have h5 := (hu.map S.inc).map f
    rw [map_sub, map_sub] at h5
    exact h5
  · have h := congrArg (Polynomial.map ((residue C).comp f)) (o1 hF hn S v g)
    rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact h
