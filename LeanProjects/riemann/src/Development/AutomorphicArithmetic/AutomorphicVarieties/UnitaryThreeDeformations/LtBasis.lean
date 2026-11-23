import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriCanon

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem lb_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((t : O) - 1) := by
    have : (t : O) ^ 2 - 1 = ((t : O) - 1) * ((t : O) + 1) := by ring
    rw [this] at ht
    exact isUnit_of_mul_isUnit_left ht
  have hi : ((t⁻¹ : Oˣ) : O) * (t : O) = 1 := by simp
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have : (t : O) - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) ^ 2 - 1) := by
      linear_combination (-(t : O)) * hi
    rw [this]
    exact (Units.isUnit _).mul ht
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have : 1 - ((t⁻¹ : Oˣ) : O) = ((t⁻¹ : Oˣ) : O) * ((t : O) - 1) := by
      linear_combination (-1 : O) * hi
    rw [this]
    exact (Units.isUnit _).mul h1
  fin_cases a <;> fin_cases b <;> simp [wt1] at hab ⊢
  all_goals first
    | exact h1 | exact h2 | exact h3
    | exact (by simpa [neg_sub] using h1.neg)
    | exact (by simpa [neg_sub] using h2.neg)
    | exact (by simpa [neg_sub] using h3.neg)

theorem UpperTheory.V.UnitaryThreeInertia.lt_basis :
    ∀ {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] [IsCO O R'] [Group D]
      (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R'), Function.Surjective p →
      ∀ (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r' : D →* GG 3 R') (x : D), Red η Ψ r' → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → CondT η Ψ I r' →
      (∃ X, GrMat 𝒜 X ∧ X.map p = (r' x).mat) →
      ∃ h : GL (Fin 3) R, InHat h ∧ GrMat 𝒜 h.val ∧ InHat (GeneralLinearGroup.map (p : R →+* R') h) ∧ TriIn η Ψ I r' (GeneralLinearGroup.map (p : R →+* R') h) := by
  intro O R R' D _ _ _ _ _ _ _ _ _ _ 𝒜 _ p hp η Ψ I r' x hr hx hΨ hc hex
  obtain ⟨X, hX, hXp⟩ := hex
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hm : ∀ y : R, p y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
    intro y
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (isUnit_map_iff (p : R →+* R') y)
  have hd : (r0 η Ψ x).mat = diagonal fun i => (((Ψ x) ^ wt1 i : Oˣ) : O) := by
    unfold GG.mat
    rw [unitaryThreeReflection_left, tor_val]
  have hred := hr.red x
  rw [hd] at hred
  have hent : ∀ a b : Fin 3, p (X a b) = (r' x).mat a b := by
    intro a b
    rw [← hXp]
    rfl
  have hoff : ∀ a b : Fin 3, a ≠ b → X a b ∈ maximalIdeal R := by
    intro a b hab
    rw [← hm, hent]
    have := hred a b
    simpa [Matrix.map_apply, Matrix.diagonal_apply_ne _ hab] using this
  have hdiff : ∀ a b : Fin 3, a ≠ b → IsUnit (X a a - X b b) := by
    intro a b hab
    by_contra hn
    have h1 : X a a - X b b ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hn
    rw [← hm, map_sub, hent, hent] at h1
    have ha := hred a a
    have hb := hred b b
    simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply_eq] at ha hb
    have hu : IsUnit (algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O))) :=
      (lb_unit (Ψ x) hΨ a b hab).map _
    apply (IsLocalRing.mem_maximalIdeal _).mp _ hu
    have : algebraMap O R' ((((Ψ x) ^ wt1 a : Oˣ) : O) - (((Ψ x) ^ wt1 b : Oˣ) : O)) =
        ((r' x).mat a a - (r' x).mat b b) - ((r' x).mat a a - algebraMap O R' (((Ψ x) ^ wt1 a : Oˣ) : O))
          + ((r' x).mat b b - algebraMap O R' (((Ψ x) ^ wt1 b : Oˣ) : O)) := by
      rw [map_sub]
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h1 ha) hb
  obtain ⟨h, hh⟩ := exists_canon X hdiff hoff
  have hg := canon_graded 𝒜 X h hdiff hX hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  have hXp' : X.map (p : R →+* R') = (r' x).mat := hXp
  rw [hXp'] at hh'
  exact ⟨h, hh.hat, hg.1, hh'.hat, (cond_iff_canon η Ψ I r' x _ hr hx hΨ hh').1.1 hc⟩
