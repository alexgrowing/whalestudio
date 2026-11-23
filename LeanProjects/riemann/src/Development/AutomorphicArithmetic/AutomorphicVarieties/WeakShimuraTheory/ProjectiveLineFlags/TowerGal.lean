import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem mul_eq_one_of_card_eq_two_of_ne_one {H : Type*} [Group H] (hH : Nat.card H = 2)
    (x y : H) (hx : x ≠ 1) (hy : y ≠ 1) : x * y = 1 := by
  classical
  haveI : Finite H := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card] at hH
  by_contra hxy
  have h3 : ({1, x, x * y} : Finset H).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨1, x, x * y, fun h => hx h.symm, fun h => hxy h.symm, ?_, rfl⟩
    intro h
    exact hy (mul_left_cancel (a := x) (by rw [mul_one]; exact h.symm))
  have := Finset.card_le_univ ({1, x, x * y} : Finset H)
  omega

set_option maxHeartbeats 400000 in
theorem UpperTheory.V.Ws.P1.towerGal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), (resLe T.F_le).range = T.GalL ∧ Function.Injective (resLe T.F_le) ∧ Continuous (resLe T.F_le) ∧
          (∀ a b : G T.F Ω, a ∉ T.GalL → b ∉ T.GalL → a * b ∈ T.GalL) ∧
          (∀ g : G T.L Ω, resQ T.F (resLe T.F_le g) = resQ T.L g ∧ cycZ T.F Ω l (resLe T.F_le g) = cycZ T.L Ω l g ∧ cycZ ℚ Ω l (resQ T.L g) = cycZ T.L Ω l g) ∧
          ∀ (A : ValuationSubring Ω) (g : G T.L Ω), (resLe T.F_le g ∈ Dec (F := T.F) A ↔ g ∈ Dec (F := T.L) A) ∧ (resLe T.F_le g ∈ Ine (F := T.F) A ↔ g ∈ Ine (F := T.L) A) := by
  intro Ω _ _ _ l _ c D T
  have hKL : T.K ≤ T.L := by
    rw [T.hL]
    exact le_sup_right
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold UpperTheory.V.Ws.Tower.GalL
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact g.commutes ⟨x, hKL hx⟩
    · intro a ha
      rw [Subgroup.mem_comap] at ha
      have hF : resQ T.F a ∈ T.F.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact a.commutes ⟨x, hx⟩
      have hL : resQ T.F a ∈ T.L.fixingSubgroup := by
        rw [T.hL, IntermediateField.fixingSubgroup_sup]
        exact ⟨hF, ha⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hL
      exact ⟨{ a.toRingEquiv with commutes' := fun x => hL x x.2 }, by ext z; rfl⟩
  · intro g₁ g₂ h
    ext z
    exact congrArg (fun k => k z) h
  · letI : Algebra T.F T.L := (IntermediateField.inclusion T.F_le).toRingHom.toAlgebra
    haveI : IsScalarTower T.F T.L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have he : (resLe T.F_le : G T.L Ω → G T.F Ω) = AlgEquiv.restrictScalarsHom T.F := by
      funext g
      ext
      rfl
    rw [he]
    exact UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _
  · unfold UpperTheory.V.Ws.Tower.GalL
    haveI : Algebra.IsQuadraticExtension ℚ T.K := ⟨T.degK⟩
    haveI hN : Normal ℚ T.K := Algebra.IsQuadraticExtension.normal ℚ T.K
    haveI : IsGalois ℚ T.K := {}
    have hcard : Nat.card (T.K ≃ₐ[ℚ] T.K) = 2 := by
      rw [IsGalois.card_aut_eq_finrank, T.degK]
    have hker := @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ T.K
      (by convert hN; exact Subsingleton.elim _ _)
    intro a b ha hb
    rw [Subgroup.mem_comap, ← hker, MonoidHom.mem_ker] at ha hb ⊢
    rw [map_mul, map_mul]
    exact mul_eq_one_of_card_eq_two_of_ne_one (by convert hcard <;> first | rfl | exact Subsingleton.elim _ _) _ _ ha hb
  · intro g
    exact ⟨by ext; rfl, rfl, rfl⟩
  · intro A g
    exact ⟨Iff.rfl, Iff.rfl⟩
