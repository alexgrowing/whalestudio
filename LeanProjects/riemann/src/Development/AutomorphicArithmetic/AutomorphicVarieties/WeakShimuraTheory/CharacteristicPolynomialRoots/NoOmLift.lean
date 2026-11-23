import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Pu.noOm_rt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have h3 : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g), mul_inv_cancel_right]
  have e : Φ.rt (wt i j) g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ (wt i j).1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ (wt i j).2 := rfl
  rw [e]
  apply Additive.ofMul.injective
  have h4 := congrArg Additive.ofMul h3
  fin_cases i <;> fin_cases j <;>
    simp only [wt, lamW, muW, ofMul_mul, ofMul_inv, ofMul_zpow] at h4 ⊢ <;> simp [h4] <;> abel

private theorem UpperTheory.V.Ws.Pu.noOm_lift {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) (hg : g ∈ T.GalL) : ∃ g' : G T.L Ω, resQ T.L g' = resQ T.F g := by
  have h1 : resQ T.F g ∈ T.L.fixingSubgroup := by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩, hg⟩
  have h2 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1
  exact ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => h2 x.1 x.2, rfl⟩

theorem UpperTheory.V.Ws.Pu.noOm :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h), D.Good → T.Ok → ∀ i j,
      (K.r.chib i).comp K.V.pr ≠ (K.r.chib j).comp K.V.pr * W.pushCh (residue c'.O) (chiO T.L Ω l c'.O) := by
  intro Ω _ _ _ l _ c D T c' h K hD hT i j hne
  haveI : IsLocalHom (inc h) := (UpperTheory.V.Ws.P1.coefRes c).2.2.1 c' h
  obtain ⟨g, hg, hw⟩ := hT.g2 (wt i j)
  obtain ⟨g', hg'⟩ := UpperTheory.V.Ws.Pu.noOm_lift T g hg
  apply hw
  have hχ : ∀ g, chi D T.pr 0 g * chi D T.pr 3 g = chi D T.pr 1 g * chi D T.pr 2 g := by
    intro g
    cases T.pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]
  have key : (T.fr ∅).rt (wt i j) g * chi D T.pr j (resQ T.F g) = chi D T.pr i (resQ T.F g) :=
    UpperTheory.V.Ws.Pu.noOm_rt (T.fr ∅) g (hχ _) i j
  have e0 : (K.r.chib i (K.V.pr g') : ResidueField c'.O) =
      (K.r.chib j (K.V.pr g') : ResidueField c'.O) * residue c'.O (chiO T.L Ω l c'.O g' : c'.O) :=
    congrArg (fun χ : G T.L Ω →* (ResidueField c'.O)ˣ => (χ g' : ResidueField c'.O)) hne
  have e1 : (chiO T.L Ω l c'.O g' : c'.O) = inc h (chiO ℚ Ω l c.O (resQ T.L g') : c.O) := rfl
  rw [K.chib, K.chib, e1, hg', ← key, Units.val_mul] at e0
  simp only [map_mul] at e0
  have u1 : residue c'.O (K.κ g' : c'.O) ≠ 0 := ((K.κ g').isUnit.map _).ne_zero
  have u2 : residue c'.O (inc h (chi D T.pr j (resQ T.F g) : c.O)) ≠ 0 := (((chi D T.pr j (resQ T.F g)).isUnit.map _).map _).ne_zero
  rw [mul_assoc, mul_right_inj' u1, mul_comm, mul_right_inj' u2] at e0
  rw [hD.om_bar]
  apply (ResidueField.map (inc h)).injective
  rw [ResidueField.map_residue, ResidueField.map_residue]
  exact e0
