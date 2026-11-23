import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcVanOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcSpKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem xvan_of_van {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (γ : G ℚ Ω →* c.Oˣ) (γ' : G ℚ Ω →* (ResidueField c.O)ˣ)
    (h : ∀ g, Raw.bar γ g = (γ' g : ResidueField c.O)) (hv : Van D.T D.pl D.rbar.ker γ') : D.XVan γ := by
  intro z hzlc hzc hzU hzD
  obtain ⟨m, hm⟩ := hv z hzlc (fun g k => by rw [hzc, h])
    (fun A hA g hgA hgK => hzU A hA g hgA (MonoidHom.mem_ker.mp hgK))
    (fun v hvT => by
      obtain ⟨m, hm⟩ := hzD v hvT
      exact ⟨m, fun g hg => by rw [hm g hg, h]⟩)
  exact ⟨m, fun g => by rw [hm g, h]⟩

theorem UpperTheory.V.X.xvan :
    CorX → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), (∀ p ∈ D.T, p.Prime ∧ (D.pl p).valuation (p : Ω) < 1) → ∀ (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ → ∀ γ : G ℚ Ω →* c.Oˣ, (∀ g, Raw.bar γ g = (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O)) → D.XVan γ ∧ D.XVan γ⁻¹ := by
  intro hCor Ω _ _ _ l _ c D hT d f n _ φ ξ hX γ hγ
  haveI : CharP (ResidueField c.O) l := by
    obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (residue c.O), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] c.O)] at hu
    exact PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu)
  set γ' : G ℚ Ω →* (ResidueField c.O)ˣ := redChar Ω (residue c.O) (prodX φ ξ) with hγ'
  obtain ⟨hKn, hKi, -⟩ := spKer D
  have hv : ∀ γ'' : G ℚ Ω →* (ResidueField c.O)ˣ, (γ'' = γ' ∨ γ'' = γ'⁻¹) →
      Van D.T D.pl D.rbar.ker γ'' := by
    intro γ'' hor
    exact vanOf Ω l (ResidueField c.O) γ''
      (hCor Ω l c (ResidueField c.O) (residue c.O) d f n φ ξ hX γ'' hor) D.T D.pl D.rbar.ker hT hKn hKi
  refine ⟨xvan_of_van D γ γ' hγ (hv γ' (Or.inl rfl)), xvan_of_van D γ⁻¹ γ'⁻¹ ?_ (hv γ'⁻¹ (Or.inr rfl))⟩
  intro g
  have h1 := hγ g
  simp only [Raw.bar, MonoidHom.inv_apply] at h1 ⊢
  rw [map_units_inv, Units.val_inv_eq_inv_val, h1]
