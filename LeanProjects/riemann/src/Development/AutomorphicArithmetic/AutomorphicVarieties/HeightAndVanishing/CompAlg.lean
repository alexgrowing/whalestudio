import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem comp_unit {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u) := by
  apply Units.ext
  rw [MulChar.coe_toUnitHom, comp, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]

private theorem comp_coe {O : Type} [CommRing O] {N : ℕ} (r : ℕ) (χ : DirichletCharacter O N) (u : (ZMod N)ˣ) :
    comp r χ (u : ZMod N) = χ (proj r N u : (ZMod N)ˣ) := by
  rw [← MulChar.coe_toUnitHom, comp_unit, MulChar.coe_toUnitHom]

private noncomputable def compHom (O : Type) [CommRing O] (N : ℕ) (r : ℕ) :
    DirichletCharacter O N →* DirichletCharacter O N :=
  MonoidHom.mk' (comp r) fun χ χ' => by
    refine MulChar.ext fun u => ?_
    rw [MulChar.coeToFun_mul, Pi.mul_apply, comp_coe, comp_coe, comp_coe, MulChar.coeToFun_mul, Pi.mul_apply]

private noncomputable def evalHom (O : Type) [CommRing O] (N : ℕ) (u : (ZMod N)ˣ) :
    DirichletCharacter O N →* O where
  toFun χ := χ (u : ZMod N)
  map_one' := MulChar.one_apply_coe u
  map_mul' χ χ' := by rw [MulChar.coeToFun_mul, Pi.mul_apply]

private theorem prod_comp {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) :
    ∏ p ∈ N.primeFactors, comp p χ = χ := by
  refine MulChar.ext fun u => ?_
  have h1 : (∏ p ∈ N.primeFactors, comp p χ) (u : ZMod N) = evalHom O N u (∏ p ∈ N.primeFactors, comp p χ) := rfl
  rw [h1, map_prod]
  have h2 : ∀ p ∈ N.primeFactors, evalHom O N u (comp p χ) = ((χ.toUnitHom (proj p N u) : Oˣ) : O) := by
    intro p _
    change comp p χ (u : ZMod N) = _
    rw [comp_coe, MulChar.coe_toUnitHom]
  rw [Finset.prod_congr rfl h2, ← Units.coe_prod, ← map_prod, projProd N u, MulChar.coe_toUnitHom]

theorem UpperTheory.V.HV.compAlg :
    ∀ (O : Type) [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (r : ℕ), r.Prime →
      (∀ (χ : DirichletCharacter O N) (u : (ZMod N)ˣ), (comp r χ).toUnitHom u = χ.toUnitHom (proj r N u)) ∧
      (∀ χ χ' : DirichletCharacter O N, comp r (χ * χ') = comp r χ * comp r χ') ∧ comp r (1 : DirichletCharacter O N) = 1 ∧
      (∀ χ : DirichletCharacter O N, comp r χ⁻¹ = (comp r χ)⁻¹) ∧ (∀ (χ : DirichletCharacter O N) (k : ℕ), comp r (χ ^ k) = comp r χ ^ k) ∧
      (∀ χ : DirichletCharacter O N, comp r (comp r χ) = comp r χ ∧ orderOf (comp r χ) ∣ orderOf χ ∧ (¬ r ∣ N → comp r χ = 1) ∧
        ∀ r', r'.Prime → r' ≠ r → comp r (comp r' χ) = 1) ∧
      (∀ χ : DirichletCharacter O N, ∏ p ∈ N.primeFactors, comp p χ = χ) ∧
      ∀ (χ : DirichletCharacter O N) (m : ℕ), (∀ p ∈ N.primeFactors, comp p χ ^ m = 1) → χ ^ m = 1 := by
  intro O _ _ N _ r hr
  have facts := projFacts N r hr
  refine ⟨fun χ u => comp_unit r χ u, fun χ χ' => map_mul (compHom O N r) χ χ', ?_,
    fun χ => map_inv (compHom O N r) χ, fun χ k => map_pow (compHom O N r) χ k,
    fun χ => ⟨?_, orderOf_map_dvd (compHom O N r) χ, ?_, ?_⟩, fun χ => prod_comp χ, ?_⟩
  · refine MulChar.ext fun u => ?_
    rw [comp_coe, MulChar.one_apply_coe, MulChar.one_apply_coe]
  · refine MulChar.ext fun u => ?_
    rw [comp_coe, comp_coe, comp_coe, facts.2.2.1]
  · intro h
    refine MulChar.ext fun u => ?_
    rw [comp_coe, facts.2.2.2.2.1 h u, Units.val_one, MulChar.map_one, MulChar.one_apply_coe]
  · intro r' hr' hne
    refine MulChar.ext fun u => ?_
    rw [comp_coe, comp_coe, (projFacts N r' hr').2.2.2.1 r hr hne.symm u, Units.val_one, MulChar.map_one,
      MulChar.one_apply_coe]
  · intro χ m h
    rw [← prod_comp χ, ← Finset.prod_pow]
    exact Finset.prod_eq_one h
