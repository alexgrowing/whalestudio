import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineDeformationAmalgamateOverFibreProductStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdIdealEqBotOfCrystallineDeformationStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatingElementUnramifiedTwistEqPowMulUnitStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryIdealSaturatorsMapAlgHomStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsTruncatedPolynomialThickeningFibreSquareStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.CrystallineTwistByUnramifiedCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.CrFrac

theorem push_comp {O R A B' Γ : Type} [CommRing O] [CommRing R] [CommRing A] [CommRing B'] [Algebra O R]
    [Algebra O A] [Algebra O B'] [Group Γ] (g : A →ₐ[O] B') (F : R →ₐ[O] A) (r : Γ →* GG 3 R) :
    push (g.comp F) r = (GG.map (g : A →+* B')).comp (push F r) := rfl

theorem core (hL : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O)
    (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B)
    (hf : D.InDcr (π : B →+* E) (push f U.r.hom))
    (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C]
    [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C]
    [IsScalarTower ℚ_[l] E C]
    (T : Type) [CommRing T] [Algebra ℚ_[l] T] [Module.Finite ℚ_[l] T] [Algebra O T] [Algebra ℤ_[l] T]
    [IsScalarTower ℤ_[l] O T] [IsScalarTower ℤ_[l] ℚ_[l] T] [Algebra E T] [IsScalarTower O E T]
    [IsScalarTower ℚ_[l] E T]
    (πC : C →ₐ[E] E) (p₁ : T →ₐ[E] B) (p₂ : T →ₐ[E] C) (t : C) (ht : IsNilpotent t)
    (hπC : ∀ a, πC a = 0 → IsNilpotent a) (hπT : ∀ a, π (p₁ a) = 0 → IsNilpotent a)
    (hcomp : π.comp p₁ = πC.comp p₂) (hsurj : ∀ b c, π b = πC c → ∃ s, p₁ s = b ∧ p₂ s = c) (k : ℕ)
    (hcanc : ∀ (P y : T) (j : ℕ) (v : Cˣ), j ≤ 2 * k → p₂ P = t ^ j * v → P * y = 0 → p₁ y = 0)
    (a : U.R) (ha : GlobalTheory.OrdLoc.del D U.r.hom ^ k * a ∈ GlobalTheory.OrdLoc.ordIdeal D U.r.hom) : f a = 0 := by
  obtain ⟨u, hu1, hu2, hu3, j, v, hj, hdel⟩ := GlobalTheory.T.saturatingElement_unramified_twist_eq_pow_mul_unit D E C t ht
  have hr₂ := GlobalTheory.T.crystalline_twist_by_unramified_character D E C πC hπC u hu1 hu2 hu3
  obtain ⟨r, hr, hr1, hr2⟩ := GlobalTheory.T.crystallineDeformation_amalgamate_over_fibre_product_cover hL D E B π hπ C πC hπC T (π.comp p₁) hπT p₁ p₂ rfl hcomp.symm hsurj
    (push f U.r.hom) _ hf hr₂
  have hx : (GG.map (π : B →+* E)).comp (push f U.r.hom) = push ((π.restrictScalars O).comp f) U.r.hom :=
    (push_comp (π.restrictScalars O) f U.r.hom).symm
  obtain ⟨F, hF, -⟩ := unramified_lift_deformation D U E T (π.comp p₁) hπT ((π.restrictScalars O).comp f) r hr.mult
    (hr.red.trans (hf.red.symm.trans hx)) hr.cont
  have hF1 : (p₁.restrictScalars O).comp F = f := by
    obtain ⟨g, -, hg⟩ := unramified_lift_deformation D U E B π hπ ((π.restrictScalars O).comp f) (push f U.r.hom) hf.mult hx hf.cont
    refine (hg _ ?_).trans (hg f rfl).symm
    show push ((p₁.restrictScalars O).comp F) U.r.hom = push f U.r.hom
    rw [push_comp, hF]
    exact hr1
  have h0 := GlobalTheory.T.ordIdeal_eq_bot_of_crystalline_deformation hL D E T (π.comp p₁) hπT r hr
  obtain ⟨hmap, -, hdelF⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D F U.r.hom
  have h1 : F (GlobalTheory.OrdLoc.del D U.r.hom ^ k * a) = 0 := by
    have h := Ideal.mem_map_of_mem (F : U.R →+* T) ha
    rw [hmap, hF, h0] at h
    exact (Submodule.mem_bot _).1 h
  rw [map_mul, map_pow, hdelF, hF] at h1
  obtain ⟨-, -, hdel2⟩ := GlobalTheory.T.ordinaryIdeal_saturators_map_algHom D (p₂.restrictScalars O) r
  have hpush : push (p₂.restrictScalars O) r = r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) := hr2
  rw [hpush, hdel] at hdel2
  have hP : p₂ (GlobalTheory.OrdLoc.del D r ^ k) = t ^ (j * k) * ((v ^ k : Cˣ) : C) := by
    rw [map_pow, show p₂ (GlobalTheory.OrdLoc.del D r) = t ^ j * v from hdel2, mul_pow, ← pow_mul, Units.val_pow_eq_pow_val]
  have h2 := hcanc _ (F a) (j * k) (v ^ k) (by nlinarith) hP h1
  rw [← hF1]
  exact h2

theorem main (hL : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O)
    (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E]
    (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
    [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
    [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (f : U.R →ₐ[O] B)
    (hf : D.InDcr (π : B →+* E) (push f U.r.hom)) : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f := by
  rintro a ⟨k, hk⟩
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  obtain ⟨C, _, _, _, T, _, _, _, πC, p₁, p₂, t, ht, hπC, hπT, hcomp, hsurj, hcanc⟩ := GlobalTheory.T.exists_truncated_polynomial_thickening_fibre_square π hπ (2 * k)
  letI : Algebra O C := Algebra.compHom C (algebraMap O E)
  letI : Algebra ℚ_[l] C := Algebra.compHom C (algebraMap ℚ_[l] E)
  letI : Algebra ℤ_[l] C := Algebra.compHom C (algebraMap ℤ_[l] E)
  haveI : IsScalarTower O E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ_[l] E C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ_[l] O C := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E C) (IsScalarTower.algebraMap_apply ℤ_[l] O E x)
  haveI : IsScalarTower ℤ_[l] ℚ_[l] C := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E C) (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E x)
  haveI : Module.Finite ℚ_[l] C := Module.Finite.trans E C
  letI : Algebra O T := Algebra.compHom T (algebraMap O E)
  letI : Algebra ℚ_[l] T := Algebra.compHom T (algebraMap ℚ_[l] E)
  letI : Algebra ℤ_[l] T := Algebra.compHom T (algebraMap ℤ_[l] E)
  haveI : IsScalarTower O E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ_[l] E T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℤ_[l] O T := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E T) (IsScalarTower.algebraMap_apply ℤ_[l] O E x)
  haveI : IsScalarTower ℤ_[l] ℚ_[l] T := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (algebraMap E T) (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E x)
  haveI : Module.Finite ℚ_[l] T := Module.Finite.trans E T
  exact core hL D U E B π hπ f hf C T πC p₁ p₂ t ht hπC hπT hcomp hsurj k hcanc a hk

end GlobalTheory.CrFrac
