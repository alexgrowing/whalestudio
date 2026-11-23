import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem torsion_descends_to_complex : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (N : ℕ), 1 ≤ N → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp ℂ) (y : Over.mk t ⟶ X.A), y ^ N = 1 → ∃ z : 𝟙_ (Over (Sp ℂ)) ⟶ X.A, y = toUnit (Over.mk t) ≫ z := by
  intro F _ _ 𝔠 X N hN Ω _ _ t y hy
  have hM := GlobalTheory.abMulN_holds
  have : CharZero Ω := charZero_of_injective_ringHom (f := (Spec.preimage t).hom) (RingHom.injective _)
  have hSub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have : Flat t := inferInstance
  have : Surjective t := ⟨fun _ => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim _ _⟩⟩
  have : Epi t := Flat.epi_of_flat_of_surjective _
  letI : GrpObj ((Over.pullback t).obj X.A) := Functor.grpObjObj
  have hg : IsGrpPullback ((Over.pullback t).obj X.A) X.A t (pullback.fst X.A.hom t) := isGrpPullback_pullback X.A t
  have hab : IsAbelianScheme ((Over.pullback t).obj X.A) := GlobalTheory.isAbelianScheme_pullback_obj t X.A X.ab
  have hdim : SmoothOfRelativeDimension (Module.finrank ℚ F) ((Over.pullback t).obj X.A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 X.dim
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hg (𝟙 (Sp Ω)) t (Category.id_comp t).symm
  have hNΩ : ((N : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hNC : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h₁ := hM Ω ((Over.pullback t).obj X.A) _ N hab hdim hNΩ
  have h₂ := hM ℂ X.A _ N X.ab X.dim hNC
  let r : {z : 𝟙_ (Over (Sp ℂ)) ⟶ X.A // z ^ N = 1} → {y : Over.mk t ⟶ X.A // y ^ N = 1} := fun z =>
    ⟨toUnit (Over.mk t) ≫ z.1, by rw [← MonObj.comp_pow, z.2, MonObj.comp_one]⟩
  have hl : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  have hr : Function.Injective r := fun a b h => Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 (by
    have := congrArg (fun q => q.1.left) h
    simpa only [r, Over.comp_left, hl] using this)))
  have hc : Nat.card {y : Over.mk t ⟶ X.A // y ^ N = 1} =
      Nat.card {x : 𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj X.A // x ^ N = 1} :=
    (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => by
      change x ^ N = 1 ↔ e x ^ N = 1
      rw [← map_pow, map_eq_one_iff e e.injective])).symm
  have : Finite {y : Over.mk t ⟶ X.A // y ^ N = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc, h₁]; positivity)
  obtain ⟨z, hz⟩ := ((Nat.bijective_iff_injective_and_card r).2 ⟨hr, h₂.trans (h₁.symm.trans hc.symm)⟩).2 ⟨y, hy⟩
  exact ⟨z.1, (congrArg Subtype.val hz).symm⟩

end GlobalTheory.RealMult
