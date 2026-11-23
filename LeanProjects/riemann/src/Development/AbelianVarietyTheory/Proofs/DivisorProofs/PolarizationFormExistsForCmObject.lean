import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolPairing

theorem exists_isCorrForm_diag : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A),
      GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ ∧ IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ((2 : R) • ψ) := by
  intro H F _ _ 𝔠 R _ X c
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have gAB := smooth_prod X.dim X.dim
  have C := cupSquare_of_free H.1 hAB gAB
  have hP := X.isLB c
  obtain ⟨φ, hφ⟩ := exists_isCorrForm C hP (X.rig₁ c) (X.rig₂ c)
  have anti : ∀ x y, φ y x = -φ x y := by
    obtain ⟨n, a, b, hc, hφe⟩ := id hφ
    let s : X.A ⊗ X.A ⟶ X.A ⊗ X.A := lift (snd X.A X.A) (fst X.A X.A)
    have m : IsMor (dp0 R) ((X.A ⊗ X.A).hom ≫ 𝟙 _) (dp0 R) ((X.A ⊗ X.A).hom ≫ 𝟙 _) (RingHom.id R) s.left :=
      IsMor.of_over _ (by rw [← Category.assoc, Over.w])
    have e₁ : ∀ z, m.pull1 (pullOver (dp0 R) (𝟙 _) (fst X.A X.A) z) = pullOver (dp0 R) (𝟙 _) (snd X.A X.A) z :=
      fun z ↦ (pullOver_pullOver _ _ s (fst X.A X.A) z).trans (by rw [lift_fst])
    have e₂ : ∀ z, m.pull1 (pullOver (dp0 R) (𝟙 _) (snd X.A X.A) z) = pullOver (dp0 R) (𝟙 _) (fst X.A X.A) z :=
      fun z ↦ (pullOver_pullOver _ _ s (snd X.A X.A) z).trans (by rw [lift_snd])
    have hs := isChern_pull m hc
    rw [map_sum] at hs
    simp only [IsMor.pullCohomologyTwo_cup, e₁, e₂] at hs
    have hs' := (isChern_existsUnique_and_iso R _ (dp0 R) _ _).2 _ _ (pull_isLB hP _) hP
      (LBIso.symm (X.symm c)) _ hs
    have H' : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) (-φ.flip) := by
      refine ⟨n, fun k ↦ -b k, a, ?_, fun x y ↦ ?_⟩
      · convert hs' using 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Submodule.coe_neg, map_neg, map_neg, LinearMap.neg_apply]
        exact neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)
      · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφe, map_neg, neg_mul, Finset.sum_neg_distrib]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _)
    have hu := hφ.unique C hP H'
    intro x y
    have := LinearMap.congr_fun₂ hu y x
    simpa using this
  refine ⟨φ, hφ, ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨ψ', hψ', e'⟩ := hψ.pull (homMor (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)))
  have h2 : (2 : R) • φ = ψ' := by
    refine LinearMap.ext₂ fun x y ↦ ?_
    rw [e' (push _ _ (lift (𝟙 X.A) (𝟙 X.A)) x) x (push _ _ (lift (𝟙 X.A) (𝟙 X.A)) y) y (fun _ ↦ rfl) (fun _ ↦ rfl),
      RingHom.id_apply, e, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _),
      push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_id, LinearMap.id_apply,
      LinearMap.id_apply, anti x y, LinearMap.smul_apply, LinearMap.smul_apply, two_smul]
    simp only [LinearMap.add_apply, sub_neg_eq_add]
  rw [h2]
  exact hψ'

end GlobalTheory.PolPairing
