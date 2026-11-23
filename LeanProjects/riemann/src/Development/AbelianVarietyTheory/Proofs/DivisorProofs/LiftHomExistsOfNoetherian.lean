import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHomReductionDescendsFinitelyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushMemLiftFilOfInjectiveStatement

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftHom_exists_of_noetherian : AbelianDeRham → (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (hI : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I → LiftObj (divided₂ hI) π ∧ LiftHom (divided₂ hI) π) →
  ∀ (R : Type) [CommRing R] (I : Ideal R) (h : I ^ 2 = 0) (R₀ : Type) [CommRing R₀] (π : R →+* R₀),
    Function.Surjective π → RingHom.ker π = I →
  ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left)
    (hA : IsGrpPullback A₀ A (spMap π) i), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
  ∀ (g' : ℕ) (B₀ : Over (Sp R₀)) [GrpObj B₀] (B : Over (Sp R)) [GrpObj B] (j : B₀.left ⟶ B.left)
    (hB : IsGrpPullback B₀ B (spMap π) j), IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom →
  ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], (∀ d ∈ liftFil (divided₂ h) hA, push (divided₂ h) (spMap π) f₀ d ∈ liftFil (divided₂ h) hB) →
    ∃ f : A ⟶ B, i ≫ f.left = f₀.left ≫ j := by
  intro P H R _ I h R₀ _ π hπ hker g A₀ _ A _ i hA abA smA g' B₀ _ B _ j hB abB smB f₀ _ hfil
  obtain ⟨S, ι₀, AS₀, _, AS, _, iS, BS₀, _, BS, _, jS, fS₀, φA, φB, ψA, ψB, hfg, hι, _, hAS, hBS, abAS, smAS,
    abBS, smBS, pA, pB, qA, qB, cA, cB, cf⟩ := GlobalTheory.T.abelian_hom_reduction_descends_finitely_generated R I R₀ π hπ hker g A₀ A i hA abA smA g' B₀ B j hB abB smB f₀
  have hS : (I.comap S.subtype) ^ 2 = 0 := by
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    refine (Ideal.le_comap_pow _ 2).trans ?_
    rw [h, Ideal.zero_eq_bot, Ideal.comap_bot_of_injective _ Subtype.val_injective]
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have hfilS := GlobalTheory.T.push_mem_liftFil_of_injective_alt P R I h R₀ π hπ hker S S.subtype Subtype.val_injective (I.comap S.subtype) hS
    (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ι₀ hι
    g A₀ A i hA AS₀ AS iS hAS abA smA abAS smAS φA ψA pA qA cA
    g' B₀ B j hB BS₀ BS jS hBS abB smB abBS smBS φB ψB pB qB cB f₀ fS₀ cf hfil
  obtain ⟨fS, ⟨_, efS⟩, -⟩ := (H S (I.comap S.subtype) hS (S ⧸ I.comap S.subtype) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker).2 g AS₀ AS iS hAS abAS smAS g' BS₀ BS jS hBS abBS smBS fS₀ hfilS
  let fl : A.left ⟶ B.left := pB.1.lift (φA ≫ fS.left) A.hom (by
    rw [Category.assoc, Over.w fS, pA.1.w])
  refine ⟨Over.homMk fl (pB.1.lift_snd _ _ _), ?_⟩
  apply pB.1.hom_ext
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_fst]
    rw [reassoc_of% cA, efS, ← Category.assoc, ← cf, Category.assoc, cB]
  · simp only [Over.homMk_left, Category.assoc, fl, pB.1.lift_snd]
    rw [hA.1.w, hB.1.w, ← Category.assoc, Over.w f₀]

end GlobalTheory
