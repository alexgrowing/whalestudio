import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafPullbackRelationsBasicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.Axes

theorem injective_of_section {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q]
    [Module R Q] [Module.Finite R M] [Module.Projective R M] [Module.Finite R Q] [Module.Projective R Q]
    (N : M →ₗ[R] Q) (P : Q →ₗ[R] M) (hNP : N ∘ₗ P = LinearMap.id)
    (hr : ∀ p, Module.rankAtStalk (R := R) M p = Module.rankAtStalk (R := R) Q p) : Function.Injective N := by
  obtain ⟨e, -, -⟩ := ((LinearMap.exact_subtype_ker_map N).splitSurjectiveEquiv
    (LinearMap.ker N).injective_subtype ⟨P, hNP⟩)
  haveI : Module.Projective R (LinearMap.ker N × Q) := Module.Projective.of_equiv e
  haveI : Module.Projective R (LinearMap.ker N) :=
    Module.Projective.of_split (LinearMap.inl R _ Q) (LinearMap.fst R _ Q) (by ext x <;> simp)
  haveI : Module.Finite R (LinearMap.ker N) :=
    Module.Finite.of_surjective ((LinearMap.fst R _ Q) ∘ₗ e.toLinearMap)
      (fun x ↦ ⟨e.symm (x, 0), by simp⟩)
  have h1 := Module.rankAtStalk_eq_of_equiv e
  rw [Module.rankAtStalk_prod] at h1
  have h0 : Module.rankAtStalk (R := R) (LinearMap.ker N) = 0 := by
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hr p] at this
    simpa using this
  haveI := Module.rankAtStalk_eq_zero_iff_subsingleton.1 h0
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker N) 0)

variable {R : Type} [CommRing R]

theorem isPullO_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ₁ φ₂ : X' ⟶ X} (e : φ₁ = φ₂)
    (h₁ : φ₁ ≫ s = s' ≫ spMap (RingHom.id R)) (h₂ : φ₂ ≫ s = s' ≫ spMap (RingHom.id R)) {a : HO1 s}
    {a' : HO1 s'} : IsPullO h₁ a a' ↔ IsPullO h₂ a a' := by
  subst e; rfl

theorem isPullO_id {X : Scheme.{0}} (s : X ⟶ Sp R) (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (a : HO1 s) :
    IsPullO h a a := by
  unfold IsPullO
  refine CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes (𝟙 X) s)
    { app := fun p ↦ (homOfLE (show p.unop.1.1 ≤ p.unop.1.2 from p.unop.2)).op
      naturality := fun _ _ _ ↦ Subsingleton.elim _ _ } ?_ a
  intro p b
  simp only [pairRes, pairPull, secPull, Sec.res, CoefMap.restrict]
  simp [Scheme.Hom.appLE, mp]
  rfl

abbrev pb {Y A : Over (Sp R)} (f : Y ⟶ A) : HO1 A.hom →ₗ[R] HO1 Y.hom := pullHO1 (overW f)

theorem pb_comp {Z Y A : Over (Sp R)} (f : Z ⟶ Y) (g : Y ⟶ A) (a : HO1 A.hom) :
    pb (f ≫ g) a = pb f (pb g a) := by
  have h'' : (f.left ≫ g.left) ≫ A.hom = Z.hom ≫ spMap (RingHom.id R) := by
    have e : (f ≫ g).left = f.left ≫ g.left := by simp
    rw [← e]; exact overW (f ≫ g)
  have k := (GlobalTheory.T.structureSheaf_pullback_relations_basic R A.left Y.left A.hom Y.hom g.left (overW g)).2.2 Z.left Z.hom f.left (overW f) h''
    a (pb g a) (pb f (pb g a)) (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)
  exact ((isPullO_congr (show f.left ≫ g.left = (f ≫ g).left by simp) h'' (overW (f ≫ g))).1 k).eq_pullHO1.symm

theorem pb_id (A : Over (Sp R)) (a : HO1 A.hom) : pb (𝟙 A) a = a := by
  have h : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.id_left]; exact overW (𝟙 A)
  exact ((isPullO_congr (Over.id_left A).symm h (overW (𝟙 A))).1 (isPullO_id A.hom h a)).eq_pullHO1.symm

theorem pb_one (Y A : Over (Sp R)) [GrpObj A] (u : Y ⟶ 𝟙_ (Over (Sp R))) (a : HO1 A.hom) :
    pb (u ≫ η[A]) a = 0 := by
  haveI : IsAffine (𝟙_ (Over (Sp R))).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  rw [pb_comp, (GlobalTheory.T.abelian_square_affine_h1_vanish R).2 _ _ (pb η[A] a), map_zero]

theorem isPullO_zero_iff {Y A : Over (Sp R)} (f : Y ⟶ A) (c : HO1 A.hom) : IsPullO (overW f) c 0 ↔ pb f c = 0 :=
  ⟨fun e ↦ e.eq_pullHO1.symm, fun e ↦ e ▸ isPullO_pullHO1 _ c⟩

end Axes

open Axes in

theorem axesO1_of_cohomology_structure : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
      ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
    ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b,
      e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → AxesVanishingStructureSheafDegOne := by
  intro hS R _ A _ g hA hg c h₁ h₂
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨f1, p1, r1⟩, -⟩ := hS R A g hA hg
  obtain ⟨⟨f2, p2, r2⟩, -⟩ := hS R (A ⊗ A) (g + g) hA2 hg2
  let N : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
    LinearMap.prod (pb (lift (𝟙 A) 1)) (pb (lift 1 (𝟙 A)))
  let P : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
    LinearMap.coprod (pb (fst A A)) (pb (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pb (lift (𝟙 A) 1) (pb (fst A A) x.1 + pb (snd A A) x.2) = x.1
      rw [map_add, ← pb_comp, ← pb_comp, lift_fst, lift_snd, pb_id]
      rw [show (1 : A ⟶ A) = toUnit A ≫ η[A] from rfl, pb_one, add_zero]
    · show pb (lift 1 (𝟙 A)) (pb (fst A A) x.1 + pb (snd A A) x.2) = x.2
      rw [map_add, ← pb_comp, ← pb_comp, lift_fst, lift_snd, pb_id]
      rw [show (1 : A ⟶ A) = toUnit A ≫ η[A] from rfl, pb_one, zero_add]
  have hinj := injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N c = N 0)
  rw [map_zero]
  exact Prod.ext ((isPullO_zero_iff _ c).1 h₁) ((isPullO_zero_iff _ c).1 h₂)

end GlobalTheory.Obs
