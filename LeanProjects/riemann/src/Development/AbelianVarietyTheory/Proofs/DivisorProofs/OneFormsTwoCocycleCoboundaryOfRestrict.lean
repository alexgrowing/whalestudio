import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem inr_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x + y = z + w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) + TrivSqZeroExt.inr y =
      TrivSqZeroExt.inr z + TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_add, ← TrivSqZeroExt.inr_add, h]

theorem inr_sub_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x - y + z = w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) - TrivSqZeroExt.inr y + TrivSqZeroExt.inr z =
      TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_sub, ← TrivSqZeroExt.inr_add, h]

theorem snd_sub_add {A M : Type} [AddCommGroup A] [AddCommGroup M] (a b c : TrivSqZeroExt A M) :
    (a - b + c).snd = a.snd - b.snd + c.snd := by
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub]

theorem mp_omExt_inr {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {T T' : C} (φ : T ⟶ T') (x : Ω[F.obj T⁄R]) :
    mp (omExt F) φ (TrivSqZeroExt.inr x : (omExt F).obj T) =
      (TrivSqZeroExt.inr (p1 F φ x) : (omExt F).obj T') :=
  TrivSqZeroExt.ext ((fst_extMap F φ _).trans (by rw [TrivSqZeroExt.fst_inr, map_zero]; rfl))
    ((snd_extMap F φ _).trans (by rw [TrivSqZeroExt.snd_inr]; rfl))

theorem coboundary_of_restrict_forms : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict (FormExt.omExt F) G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) := by
  intro R _ C _ C' _ F G hinj κ hκ β' hβ'
  let z : Z2 (omExt F) := ⟨fun T T' T'' φ ψ ↦ TrivSqZeroExt.inr (κ T T' T'' φ ψ),
    fun T T' T'' T''' φ ψ χ ↦ by
      simp only []
      rw [mp_omExt_inr]
      exact inr_add_inr_eq (hκ φ ψ χ)⟩
  have h0 : (CoefMap.restrict (omExt F) G).pull2 (H2.mk (omExt F) z) = 0 := by
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun t t' a ↦ (TrivSqZeroExt.inr (β' t t' a) : (omExt F).obj (G.obj t')), ?_⟩
    funext t t' t'' a b
    exact (congrArg (fun x : TrivSqZeroExt (F.obj (G.obj t'')) Ω[F.obj (G.obj t'')⁄R] ↦
      x - TrivSqZeroExt.inr (β' t t'' (a ≫ b)) + TrivSqZeroExt.inr (β' t' t'' b))
      (mp_omExt_inr F (G.map b) (β' t t' a))).trans (inr_sub_add_inr_eq (hβ' a b).symm)
  have h1 : H2.mk (omExt F) z = 0 := hinj (h0.trans (map_zero _).symm)
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 h1
  refine ⟨fun T T' φ ↦ (f T T' φ).snd, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrArg TrivSqZeroExt.snd
    (congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ)
  have e2 := (snd_sub_add (mp (omExt F) ψ (f T T' φ)) (f T T'' (φ ≫ ψ)) (f T' T'' ψ)).symm.trans
    (e.trans (TrivSqZeroExt.snd_inr _ _))
  rw [show (mp (omExt F) ψ (f T T' φ)).snd = p1 F ψ (f T T' φ).snd from snd_extMap F ψ _] at e2
  exact e2.symm

end GlobalTheory.CechDR.FormExt
