import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem spMap_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem gen_unique_of_eq {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {Ix : Type} [Fintype Ix]
    {φ φ' : Ix → (Y ⟶ X)} {ε : Ix → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (hφ : φ' = φ) {u : LB.Gen (LB.LinComb M φ' ε)}
    {u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  subst hφ
  exact gen_unique hM p e he hp hu hu' h Z r z J hJ

theorem gen_values_mem : ∀ (V₁ W₀ : Type) [CommRing V₁] [CommRing W₀] (ib : W₀ →+* V₁) (A : Over (Sp V₁)) [GrpObj A],
    IsAbelianScheme A → ∀ (B₀ : Over (Sp W₀)) (β : A.left ⟶ B₀.left), IsPullback β A.hom B₀.hom (spMap ib) →
    ∀ (M₀ : LB B₀.left), M₀.IsLB → ∀ (Ix : Type) [Fintype Ix] (φ : Ix → (A.left ⟶ B₀.left))
    (ψ : Ix → (B₀.left ⟶ B₀.left)), (∀ k, φ k = β ≫ ψ k) → ∀ (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb M₀ φ ε)),
    t.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    (∀ a, ev (ib a) ∈ k₀) → ∀ x₁ : Sp K ⟶ A.left, x₁ ≫ A.hom = spMap ev → DefOver k₀ (x₁ ≫ β) →
    (∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → val t x₁ z J = 1) →
    ∀ x : Sp K ⟶ A.left, x ≫ A.hom = spMap ev → DefOver k₀ (x ≫ β) →
    ∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → ∃ c ∈ k₀, (val t x z J).val = toStk z c := by
  intro V₁ W₀ _ _ ib A _ hA B₀ β hβ M₀ hM₀ Ix _ φ ψ hφ ε t ht K _ _ ev k₀ hk₀ hk x₁ hx₁ hd₁ h1 x hx hd z J hJ
  classical
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  let v : (Sp K ⟶ A.left) → ((Sp K ⟶ B₀.left) → M₀.ι) → K := fun x J =>
    valF x (LB.wchart M₀ φ (fun k => J (x ≫ φ k))) ((genSec t ht).f (fun k => J (x ≫ φ k)))
  have hv : ∀ x z J, Good M₀ z J → (val t x z J).val = toStk z (v x J) := fun x z J hJ =>
    (sval_genSec t ht x z hJ).symm.trans (toStk_valF_gs x _ z (hJ.mem φ x) _).symm
  have hfix : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) →
      ∀ k, spMap σ.toRingHom ≫ x ≫ φ k = x ≫ φ k := by
    intro x hd σ hσ k
    obtain ⟨P₀, hP₀⟩ := hd
    rw [hφ k, ← Category.assoc x, ← hP₀, Category.assoc, ← Category.assoc (spMap σ.toRingHom),
      spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  have hvσ : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ z J, Good M₀ z J →
      (val t (spMap σ.toRingHom ≫ x) z J).val = toStk z (σ (v x J)) := fun x hd σ hσ z J hJ =>
    (sval_genSec t ht _ z hJ).symm.trans (sval_spMap _ σ.toRingHom x z hJ (hfix x hd σ hσ))
  have hsurj : Function.Surjective (pullback.snd A.hom (spMap ev)).appTop.hom :=
    fun w => TLinPf.const_pullback GlobalTheory.SemiRigid.globalFns (spMap ev) A hA w
  have key : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ (v x J) = v x J := by
    intro σ hσ
    have hc : (pullback.fst A.hom (spMap ev) ≫ β) ≫ B₀.hom =
        (pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev) ≫ spMap ib := by
      simp only [Category.assoc]
      rw [hβ.w, pullback.condition_assoc, spMap_two, spMap_conj k₀ _ hf σ hσ]
    obtain ⟨l, hl1, hl2⟩ : ∃ l : pullback A.hom (spMap ev) ⟶ A.left, l ≫ β = pullback.fst A.hom (spMap ev) ≫ β ∧
        l ≫ A.hom = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev :=
      ⟨hβ.lift _ _ hc, hβ.lift_fst _ _ hc, hβ.lift_snd _ _ hc⟩
    obtain ⟨σt, hs1, hs2⟩ : ∃ σt : pullback A.hom (spMap ev) ⟶ pullback A.hom (spMap ev),
        σt ≫ pullback.fst A.hom (spMap ev) = l ∧
        σt ≫ pullback.snd A.hom (spMap ev) = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom :=
      ⟨pullback.lift l _ (by rw [hl2, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hσβ : σt ≫ pullback.fst A.hom (spMap ev) ≫ β = pullback.fst A.hom (spMap ev) ≫ β := by
      rw [reassoc_of% hs1, hl1]
    have hpt : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) →
        pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) ≫ σt =
          spMap σ.toRingHom ≫ pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) := by
      intro y hy hd
      obtain ⟨P₀, hP₀⟩ := hd
      apply pullback.hom_ext
      · simp only [Category.assoc, hs1, pullback.lift_fst]
        apply hβ.hom_ext
        · simp only [Category.assoc, hl1, pullback.lift_fst_assoc]
          rw [← hP₀, ← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
        · simp only [Category.assoc, hl2, pullback.lift_snd_assoc, Category.id_comp, hy]
      · simp only [Category.assoc, hs2, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd, Category.comp_id]
    let tK := LB.pullGen M₀ φ ε t (pullback.fst A.hom (spMap ev))
    have htK : tK.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
    have hu : (LB.pullGen M₀ _ ε tK σt).IsGen := DVR.pullGen_isGen _ _ _ _ htK _
    have hval : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) → ∀ z J, Good M₀ z J →
        val (LB.pullGen M₀ _ ε tK σt) (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J =
          val t (spMap σ.toRingHom ≫ y) z J := by
      intro y hy hd z J hJ
      rw [val_pull hJ, hpt y hy hd, val_pull hJ, Category.assoc, pullback.lift_fst]
    have hvalK : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev) z J, Good M₀ z J →
        val tK (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J = val t y z J := by
      intro y hy z J hJ
      rw [val_pull hJ, pullback.lift_fst]
    have huniq := gen_unique_of_eq hM₀ (pullback.snd A.hom (spMap ev))
      (pullback.lift x₁ (𝟙 _) (by rw [hx₁, Category.id_comp])) (pullback.lift_snd _ _ _) hsurj
      (funext fun k => by rw [hφ k]; exact (reassoc_of% hσβ) (ψ k)) hu htK (fun y J hJ => by
        rw [hval x₁ hx₁ hd₁ y J hJ, hvalK x₁ hx₁ y J hJ, h1 y J hJ]
        apply Units.ext
        have e1 := hv x₁ y J hJ
        rw [h1 y J hJ, Units.val_one, ← map_one (toStk y)] at e1
        rw [hvσ x₁ hd₁ σ hσ y J hJ, ← (toStk y).injective e1, map_one, map_one, Units.val_one])
      (Sp K) (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])) z J hJ
    rw [hval x hx hd z J hJ, hvalK x hx z J hJ] at huniq
    have e2 := congrArg Units.val huniq
    rw [hvσ x hd σ hσ z J hJ, hv x z J hJ] at e2
    exact (toStk z).injective e2
  refine ⟨v x J, ?_, hv x z J hJ⟩
  apply mem_of_finite_conj k₀ hk₀
  apply (Set.finite_singleton (v x J)).subset
  rintro b ⟨σ, hσ, rfl⟩
  exact key σ hσ

end GlobalTheory.Poinc.Sep
