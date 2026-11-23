import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def MapBy (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem tMap_iff (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) : TMap t' t f ↔ ∃ φ, MapBy t' t f φ := Iff.rfl

def GeoGood (t t' : TObj g k J b s) (Sg : Set S) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ S), Set.range x ⊆ Sg →
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (su : Sp Ω ⟶ Sp o) (u : TObj g k J b su)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left),
      MapBy u t (spMap i ≫ x) ψ ∧ MapBy u t' (spMap i ≫ x) ψ'

theorem GeoGood.symm {t t' : TObj g k J b s} {Sg : Set S} (h : GeoGood t t' Sg) : GeoGood t' t Sg := fun K _ x hx => by
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := h K x hx
  exact ⟨Ω, inferInstance, inferInstance, i, su, u, ψ', ψ, h₂, h₁⟩

def Compat (t t' : TObj g k J b s) {X : Scheme.{0}} (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left) : Prop :=
  f ≫ t'.A.hom = c₀ ≫ t.A.hom ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ (B : Type) [Field B] (z : Sp B ⟶ u.A.left) (y : Sp B ⟶ X), y ≫ c₀ = z ≫ ψ → y ≫ f = z ≫ ψ'

theorem epi_spMap {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    refine (HasRingHomProperty.Spec_iff (P := @Flat)).2 ?_
    letI := i.toAlgebra
    exact (inferInstance : Module.Flat K Ω)
  have : Surjective (spMap i) := ⟨fun p => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem ext_of_geoGood {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X Y : Scheme.{0}}
    [IsReduced X] (p : X ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (q : Y ⟶ S) [IsSeparated q] {f f' : X ⟶ Y}
    (hf : f ≫ q = p) (hf' : f' ≫ q = p)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ y : Sp K ⟶ X, y ≫ p = x → y ≫ f = y ≫ f') : f = f' := by
  refine (GlobalTheory.dense_fibres_ext X S p Sg hd).2.1 Y q f f' hf hf' fun K _ _ y hy => ?_
  obtain ⟨Ω, _, _, i, su, u, ψ, ψ', h₁, h₂⟩ := hg K (y ≫ p) hy
  have := epi_spMap i
  rw [← cancel_epi (spMap i), ← Category.assoc, ← Category.assoc]
  exact H Ω su u _ ψ ψ' h₁ h₂ _ (Category.assoc _ _ _)

theorem Compat.unique {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X : Scheme.{0}}
    [IsReduced X] {c₀ : X ⟶ t.A.left} [Flat (c₀ ≫ t.A.hom)] [LocallyOfFinitePresentation (c₀ ≫ t.A.hom)]
    {f f' : X ⟶ t'.A.left} (h : Compat t t' c₀ f) (h' : Compat t t' c₀ f') : f = f' := by
  have := t'.ab.proper
  refine ext_of_geoGood hd hg (c₀ ≫ t.A.hom) t'.A.hom h.1 h'.1 fun K _ _ su u x ψ ψ' h₁ h₂ y hy => ?_
  have w : (y ≫ c₀) ≫ t.A.hom = 𝟙 _ ≫ x := by rw [Category.assoc, hy, Category.id_comp]
  have e := (h₁.1.1.lift_fst _ _ w).symm
  exact (h.2 K su u x ψ ψ' h₁ h₂ K _ y e).trans (h'.2 K su u x ψ ψ' h₁ h₂ K _ y e).symm

theorem Compat.comp {t t' : TObj g k J b s} {X Y : Scheme.{0}} {c₀ : X ⟶ t.A.left} {f : X ⟶ t'.A.left}
    (h : Compat t t' c₀ f) (j : Y ⟶ X) : Compat t t' (j ≫ c₀) (j ≫ f) :=
  ⟨by rw [Category.assoc, Category.assoc, h.1], fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y e => by
    rw [← Category.assoc] at e ⊢
    exact h.2 K su u x ψ ψ' h₁ h₂ B z _ e⟩

theorem Compat.fibre {t t' : TObj g k J b s} {φ : t.A.left ⟶ t'.A.left} (h : Compat t t' (𝟙 _) φ)
    {K : Type} [Field K] [IsAlgClosed K] {su : Sp K ⟶ Sp o} {u : TObj g k J b su} {x : Sp K ⟶ S}
    {ψ : u.A.left ⟶ t.A.left} {ψ' : u.A.left ⟶ t'.A.left} (h₁ : MapBy u t x ψ) (h₂ : MapBy u t' x ψ') :
    ψ ≫ φ = ψ' := by
  have := u.ab.proper
  have := u.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced u.A.hom
  have w : (ψ ≫ φ) ≫ t'.A.hom = u.A.hom ≫ x := by rw [Category.assoc, h.1, Category.id_comp, h₁.1.1.w]
  have e : h₂.1.1.lift _ _ w = 𝟙 _ :=
    (GlobalTheory.dense_fibres_ext _ _ u.A.hom Set.univ dense_univ).2.1 _ u.A.hom _ _ (h₂.1.1.lift_snd _ _ _)
      (Category.id_comp _) fun B _ _ z _ => by
        apply h₂.1.1.hom_ext
        · rw [Category.assoc, h₂.1.1.lift_fst, Category.comp_id, ← Category.assoc]
          exact h.2 K su u x ψ ψ' h₁ h₂ B z _ (Category.comp_id _)
        · rw [Category.assoc, h₂.1.1.lift_snd, Category.comp_id]
  rw [← h₂.1.1.lift_fst _ _ w, e, Category.id_comp]

theorem exists_compat_of_local [IsReduced S] {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg)
    (H : ∀ p : t.A.left, ∃ (X : Scheme.{0}) (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left), IsOpenImmersion c₀ ∧
      p ∈ Set.range c₀ ∧ Compat t t' c₀ f) : ∃ φ, Compat t t' (𝟙 _) φ := by
  choose X c₀ f hc₀ hp hf using H
  have := t.ab.smooth
  have := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  let 𝒰 : t.A.left.OpenCover := Scheme.Cover.mkOfCovers _ X c₀ (fun p => ⟨p, hp p⟩) hc₀
  have hc : ∀ p q, pullback.fst (𝒰.f p) (𝒰.f q) ≫ f p = pullback.snd _ _ ≫ f q := fun p q => by
    have := hc₀ p
    have := hc₀ q
    have : IsReduced (pullback (c₀ p) (c₀ q)) := isReduced_of_isOpenImmersion (pullback.fst (c₀ p) (c₀ q) ≫ c₀ p)
    exact ((hf p).comp (pullback.fst (c₀ p) (c₀ q))).unique hd hg
      (by rw [pullback.condition]; exact (hf q).comp (pullback.snd (c₀ p) (c₀ q)))
  have e : ∀ p, c₀ p ≫ 𝒰.glueMorphisms f hc = f p := fun p => 𝒰.ι_glueMorphisms f hc p
  refine ⟨𝒰.glueMorphisms f hc, 𝒰.hom_ext _ _ fun p => ?_, fun K _ _ su u x ψ ψ' h₁ h₂ B _ z y hy => ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (e p)).trans ((hf p).1.trans
      (congrArg _ (Category.id_comp _).symm)))
  · let p := y (default : PrimeSpectrum B)
    have := hc₀ p
    have hr : Set.range y ⊆ Set.range (c₀ p) := by
      rintro _ ⟨q, rfl⟩
      obtain rfl : q = (default : PrimeSpectrum B) := Subsingleton.elim (α := PrimeSpectrum B) _ _
      exact hp _
    have l := IsOpenImmersion.lift_fac (c₀ p) y hr
    rw [← l, Category.assoc, e]
    exact (hf p).2 K su u x ψ ψ' h₁ h₂ B z _ (l.trans ((Category.comp_id _).symm.trans hy))

end GlobalTheory.TUniq
