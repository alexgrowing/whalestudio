import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLift

structure Data where

  R : Type
  [ring : CommRing R]

  I : Ideal R

  κ : DividedPowers I
  nil : IsNilDP κ

  X : Scheme.{0}

  X₀ : Scheme.{0}

  s : X ⟶ Sp R

  t : X₀ ⟶ Sp R

  i : X₀ ⟶ X
  smooth : Smooth s
  sep : IsSeparated s
  qc : QuasiCompact s
  red : ∃ s₀ : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀ s (spMap (Ideal.Quotient.mk I)) ∧ t = s₀ ≫ spMap (Ideal.Quotient.mk I)

attribute [instance] Data.ring

def Data.ofQuot {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) (hκ : IsNilDP κ)
    {R₀ : Type} [CommRing R₀] (π : R →+* R₀) (hπ : Function.Surjective π) (hI : RingHom.ker π = I)
    {X X₀ : Scheme.{0}} (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) (h : IsPullback i s₀ s (spMap π)) (t : X₀ ⟶ Sp R) (ht : t = s₀ ≫ spMap π) : Data where
  R := R
  I := I
  κ := κ
  nil := hκ
  X := X
  X₀ := X₀
  s := s
  t := t
  i := i
  smooth := hs
  sep := hs'
  qc := hs''
  red := by
    subst hI
    let e' := RingHom.quotientKerEquivOfSurjective hπ
    let e : R ⧸ RingHom.ker π →+* R₀ := e'
    have he : spMap e ≫ spMap (Ideal.Quotient.mk (RingHom.ker π)) = spMap π := by
      rw [← Cris.spMap_comp]; rfl
    haveI : IsIso (spMap e) := (inferInstance : IsIso (Spec.map e'.toCommRingCatIso.hom))
    refine ⟨s₀ ≫ spMap e, ?_, by rw [ht, Category.assoc, he]⟩
    exact h.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap e)) (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp [he])

def Data.self {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s) (hs' : IsSeparated s)
    (hs'' : QuasiCompact s) : Data :=
  Data.ofQuot (dp0 R) (isDPNilpotent_bot R) (RingHom.id R) Function.surjective_id
    ((RingHom.injective_iff_ker_eq_bot _).1 fun _ _ h ↦ h) s s (𝟙 X) hs hs' hs''
    (by rw [Cris.spMap_id]; exact IsPullback.id_horiz s) s (by rw [Cris.spMap_id, Category.comp_id])

def Data.sqLine {R : Type} [CommRing R] {I : Ideal R} (h : I ^ 2 = 0) : Data :=
  Data.ofQuot (divided₂ h) (isDPNilpotent_squareZero h) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Ideal.mk_ker
    (lineStr R) _ _ (by
      rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
      have : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
      exact RingHom.smooth_algebraMap.2 this) inferInstance inferInstance
    (IsPullback.of_hasPullback _ _) _ rfl

def Data.lineModFour : Data :=
  Data.sqLine (R := ZMod 4) (I := Ideal.span {2}) (by
    rw [Ideal.span_singleton_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; decide)

theorem Data.lineModFour_ideal : Data.lineModFour.I ≠ ⊥ ∧ Data.lineModFour.I ≠ ⊤ := by
  change Ideal.span {(2 : ZMod 4)} ≠ ⊥ ∧ Ideal.span {(2 : ZMod 4)} ≠ ⊤
  rw [Ne, Ne, Ideal.span_singleton_eq_bot, Ideal.span_singleton_eq_top]
  decide

theorem Data.lineModFour_nontrivial : Nontrivial (HH1 Data.lineModFour.s) := by
  change Nontrivial (HH1 (lineStr (ZMod 4)))
  refine ⟨⟨lineEquiv _ (Submodule.Quotient.mk ((Polynomial.X : Polynomial (ZMod 4)) •
    KaehlerDifferential.D (ZMod 4) (Polynomial (ZMod 4)) Polynomial.X)), 0, ?_⟩⟩
  rw [Ne, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
  rintro ⟨p, hp⟩
  have f3 := congrArg (KaehlerDifferential.polynomialEquiv (ZMod 4)) hp
  simp only [Derivation.coeFn_coe, map_smul, KaehlerDifferential.polynomialEquiv_D, Polynomial.derivative_X,
    smul_eq_mul, mul_one] at f3
  have := congrArg (Polynomial.coeff · 1) f3
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_X_one] at this
  revert this
  generalize p.coeff (1 + 1) = a
  revert a
  decide

def affDiag (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), le_rfl⟩ : Pair (𝟙 X))) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def affDiagCoef {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) :
    CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := affDiag X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem pairRes2_id_injective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) :
    Function.Injective (pullHyp2 (pairRes (𝟙 X) s)) := by
  refine Function.LeftInverse.injective (g := pullHyp2 (affDiagCoef s)) fun c ↦ ?_
  exact (pullHyp2_comp _ _ c).symm.trans (pullHyp2_id c)

end GlobalTheory.SmoothLift

namespace GlobalTheory.Published

open GlobalTheory.SmoothLift

def CrystallineSmoothLift : Prop :=
  ∃ (e₁ : ∀ D : Data, CatCoh.H1 (O D.κ D.t) ≃ₗ[D.R] HH1 D.s) (e₂ : ∀ D : Data, CatCoh.H2 (O D.κ D.t) ≃ₗ[D.R] HH2 D.s),
    (∀ (D : Data) (a b : CatCoh.H1 (O D.κ D.t)), e₂ D (cup _ a b) = cupHH D.s (e₁ D a) (e₁ D b)) ∧
    (∀ (D : Data) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), e₁ D (m.pull1 c) = cmp1 D.s c) ∧
    ∀ (D D' : Data) (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (h : φ ≫ D.s = D'.s ≫ spMap σ)
      (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ →
      (∀ c, IsPull1 h (e₁ D c) (e₁ D' (m.pull1 c))) ∧ ∀ c, IsPull2 h (e₂ D c) (e₂ D' (m.pull2 c))

theorem CrystallineSmoothLift.bijective_cechDeRhamComparison_degreeOne (H : CrystallineSmoothLift) {R : Type} [CommRing R] {X : Scheme.{0}}
    (s : X ⟶ Sp R) (hs : Smooth s) (hs' : IsSeparated s) (hs'' : QuasiCompact s) : Function.Bijective (cmp1 s) := by
  obtain ⟨e₁, -, -, h, -⟩ := H
  have k : ∀ c, e₁ (Data.self s hs hs' hs'') c = cmp1 s c := fun c ↦
    (congrArg _ ((IsMor.id (dp0 R) s).pullCohomologyOne_id c)).symm.trans (h (Data.self s hs hs' hs'') (IsMor.id _ s) c)
  exact (funext k : _ = ⇑(cmp1 s)) ▸ (e₁ (Data.self s hs hs' hs'')).bijective

theorem CrystallineSmoothLift.toCrystallineDeRham (H : CrystallineSmoothLift) : CrystallineDeRham := by
  intro R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hs' hs'' hp m
  have b := H.bijective_cechDeRhamComparison_degreeOne s hs hs' hs''
  obtain ⟨e₁, e₂, -, h, n⟩ := H
  let D := Data.ofQuot κ hκ π hπ hI s s₀ i hs hs' hs'' hp _ rfl
  let D₀ := Data.self s hs hs' hs''
  have w : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by rw [Cris.spMap_id]; simp
  constructor
  · have : ⇑(e₁ D) ∘ ⇑m.pull1 = ⇑(cmp1 s) := funext (h D m)
    exact (Function.Bijective.of_comp_iff' (e₁ D).bijective _).1 (this ▸ b)
  · have k := (n D₀ D (RingHom.id R) (𝟙 X) i w m rfl).2
    have : ⇑(e₂ D) ∘ ⇑m.pull2 = ⇑(e₂ D₀) := funext fun c ↦
      pairRes2_id_injective s ((k c).symm.trans (isPull2_id w _))
    exact (Function.Bijective.of_comp_iff' (e₂ D).bijective _).1 (this ▸ (e₂ D₀).bijective)

end GlobalTheory.Published
