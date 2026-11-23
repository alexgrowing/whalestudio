import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FixedCx

open Cardinal

theorem mk_le_of_essFiniteType {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] :
    #S ≤ max #R ℵ₀ := by
  have h1 : #S ≤ #(Algebra.EssFiniteType.subalgebra R S) :=
    IsLocalization.cardinalMk_le (Algebra.EssFiniteType.submonoid R S)
  have h2 := Algebra.cardinalMk_adjoin_le R ((Algebra.EssFiniteType.finset R S : Finset S) : Set S)
  have h3 : #(((Algebra.EssFiniteType.finset R S : Finset S) : Set S)) ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite _).le
  refine h1.trans (h2.trans ?_)
  exact max_le (max_le (le_max_left _ _) (h3.trans (le_max_right _ _))) (le_max_right _ _)

theorem nonempty_ringHom_complex (K : Type) [Field K] [CharZero K] (h : #K ≤ 𝔠) : Nonempty (K →+* ℂ) := by
  have hP1 : #(MvPolynomial ℝ K) ≤ 𝔠 := MvPolynomial.cardinalMk_le_max.trans
    (max_le (max_le h (Cardinal.mk_real).le) Cardinal.aleph0_le_continuum)
  have hP2 : 𝔠 ≤ #(MvPolynomial ℝ K) := by
    rw [← Cardinal.mk_real]
    exact Cardinal.mk_le_of_injective (MvPolynomial.X_injective (σ := ℝ) (R := K))
  have hF : #(FractionRing (MvPolynomial ℝ K)) = 𝔠 := (FractionRing.cardinalMk (MvPolynomial ℝ K)).trans (le_antisymm hP1 hP2)
  haveI : CharZero (FractionRing (MvPolynomial ℝ K)) :=
    charZero_of_injective_ringHom (f := (algebraMap (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp MvPolynomial.C)
      ((IsFractionRing.injective (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp (MvPolynomial.C_injective ℝ K))
  haveI : CharZero (AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) := charZero_of_injective_ringHom (algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).injective
  have hΩ1 : #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) ≤ 𝔠 := (Algebra.IsAlgebraic.cardinalMk_le_max (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).trans
    (max_le hF.le Cardinal.aleph0_le_continuum)
  have hΩ2 : 𝔠 ≤ #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) := hF ▸ Cardinal.mk_le_of_injective (algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).injective
  have hΩ : #(AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) = #ℂ := (le_antisymm hΩ1 hΩ2).trans Cardinal.mk_complex.symm
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := AlgebraicClosure (FractionRing (MvPolynomial ℝ K))) (L := ℂ)
    (by rw [hΩ, Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 hΩ)
  exact ⟨e.toRingHom.comp ((algebraMap (FractionRing (MvPolynomial ℝ K)) (AlgebraicClosure (FractionRing (MvPolynomial ℝ K)))).comp ((algebraMap (MvPolynomial ℝ K) (FractionRing (MvPolynomial ℝ K))).comp MvPolynomial.C))⟩

theorem cancel_spec_field {K L : Type} [Field K] [Field L] (φ : L →+* K) {X : Scheme.{0}} (a b : Sp L ⟶ X)
    (h : spMap φ ≫ a = spMap φ ≫ b) : a = b := by
  obtain ⟨⟨p, α⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective a
  obtain ⟨⟨q, β⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  obtain ⟨e, he⟩ := GlobalTheory.SS.residue_embedding_unique _ _ h
  subst e
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp] at he
  have : α = β := by
    ext c
    exact φ.injective (congrArg (fun g => g.hom c) he)
  rw [this]

end GlobalTheory.FixedCx

open GlobalTheory.FixedCx Cardinal in

theorem GlobalTheory.FixedCx.exists_fixed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (k : Type) [Field k] (x : Sp k ⟶ Xo.X) (ρ : Xo.X ⟶ Xo.X), x ≫ ρ = x → ∃ x' : Sp ℂ ⟶ Xo.X, x' ≫ ρ = x' := by
  intro E _ _ _ H Dw l Xo k _ x ρ hx
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Xo.X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hι : Xo.X.fromSpecResidueField p ≫ ρ = Xo.X.fromSpecResidueField p :=
    cancel_spec_field φ.hom _ _ (by rw [Category.assoc] at hx; exact hx)
  haveI := Xo.smooth
  haveI := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Xo.X.fromSpecResidueField p ≫ Xo.s)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType Xo.s p ψ hψ
  letI : Algebra (KA l) (Xo.X.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType (KA l) (Xo.X.residueField p) := hess
  haveI : CharZero (KA l) := charZero_of_injective_ringHom (algebraMap ℚ (KA l)).injective
  haveI : CharZero (Xo.X.residueField p) := charZero_of_injective_ringHom ψ.hom.injective
  have hK : #(KA l) ≤ 𝔠 := (Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le
  have hc : #(Xo.X.residueField p) ≤ 𝔠 :=
    mk_le_of_essFiniteType.trans (max_le hK Cardinal.aleph0_le_continuum)
  obtain ⟨j⟩ := nonempty_ringHom_complex (Xo.X.residueField p) hc
  exact ⟨Spec.map (CommRingCat.ofHom j) ≫ Xo.X.fromSpecResidueField p, by rw [Category.assoc, hι]⟩
