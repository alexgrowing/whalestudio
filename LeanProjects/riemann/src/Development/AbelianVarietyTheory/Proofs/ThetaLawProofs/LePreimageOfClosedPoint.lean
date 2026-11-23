import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.FormalChart

section Alg

variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] {g : ℕ}

theorem ext_of_isHausdorff (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra O A] (J : Ideal A) [IsHausdorff J A] (φ₁ φ₂ : B →ₐ[O] A)
    (h : ∀ b, φ₁ b - φ₂ b ∈ J)
    (hs : ∀ j : Fin g, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have hJ : ⨅ i, J ^ i = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => by
      rw [sub_zero]
      exact Ideal.mem_iInf.1 hx n
  have : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext_of_iInf J hJ fun b => Ideal.Quotient.eq.2 (h b)
  ext x
  exact AlgHom.congr_fun this x

theorem exists_expansion (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) :
    ∃ φ : B →ₐ[O] MvPowerSeries (Fin g) O, (∀ b, MvPowerSeries.constantCoeff (φ b) = e b) ∧
      ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let A := MvPowerSeries (Fin g) O
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A :=
    MvPolynomial.aeval (fun j => algebraMap O A (e (π (MvPolynomial.X j))) + MvPowerSeries.X j)
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
  have hf₀ : ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).comp π =
      (Ideal.Quotient.mkₐ O J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X, Algebra.ofId_apply]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin g) O] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  obtain ⟨φ', hφ'⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f₀
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  let φ : B →ₐ[O] A := { φ'.toRingHom with
    commutes' := fun r => by
      show φ' (algebraMap O B r) = _
      rw [← π.commutes, hc, ρ.commutes] }
  have hφ : ∀ b, φ b = φ' b := fun _ => rfl
  have hJ : J ≤ RingHom.ker (MvPowerSeries.constantCoeff) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i
  refine ⟨φ, fun b => ?_, fun j => ?_⟩
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (algebraMap O A (e b)) :=
      AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    have e2 := hJ e1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e2
    exact e2.trans (MvPowerSeries.constantCoeff_C _)
  · rw [map_sub, AlgHom.commutes, hφ, hc]
    simp [ρ]

theorem exists_factor (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) (φ : B →ₐ[O] MvPowerSeries (Fin g) O)
    (h₁ : ∀ b, MvPowerSeries.constantCoeff (φ b) = e b)
    (h₂ : ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j)
    {T : Type} [CommRing T] [Algebra O T] (J : Ideal T) [IsAdicComplete J T] (ψ : B →ₐ[O] T)
    (hψ : ∀ b, ψ b - algebraMap O T (e b) ∈ J) :
    ∃ v : MvPowerSeries (Fin g) O →ₐ[O] T, (∀ i, v (MvPowerSeries.X i) ∈ J) ∧ v.comp φ = ψ := by
  let v := GlobalTheory.mvEvalAdic O J (fun j => ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))))
    (fun j => hψ _)
  have hv : ∀ j, v (MvPowerSeries.X j) =
      ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))) := fun j =>
    GlobalTheory.mvEvalAdic_X _ _ _ j
  have hv' : ∀ j, v (MvPowerSeries.X j) ∈ J := fun j => hv j ▸ hψ _
  refine ⟨v, hv', ext_of_isHausdorff π hπ J _ _ (fun b => ?_) (fun j => ?_)⟩
  · have := GlobalTheory.algHom_sub_constantCoeff_mem v hv' (φ b)
    rw [h₁] at this
    have h3 := sub_mem this (hψ b)
    rwa [sub_sub_sub_cancel_right] at h3
  · have := hv j
    rw [← h₂, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this
    exact this

end Alg

section Geo
open GlobalTheory.KeyKa.EtBaseChange

variable {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {T : Type} [CommRing T]

theorem spMap_valH (w : Sp T ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    spMap (R := Γ(X, V)) (valH w V hw) ≫ hV.fromSpec = w := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec w hV (isAffineOpen_top (Spec (CommRingCat.of T))) hw
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  show Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ hV.fromSpec = w
  rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem le_preimage (φ : Γ(X, V) →+* T) : ⊤ ≤ (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) ⁻¹ᵁ V :=
  fun _ _ => hV.range_fromSpec.subset (Set.mem_range_self _)

theorem valH_spMap (φ : Γ(X, V) →+* T) :
    valH (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) V (le_preimage hV φ) = φ := by
  have h := spMap_valH hV _ (le_preimage hV φ)
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem fromSpec_comp {O : Type} [CommRing O] (h : X ⟶ Sp O) :
    hV.fromSpec ≫ h = spMap (R' := Γ(X, V))
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top (Spec (CommRingCat.of O))) hV
    (le_top : V ≤ h ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [← e, ← Spec.map_comp]
  rfl

theorem le_preimage_of_closedPoint [IsLocalRing T] (w : Sp T ⟶ X)
    (hw : w (IsLocalRing.closedPoint T) ∈ V) : ⊤ ≤ w ⁻¹ᵁ V := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open V.isOpen hw

end Geo

open GlobalTheory.KeyKa.EtBaseChange in

theorem exists_formal_chart : ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0}) (h : X ⟶ Sp O) (g : ℕ) (z : Sp O ⟶ X), SmoothOfRelativeDimension g h → z ≫ h = 𝟙 _ → ∃ θ : Sp (MvPowerSeries (Fin g) O) ⟶ X, θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) = z (IsLocalRing.closedPoint O) ∧ θ ≫ h = spMap (algebraMap O (MvPowerSeries (Fin g) O)) ∧ (∃ (V : X.Opens) (t : Fin g → Γ(X, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin g) O)) θ V (t i) = MvPowerSeries.X i) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ X), w ≫ h = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) → ∃ e : (MvPowerSeries (Fin g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) := by
  intro O _ _ X h g z hG hz
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (z (IsLocalRing.closedPoint O))
  have hU' : U = ⊤ := by
    have h1 : (z ≫ h) (IsLocalRing.closedPoint O) ∈ U :=
      (Scheme.Hom.comp_apply z h (IsLocalRing.closedPoint O)).symm ▸ e hx
    have h2 := le_preimage_of_closedPoint (z ≫ h) h1
    rw [hz] at h2
    exact eq_top_iff.2 h2
  subst hU'
  let a : O →+* Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom
  have ha : hV.fromSpec ≫ h = spMap (R' := Γ(X, V)) a := fromSpec_comp hV h
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g a :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv hs
  obtain ⟨π₀, hπ1, hπ⟩ := h2.exists_etale_mvPolynomial
  clear_value a
  letI : Algebra O Γ(X, V) := a.toAlgebra
  let π : MvPolynomial (Fin g) O →ₐ[O] Γ(X, V) := { π₀ with commutes' := fun r => RingHom.congr_fun hπ1 r }
  have hpt : ∀ (T : Type) [CommRing T] [Algebra O T] (w : Sp T ⟶ X), ⊤ ≤ w ⁻¹ᵁ V →
      w ≫ h = spMap (algebraMap O T) →
      ∃ ψ : Γ(X, V) →ₐ[O] T, spMap (R := Γ(X, V)) ψ.toRingHom ≫ hV.fromSpec = w := by
    intro T _ _ w hw hw'
    have e1 := spMap_valH hV w hw
    have e2 : spMap ((valH w V hw).comp a) = spMap (algebraMap O T) := by
      rw [spMap_comp, ← ha, ← Category.assoc, e1, hw']
    have e3 : (valH w V hw).comp a = algebraMap O T :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    exact ⟨⟨valH w V hw, fun r => RingHom.congr_fun e3 r⟩, e1⟩
  obtain ⟨ε, rfl⟩ := hpt O z (le_preimage_of_closedPoint z hx) (hz.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_expansion π hπ ε
  have hcl : (spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec)
      (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) =
      (spMap (R := Γ(X, V)) ε.toRingHom ≫ hV.fromSpec) (IsLocalRing.closedPoint O) := by
    refine congrArg hV.fromSpec (PrimeSpectrum.ext (Ideal.ext fun b => ?_))
    show φ b ∈ IsLocalRing.maximalIdeal _ ↔ ε b ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, hφ₁]
  refine ⟨spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec, hcl, ?_,
    ⟨V, fun j => π (MvPolynomial.X j) - algebraMap O _ (ε (π (MvPolynomial.X j))), le_preimage hV _,
      fun j => ?_⟩, ?_⟩
  · rw [Category.assoc, ha, ← spMap_comp]
    exact congrArg spMap φ.comp_algebraMap
  · rw [valT_eq _ _ (le_preimage hV _), valH_spMap]
    exact hφ₂ j
  · intro T _ _ _ _ w hw hw'
    rw [hcl] at hw'
    obtain ⟨ψ, rfl⟩ := hpt T w (le_preimage_of_closedPoint w (hw' ▸ hx)) hw
    have h3 := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hw')
    obtain ⟨v, hv, rfl⟩ := exists_factor π hπ ε φ hφ₁ hφ₂ (IsLocalRing.maximalIdeal T) ψ fun b => by
      have h4 : b - algebraMap O _ (ε b) ∈ (IsLocalRing.maximalIdeal O).comap ε.toRingHom := by
        show ε (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal O
        simp
      have h5 : ψ (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal T := h3.ge h4
      rwa [map_sub, AlgHom.commutes] at h5
    refine ⟨v, hv, ?_⟩
    rw [← Category.assoc, ← spMap_comp]
    rfl

end GlobalTheory.FormalChart
