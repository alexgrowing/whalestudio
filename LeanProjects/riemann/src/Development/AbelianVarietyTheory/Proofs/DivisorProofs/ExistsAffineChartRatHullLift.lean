import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCompactificationGenericSubsetModuli
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points

namespace GlobalTheory.UPoinc.ChartAt

theorem isUnit_map_of_ne_zero {o R : Type} [CommRing o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [CommRing R]
    (hR : ∀ n : ℤ, n ≠ 0 → IsUnit (n : R)) (φ : o →+* R) {a : o} (ha : a ≠ 0) : IsUnit (φ a) := by
  by_contra h
  obtain ⟨m, hm, ham⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 h)
  letI := Ideal.Quotient.field m
  haveI : CharZero (R ⧸ m) := charZero_of_inj_zero fun n hn => by
    by_contra h0
    have hu := (hR n (by exact_mod_cast h0)).map (Ideal.Quotient.mk m)
    exact hu.ne_zero (by simpa using hn)
  have hk := ker_eq_bot_of_charZero ((Ideal.Quotient.mk m).comp φ)
  have : a ∈ RingHom.ker ((Ideal.Quotient.mk m).comp φ) := Ideal.Quotient.eq_zero_iff_mem.2 ham
  rw [hk] at this
  exact ha this

theorem exists_affine_chart_ratHull_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (w₀ : X.M.Z), X.π w₀ ∈ Set.range C.i → ∃ (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf), IsAffineOpen U₀ ∧ w₀ ∈ U₀ ∧ spMap (ratHull (X.M.ringOn U₀)).val.toRingHom ≫ u₀ = X.uΩ := by
  intro E _ _ _ H Dw _ l Xo cf C X w hw
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.iF_open
  haveI := C.ded
  haveI := C.ft
  haveI := C.isPreimmersion_i
  haveI : CharZero X.Ω₁ := by
    obtain ⟨t, -⟩ := Spec.map_surjective (X.uΩ ≫ pullback.snd _ _)
    exact (RingHom.charZero_iff (R := cf.F) t.hom.injective).1 inferInstance
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hg : Topology.IsEmbedding (pullback.fst C.z (spMap C.b) :) := (pullback.fst C.z (spMap C.b)).isEmbedding
  obtain ⟨V, hV, hVe⟩ := hg.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ X.π ⁻¹ᵁ ⟨V, hV⟩ := by
    obtain ⟨x, hx⟩ := hw
    have : C.iF x ∈ (pullback.fst C.z (spMap C.b) :) ⁻¹' V := hVe ▸ ⟨x, rfl⟩
    show X.π w ∈ V
    rw [← hx]
    exact this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X.M.Z) hwV
  have hne : ((U : X.M.Z.Opens) : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  let φ : Γ(X.M.Z, U) ⟶ CommRingCat.of (ratHull (X.M.ringOn U)) :=
    CommRingCat.ofHom ((toRat (X.M.ringOn U)).comp (X.M.sectionsEquiv U hne).toRingHom)
  let f : Sp (ratHull (X.M.ringOn U)) ⟶ X.M.Z := Spec.map φ ≫ hU.fromSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (f ≫ X.π ≫ C.z)
  have hu : ∀ a : nonZeroDivisors C.o, IsUnit (ψ.hom a) := fun a =>
    isUnit_map_of_ne_zero (fun n hn => isUnit_intCast_ratHull _ hn) ψ.hom (nonZeroDivisors.ne_zero a.2)
  let χ : cf.F →+* ratHull (X.M.ringOn U) := IsLocalization.lift (M := nonZeroDivisors C.o) hu
  have hχ : (f ≫ X.π) ≫ C.z = spMap χ ≫ spMap C.b := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun t => spMap t) (IsLocalization.lift_comp (M := nonZeroDivisors C.o) hu).symm
  let g := pullback.lift _ _ hχ
  have hgf : g ≫ pullback.fst _ _ = f ≫ X.π := pullback.lift_fst _ _ _
  have hrange : Set.range g ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hVe]
    show (g ≫ pullback.fst C.z (spMap C.b)) y ∈ V
    rw [hgf]
    have : hU.fromSpec (Spec.map φ y) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at this
    exact hUV this
  refine ⟨U, IsOpenImmersion.lift C.iF g hrange, hU, hwU, ?_⟩
  rw [← cancel_mono C.i, Category.assoc, Category.assoc, ← X.comp, UCompact.i, IsOpenImmersion.lift_fac_assoc, hgf]
  have hpt : ⊤ ≤ X.M.pt ⁻¹ᵁ U := X.M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom (ratHull (X.M.ringOn U)).val.toRingHom = valMap X.M.pt U hpt := by
    ext a
    show ((X.M.sectionsEquiv U hne a : X.M.ringOn U) : X.Ω₁) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ f = X.M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  rw [← hf]
  simp only [Category.assoc]

end GlobalTheory.UPoinc.ChartAt
