import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UniformisedModel

theorem exists_finite_factor {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {p : ℕ} [Fact p.Prime]
    (y₀ : R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (y : R →+* K),
      (∀ a, (y a : PadicAlgCl p) = y₀ a) ∧ ∀ x ∈ Fs, x ∈ K := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  let t : Finset (PadicAlgCl p) := s.image y₀ ∪ Fs
  let K := IntermediateField.adjoin ℚ_[p] (t : Set (PadicAlgCl p))
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hy : ∀ a, y₀ a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _
        (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))
    | algebraMap n => rw [eq_intCast, map_intCast]; exact intCast_mem K n
    | add a b _ _ ha hb => rw [map_add]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  exact ⟨K, hK, y₀.codRestrict K hy, fun _ => rfl, fun x hx =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_union_right _ hx))⟩

theorem spMap_spMap {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_polBaseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ ∧ LBIso P'.L (P.L.pull φ) := by
  obtain ⟨P', φ, hφ, -, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ.w y), ← hm]
  rfl

theorem exists_isGrpPullback_jK {V K R : Type} [CommRing V] [IsDomain V] [CommRing K] [CommRing R] (a : V →+* K)
    (b : K →+* FractionRing V) (e : b.comp a = algebraMap V (FractionRing V)) (u : R →+* K)
    (G : Over (Sp V)) [GrpObj G] (A : Over (Sp R)) [GrpObj A] {φ : pullback G.hom (spMap a) ⟶ A.left}
    (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ, IsGrpPullback ((Over.pullback (jK V)).obj G) A (spMap (b.comp u)) ψ := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V))
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_spMap, e]) rfl)
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_spMap]) rfl⟩

end GlobalTheory.UniformisedModel

namespace GlobalTheory

open UniformisedModel in

theorem exists_uniformised_model : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  intro hN hU hB o Ω _ _ _ _ S ρ p _ y₀ Fs
  haveI := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType S.R).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  obtain ⟨K, _, y, hy, hFs⟩ := exists_finite_factor y₀ Fs
  obtain ⟨P, φ₀, hφ₀, -⟩ := exists_polBaseChange hB (spMap y) ρ.P
  obtain ⟨K', h, _, _, G, _, hG, hE, φ, hφ⟩ := exists_semiAbelian_model_split_specialFibre hN p K P
  let V := integralClosure ℤ_[p] K'
  let e : FractionRing V ≃ₐ[V] K' := FractionRing.algEquiv V K'
  let y' : S.R →+* K' := (IntermediateField.inclusion h).toRingHom.comp y
  let b : K' →+* FractionRing V := e.symm.toRingEquiv.toRingHom
  have hb : b.comp (algebraMap V K') = algebraMap V (FractionRing V) := RingHom.ext fun x => e.symm.commutes x
  obtain ⟨ψ, hψ⟩ := exists_isGrpPullback_jK (algebraMap V K') b hb y' G ρ.P.A
    ((hφ.comp hφ₀).congr (spMap_spMap _ _) rfl)
  obtain ⟨A, χ, hχ, hL⟩ := exists_polBaseChange hB (spMap (b.comp y')) ρ.P
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso hψ hχ
  haveI : CharZero V := charZero_integralClosure_padicInt
  haveI := hG.comm
  have hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V :=
    CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] V
  obtain ⟨D, U, -⟩ := hU V hc A G hG hE
    (SymBaseChange.hypS_baseChange _ _ ρ.P.A A.A _ χ ρ.P.L A.L ρ.P.isLB A.isLB hχ hL ρ.hypS) gen hgen
  let c : FractionRing V →+* PadicAlgCl p := (algebraMap K' (PadicAlgCl p)).comp e.toRingEquiv.toRingHom
  have hcb : ∀ x : K', c (b x) = x := fun x => congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨{ V := V, complete := hc, alg := c.toAlgebra, norm_le := fun x => ?_, yK := b.comp y'
            fac := RingHom.ext fun a => (hcb (y' a)).trans (hy a), A := A, φ := χ, cart := hχ, lb := hL, G := G
            semi := hG, D := D, U := U }, fun x hx => ⟨b ⟨x, h (hFs x hx)⟩, hcb _⟩⟩
  refine (mem_integralClosure_padicInt_iff K' (e x)).symm.trans ⟨fun hx => ⟨⟨e x, hx⟩, ?_⟩, ?_⟩
  · exact e.injective (e.commutes _)
  · rintro ⟨v, rfl⟩
    rw [e.commutes]
    exact v.2

end GlobalTheory
