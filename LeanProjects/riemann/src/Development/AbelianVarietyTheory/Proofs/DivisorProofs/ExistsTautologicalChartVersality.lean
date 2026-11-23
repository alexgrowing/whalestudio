import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFractionRingMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyIsPointRigidTautologicalChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem spMap_isDominant_of_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : IsDominant (spMap f) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hf]
    exact bot_le)⟩

theorem spMap_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] {S : Scheme.{0}} [S.IsSeparated]
    (f : A →+* B) (hf : Function.Injective f) {a b : Sp A ⟶ S} (h : spMap f ≫ a = spMap f ≫ b) : a = b := by
  haveI := spMap_isDominant_of_injective f hf
  exact ext_of_isDominant_of_isSeparated (terminal.from S) (terminal.hom_ext _ _) (spMap f) h

theorem isSeparated_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    X.IsSeparated := by
  obtain ⟨N, ci, hci, hcis⟩ := h
  haveI := hci
  have : IsSeparated f := by
    rw [← hcis, PSpace.str]
    infer_instance
  exact ⟨by rw [← terminal.comp_from f]; infer_instance⟩

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem exists_taut_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), Nontrivial C.P.D.toPre.X → C.y ≫ j = jK V ≫ ξV → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S) (θ : ChartRing k m e →+* V), IsTautB C₁ ∧ C₁.y ≫ j = jK _ ≫ ξ ∧ IsLocalHom θ ∧ spMap θ ≫ ξ = ξV := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hSep V _ _ _ hB hac C ξV hnt hCV
  obtain ⟨k, hk, m, e, C₁, θ, ⟨hcan⟩, hpar, hθ, hthr⟩ := GlobalTheory.T.exists_canonical_family_through_degenerating_family Xo c φ V hB hac C hnt
  letI := hk
  have hT : IsTautB C₁ := GlobalTheory.T.canonicalFamily_isPointRigid_tautologicalChart Xo c φ hpq hpf hns C₁ hcan hpar
  obtain ⟨ξ, hξ⟩ := GlobalTheory.UChart.taut_exists_map Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hSep C₁ hT.1
  haveI : S.IsSeparated := isSeparated_of_projOver hU.2.2.2.2.1.2.1
  refine ⟨k, hk, m, e, C₁, ξ, θ, hT, hξ, hθ, ?_⟩
  obtain ⟨yo, κ, hgen, hκ, hκy⟩ := hthr

  obtain ⟨hm, hs⟩ := hpar
  have hne : (∏ i, C₁.s i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [hs i]
    exact bdParam_ne_zero k m e _
  set L := Localization.Away (∏ i, C₁.s i)
  have hle : Submonoid.powers (∏ i, C₁.s i) ≤ nonZeroDivisors (ChartRing k m e) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hne
  haveI : IsDomain L := IsLocalization.isDomain_localization hle
  have hu : IsUnit (algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) (∏ i, C₁.s i)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hne)
  let gR : L →+* FractionRing (ChartRing k m e) := IsLocalization.Away.lift (∏ i, C₁.s i) hu
  have hgR : gR.comp (algebraMap (ChartRing k m e) L) = algebraMap (ChartRing k m e) (FractionRing (ChartRing k m e)) :=
    IsLocalization.Away.lift_comp (∏ i, C₁.s i) hu
  have hinj : Function.Injective gR := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    rw [(IsLocalization.injective L hle).eq_iff, (IsFractionRing.injective (ChartRing k m e) (FractionRing (ChartRing k m e))).eq_iff]
  have hg : spMap gR ≫ spMap (algebraMap (ChartRing k m e) L) = jK (ChartRing k m e) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hgR]

  have hopen : spMap (algebraMap (ChartRing k m e) L) ≫ ξ = yo ≫ j := by
    refine spMap_ext_of_injective gR hinj ?_
    rw [← Category.assoc, hg, ← hξ, ← Category.assoc, hgen _ hg]
  refine spMap_ext_of_injective (algebraMap V (FractionRing V)) (IsFractionRing.injective _ _) ?_
  change jK V ≫ _ = jK V ≫ _
  rw [← Category.assoc, ← hκ, Category.assoc, hopen, ← Category.assoc, hκy, hCV]

end GlobalTheory.UCanon
