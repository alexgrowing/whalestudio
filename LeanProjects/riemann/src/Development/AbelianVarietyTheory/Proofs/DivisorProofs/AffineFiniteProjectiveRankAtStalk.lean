import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NatCastNeZeroOfIsUnit
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AbelianMulFin

theorem affine_finite_projective_rankAtStalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (r : ℕ) (hr : ∀ y, f.finrank y = r) (V : Y.Opens)
    (hV : IsAffineOpen V) :
    letI := (f.app V).hom.toAlgebra
    Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      Module.Projective Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      ∀ p : PrimeSpectrum Γ(Y, V), Module.rankAtStalk Γ(X, f ⁻¹ᵁ V) p = r := by
  letI := (f.app V).hom.toAlgebra
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have h1 : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  have h2 : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have := f.flat_appLE hV hU le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  have h3 : Algebra.FinitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := by
    have := f.finitePresentation_appLE hV hU le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  have h4 := Module.FinitePresentation.of_finite_of_finitePresentation Γ(Y, V) Γ(X, f ⁻¹ᵁ V)
  refine ⟨h1, h2, Module.Flat.projective_of_finitePresentation, fun p => ?_⟩
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ (GlobalTheory.isPullback_fromSpec_app f hV hU) p
  rw [hr] at e
  exact (Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V) p).symm.trans e

theorem isUnit_natCast_Sp {K : Type} [Field K] {n : ℕ} (hn : (n : K) ≠ 0) :
    IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
  have := (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  rwa [map_natCast] at this

end GlobalTheory.AbelianMulFin

namespace GlobalTheory.AbelianMulFin

theorem natCast_card_torsion_ne_zero {K : Type} [Field K] {G : Type} [CommGroup G] {n r : ℕ}
    (hn : (n : K) ≠ 0) (hr1 : 1 ≤ r) (hr : r = Nat.card {y : G // y ^ n = 1}) : (r : K) ≠ 0 := by
  intro hr0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · haveI := Fact.mk hp
    have hdvd : ringChar K ∣ r := (CharP.cast_eq_zero_iff K (ringChar K) r).1 hr0
    let H : Subgroup G := (powMonoidHom n : G →* G).ker
    have hHc : Nat.card {y : G // y ^ n = 1} = Nat.card H :=
      Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H, MonoidHom.mem_ker])
    rw [hr, hHc] at hdvd
    have hpos : Nat.card H ≠ 0 := by rw [← hHc, ← hr]; omega
    haveI : Finite H := Nat.finite_of_card_ne_zero hpos
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hdvd
    have hx2 : (x : G) ^ n = 1 := x.2
    have hxn : x ^ n = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hx2]; rfl)
    have hd : ringChar K ∣ n := hx ▸ orderOf_dvd_of_pow_eq_one hxn
    exact hn ((CharP.cast_eq_zero_iff K (ringChar K) n).2 hd)
  · have : CharP K 0 := hp ▸ ringChar.charP K
    haveI := CharP.charP_to_charZero K
    exact (Nat.cast_ne_zero.2 (by omega)) hr0

theorem mulA_finite_locallyFree (K : Type) [Field K] [IsAlgClosed K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [hA : IsAbelianScheme A] (n : ℕ)
    (hn : (n : K) ≠ 0) :
    IsFinite (mulA A n).left ∧ Flat (mulA A n).left ∧ Etale (mulA A n).left ∧
      ∃ r : ℕ, (r : K) ≠ 0 ∧ 1 ≤ r ∧ (∀ a : A.left, (mulA A n).left.finrank a = r) ∧
        ∀ V : A.left.Opens, IsAffineOpen V →
          letI := ((mulA A n).left.app V).hom.toAlgebra
          Module.Finite Γ(A.left, V) Γ(A.left, (mulA A n).left ⁻¹ᵁ V) ∧
          Module.Flat Γ(A.left, V) Γ(A.left, (mulA A n).left ⁻¹ᵁ V) ∧
          Module.Projective Γ(A.left, V) Γ(A.left, (mulA A n).left ⁻¹ᵁ V) ∧
          ∀ p : PrimeSpectrum Γ(A.left, V),
            Module.rankAtStalk Γ(A.left, (mulA A n).left ⁻¹ᵁ V) p = r := by
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  obtain ⟨⟨hfin, het⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (isUnit_natCast_Sp hn)
  rw [← GlobalTheory.MulLawsCompare.mulN_eq_mulA]
  haveI := hfin
  haveI := het
  haveI : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  let z₀ : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let o : A.left := η[A].left z₀
  have hη : η[A] ≫ mulN A n = η[A] := by
    rw [GlobalTheory.MulLawsCompare.mulN_eq_mulA]
    haveI := GlobalTheory.AbLaw.MulN.isMonHom_mulA A n
    exact IsMonHom.one_hom (mulA A n)
  have hfo : (mulN A n).left o = o := by
    change (η[A].left ≫ (mulN A n).left) z₀ = _
    rw [← Over.comp_left, hη]
  set r := (mulN A n).left.finrank o with hr_def
  have hall : ∀ a, (mulN A n).left.finrank a = r := fun a =>
    (Scheme.Hom.isLocallyConstant_finrank (mulN A n).left).apply_eq_of_preconnectedSpace a o
  have hr1 : 1 ≤ r := by
    have := Scheme.Hom.one_le_finrank_map (mulN A n).left o
    rwa [hfo] at this
  haveI hsurj : Surjective (mulN A n).left :=
    (Scheme.Hom.one_le_finrank_iff_surjective (mulN A n).left).1 fun a => by
      show 1 ≤ (mulN A n).left.finrank a
      rw [hall a]; exact hr1
  have hcard := GlobalTheory.MulLawsCompare.finrank_mulN_eq_card A n (η[A].left) z₀
  refine ⟨hfin, inferInstance, het, r, natCast_card_torsion_ne_zero hn hr1 hcard, hr1, hall,
    fun V hV => affine_finite_projective_rankAtStalk _ r hall V hV⟩

end GlobalTheory.AbelianMulFin
