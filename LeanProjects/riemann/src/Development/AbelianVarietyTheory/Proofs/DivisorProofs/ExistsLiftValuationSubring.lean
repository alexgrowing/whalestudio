import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorEnd

theorem exists_lift_valuationSubring {F : Type} [Field F] (O : ValuationSubring F) {M : Type} [CommGroup M]
    (τ : M →* Fˣ) {k : ℕ} (hk : k ≠ 0) (hτ : τ ^ k = 1) :
    ∃ σ : M →* Oˣ, σ ^ k = 1 ∧ ∀ x, ((σ x : O) : F) = τ x := by
  have hp : ∀ x, (τ x : F) ^ k = 1 := fun x => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply, Units.val_one]
  have hm : ∀ x, (τ x : F) ∈ O := fun x => by
    rw [← O.valuation_le_one_iff]
    have := congrArg O.valuation (hp x)
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hk).1 this).le
  let σ₀ : M →* O :=
    { toFun := fun x => ⟨τ x, hm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨σ₀.toHomUnits, MonoidHom.ext fun x => Units.ext (Subtype.ext ?_), fun x => rfl⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  exact hp x

theorem chV_comp_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z : Over S}
    (z : Z ⟶ splitTorus S X) (m : Y →+ X) (χ : Y) :
    GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap S m) χ = GlobalTheory.UU.chV z (m χ) := by
  refine Units.ext ?_
  rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
    ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]

theorem torMatch_of_endChar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G), IsMonHom f → ∀ m, EndChar U f m → TorMatch U U (RingHom.id R) f.left m := by
  intro R _ _ _ hR G _ _ hG D A U f hf m hm F _ _ i₁ i₂ hi k hk τ τ' q q' x x' hτ' hτ hq hqt hq' hqt' hx hx'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨s, s₁, s₂, s₃, s₄⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k (Nat.one_le_iff_ne_zero.2 hk0)
  let a : R →+* F := (@algebraMap (FractionRing R) F _ _ i₁).comp (algebraMap R (FractionRing R))
  have ha₂ : a = (@algebraMap (FractionRing R) F _ _ i₂).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => hi r
  let ν : Multiplicative D.toPre.X →* Multiplicative D.toPre.X := AddMonoidHom.toMultiplicative m
  have pw : ∀ {B : Type} [CommRing B] (σ : Multiplicative D.toPre.X →* Bˣ), σ ^ k = 1 → σ.comp ν ^ k = 1 :=
    fun σ h => MonoidHom.ext fun χ => DFunLike.congr_fun h (ν χ)
  obtain rfl : τ = τ'.comp ν := MonoidHom.ext fun χ => hτ χ.toAdd
  have e₁ := @s₄ F _ _ i₁ a _ (pw τ' hτ') q x rfl hq hqt hx
  have e₂ := @s₄ F _ _ i₂ a _ hτ' q' x' ha₂ hq' hqt' hx'
  rw [e₁, reassoc_of% e₂]
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing a
  let c : R →+* O := a.codRestrict O.toSubring hO
  have hc : IsLocalHom c := hloc
  obtain ⟨σ, hσ, hστ⟩ := exists_lift_valuationSubring O τ' hk0 hτ'
  have n₁ := s₂ O F c a O.subtype _ (pw σ hσ) _ (pw τ' hτ') rfl fun χ => (hστ (ν χ)).symm
  have n₂ := s₂ O F c a O.subtype _ hσ _ hτ' rfl fun χ => (hστ χ).symm
  suffices key : s O c _ (pw σ hσ) = s O c σ hσ ≫ f by
    rw [n₁, n₂, key, Over.comp_left, Category.assoc]
  have hkO : IsUnit (k : O) := by simpa using hk.map c
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap c) k hkO _ _ ?_
    (ResidueField O) (residue O) inferInstance ?_
  · rw [s₁, ← MonObj.pow_comp, s₁, MonObj.one_comp]
  let a₀ : R →+* ResidueField O := (residue O).comp c
  have ha₀ : ∀ r ∈ maximalIdeal R ^ (0 + 1), a₀ r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (residue_eq_zero_iff _).2 (map_nonunit c r hr)
  let σ₀ : Multiplicative D.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp σ
  have hσ₀ : σ₀ ^ k = 1 := MonoidHom.ext fun χ => by
    have := DFunLike.congr_fun hσ χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    simp only [σ₀, MonoidHom.comp_apply, ← map_pow, this, map_one]
  have r₁ := s₂ O _ c a₀ (residue O) _ (pw σ hσ) _ (pw σ₀ hσ₀) rfl fun χ => rfl
  have r₂ := s₂ O _ c a₀ (residue O) _ hσ _ hσ₀ rfl fun χ => rfl
  have h₀ := isGrpPullback_pullback G (spMap a₀)
  let z : Over.mk (spMap (RingHom.id (ResidueField O))) ⟶ splitTorus (Sp (ResidueField O)) D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp σ₀)
  have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (σ₀ (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
    rfl
  have t₁ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ (pw σ₀ hσ₀) (z ≫ GlobalTheory.SplitTorus.torusMap _ m) rfl
    fun χ => (chV_comp_torusMap z m χ).trans (hz _)
  have t₂ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ hσ₀ z rfl hz
  have hf₀ : ((Over.pullback (spMap a₀)).map f).left ≫ pullback.fst G.hom (spMap a₀) =
      pullback.fst G.hom (spMap a₀) ≫ f.left := pullback.lift_fst _ _ _
  have hE := hm _ a₀ ha₀ _ _ h₀ _ hf₀
  rw [Over.comp_left, ← r₁, ← reassoc_of% r₂, t₁, t₂, Category.assoc z, ← hE, Category.assoc, ← hf₀]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.TorEnd

end
