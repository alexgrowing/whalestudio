import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem torAt_of_closedPoint : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (β : G.left ⟶ H.left), IsGrpPullback G H ξ β → ∀ (σ : Sp V ⟶ H.left), σ ≫ H.hom = ξ → ∀ (k : ℕ) (w : V), 1 ≤ k → IsUnit (k : V) → w ^ k = 1 → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (c : D.toPre.X →+ ℤ) (x : TFK (R := V) F ⟶ A.A), x ^ k = 1 → x.left ≫ genMap U ≫ β = spMap (algebraMap (FractionRing V) F) ≫ jK V ≫ σ → ∀ (κ : Type) [Field κ] (b : V →+* κ) (hb : ∀ y ∈ maximalIdeal V ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G.left) (hm : IsGrpPullback Gκ G (spMap b) m) (τ : Multiplicative D.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b w ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ σ = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb hm).left ≫ m ≫ β → TorAt U F k (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) w)) c x := by
  intro B H _ V _ _ _ hV G _ _ hG D A U ξ β hβ σ hσ k w hk hkV hw F _ _ _ c x hx hxσ κ _ b hb Gκ _ m hm τ hτ z hz hbσ
  haveI : CharZero V := hV.2
  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := Spec.map_id _
  let σ₀ : Sp V ⟶ G.left := hβ.1.lift σ (𝟙 _) (hσ.trans (Category.id_comp _).symm)
  have hσ₀ : σ₀ ≫ β = σ := hβ.1.lift_fst _ _ _
  have hσ₀' : σ₀ ≫ G.hom = 𝟙 _ := hβ.1.lift_snd _ _ _
  let σ₁ : Over.mk (spMap (RingHom.id V)) ⟶ G := Over.homMk σ₀ (hσ₀'.trans hid.symm)
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.ToricTorsionUnif.main V hV G hG D A U k hk
  have hwu : IsUnit w := IsUnit.of_pow_eq_one hw (by omega)
  obtain ⟨u, rfl⟩ := hwu
  have hu : u ^ k = 1 := Units.ext (by simpa using hw)
  let τV : Multiplicative D.toPre.X →* Vˣ := (zpowersHom Vˣ u).comp (AddMonoidHom.toMultiplicative c)
  have hτV' : ∀ χ, τV χ = u ^ c (Multiplicative.toAdd χ) := fun χ => rfl
  have hτV : τV ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply, hτV', ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]; rfl
  have hval : ∀ (L : Type) [Field L] (f : V →+* L) (n : ℤ), f ((u ^ n : Vˣ) : V) = f u ^ n := fun L _ f n => by
    have := congrArg Units.val (map_zpow (Units.map (f : V →* L)) u n)
    rw [Units.val_zpow_eq_zpow_val] at this
    exact this
  let a : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have ha : spMap a = spMap (algebraMap (FractionRing V) F) ≫ jK V := GlobalTheory.ToricTorsionSec.spMap_comp _ _
  have hainj : Function.Injective a :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK V)).obj G) (𝟙 _) U.gen.inv.left :=
    isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK V)
  have hp : IsGrpPullback A.A G (jK V) (genMap U) := (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hp (TFK (R := V) F) (spMap a) ha
  let ρ : Over.mk (spMap a) ⟶ Over.mk (spMap (RingHom.id V)) :=
    Over.homMk (spMap a) (by show spMap a ≫ spMap (RingHom.id V) = spMap a; rw [hid, Category.comp_id])
  have hex : e x = ρ ≫ σ₁ := by
    refine Over.OverMorphism.ext (hβ.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [he]
    show (x.left ≫ genMap U) ≫ β = (spMap a ≫ σ₀) ≫ β
    rw [Category.assoc, Category.assoc, hσ₀, ha, hxσ, Category.assoc]
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsDominant (spMap a) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical a).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hainj]; exact bot_le)⟩
  have hσ₁ : σ₁ ^ k = 1 := by
    have h1 : ρ ≫ σ₁ ^ k = ρ ≫ 1 := by
      rw [MonObj.comp_pow, ← hex, ← map_pow, hx, map_one, MonObj.comp_one]
    haveI : AlgebraicGeometry.IsReduced (Over.mk (spMap (RingHom.id V))).left :=
      inferInstanceAs (AlgebraicGeometry.IsReduced (Sp V))
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom
      ((Over.w _).trans (Over.w _).symm) (spMap a) ?_)
    exact congrArg (·.left) h1
  have hbl : IsLocalHom b := ⟨fun y hy => by
    by_contra hn
    rw [hb y (by simpa using (mem_maximalIdeal y).2 hn)] at hy
    exact not_isUnit_zero hy⟩
  have hτb : ∀ χ, (τ χ : κ) = b (τV χ : V) := fun χ => by
    rw [hτV', hval]; exact hτ (Multiplicative.toAdd χ)
  have hτk : τ ^ k = 1 := MonoidHom.ext fun χ => Units.ext (by
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hτb, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← MonoidHom.pow_apply, hτV]; simp)
  have hσs : σ₁ = s V (RingHom.id V) τV hτV := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp V) G hG.smooth V _ k hkV _ _ (by rw [hσ₁, s1]) κ b hbl ?_
    rw [← s2 V κ (RingHom.id V) b b τV hτV τ hτk rfl hτb,
      s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z rfl hz]
    refine hβ.1.hom_ext ?_ ?_
    · show (spMap b ≫ σ₀) ≫ β = _
      rw [Category.assoc, hσ₀, hbσ, Category.assoc]
    · show (spMap b ≫ σ₀) ≫ G.hom = _
      rw [Category.assoc, hσ₀', Category.comp_id,
        ← s3 κ κ b hb b (RingHom.id κ) Gκ m hm τ hτk z rfl hz]
      exact (Over.w (s κ b τ hτk)).symm
  let τF : Multiplicative D.toPre.X →* Fˣ := (Units.map (a : V →* F)).comp τV
  have hτF : τF ^ k = 1 := MonoidHom.ext fun χ => by
    rw [MonoidHom.pow_apply]
    show Units.map (a : V →* F) (τV χ) ^ k = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hτV, MonoidHom.one_apply, map_one]
  obtain ⟨q, hqy, hqt⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult (k := k) τF hτF
  obtain ⟨f, ⟨i, -⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause V (maximalIdeal V) hV.1 D A G hG U F k hk
  have hq := (i q _).2 rfl
  have hxq : x = f q := by
    apply e.injective
    refine Over.OverMorphism.ext ?_
    rw [he (f q), s4 F a τF hτF q (f q) rfl hqy hqt hq,
      s2 V F (RingHom.id V) a a τV hτV τF hτF rfl (fun χ => rfl), ← hσs, hex]
    rfl
  refine ⟨τF, q, fun χ => ?_, hqy, hqt, hxq ▸ hq⟩
  exact hval F a (c χ)

end GlobalTheory.Poinc.Sep.Spz
