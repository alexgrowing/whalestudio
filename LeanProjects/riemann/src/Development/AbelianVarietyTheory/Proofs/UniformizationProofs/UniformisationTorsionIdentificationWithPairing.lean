import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDimStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOriginStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImageStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsInducedTranslationFrobeniusOnSectionsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardQuotientKTorsionPairsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsionStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem translT_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] {T : Over S} (x y : T ⟶ A) :
    translT A x ≫ translT A y = translT A (x * y) := by
  have h : ∀ z : T ⟶ A, translPt A z = snd T A * (fst T A ≫ z) := fun z => by
    rw [mul_comm]; rfl
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp only [translT, Category.assoc, lift_snd, h, MonObj.comp_mul, lift_fst_assoc, _root_.mul_assoc]

theorem torsion_eq : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k : ℕ), 1 ≤ k → ∃ f, Tors U.toUnifPre F k f := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ k hk
  have hqk := GlobalTheory.T.inducesFrobeniusOnSections_translation_iff_image hL R I hI D A G hG U F k hk
  have hcomp := GlobalTheory.T.indAt_comp_equiv_unique_id hL R I hI D A G hG U F k hk
  have huniq := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hinj := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 R I hI D A G hG U F k hk
  have hex : ∀ p : QkPt D.toPre F k, ∃ x, QkToAkU U.toUnifPre F k p x := fun p => by
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_inducedTranslation_frobeniusOnSections hL R I hI D A G hG U F k hk p
    exact ⟨x, (hqk p x).1 (hx 1 k le_rfl (mul_one k).symm p (one_smul _ _).symm rfl)⟩
  choose f hf using hex
  have hwd : ∀ p p', QkPt.Equiv D.toPre F p p' → f p = f p' := fun p p' h =>
    huniq p' _ _ ((hqk _ _).1 ((hcomp p p' p' _ (𝟙 _) ((hqk _ _).2 (hf p))).2.1 h)) (hf p')
  have hpow : ∀ p, f p ^ k = 1 := fun p => by
    obtain ⟨w, hw⟩ := U.ext
    exact (hf p w hw).1
  refine ⟨f, fun p x => ⟨fun h => huniq p _ _ h (hf p), fun h => h ▸ hf p⟩, ?_,
    fun p p' => ⟨fun h => hinj p p' (f p) (hf p) (h ▸ hf p'), hwd p p'⟩, ?_,
    fun p p' z => GlobalTheory.T.weilQkIs_iff_commutatorPairing_torsion hL R I hI D A G hG U F k hk p p' _ _ (hf p) (hf p') z⟩
  · haveI : CharZero (FractionRing R) := inferInstance
    haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
    have hA := (hL.1.mulN _ A k hk).2.2.2.2 F (jFK (R := R) F) (Nat.cast_ne_zero.2 (by omega))
    have hQ := GlobalTheory.T.card_quotient_kTorsion_pairs hL R I hI D F k hk
    have hd := GlobalTheory.T.unif_g_eq_rank_add_g hL R I hI D A G hG U
    let φ : Quot (QkPt.Equiv D.toPre F (k := k)) → {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} :=
      Quot.lift (fun p => ⟨f p, hpow p⟩) (fun p p' h => Subtype.ext (hwd p p' h))
    have hφ : Function.Injective φ := by
      rintro ⟨p⟩ ⟨p'⟩ h
      have h' : f p = f p' := congrArg Subtype.val h
      exact Quot.sound (hinj p p' (f p) (hf p) (h' ▸ hf p'))
    haveI : Finite {x : TFK (R := R) F ⟶ A.A // x ^ k = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hA]; positivity)
    have hb : Function.Bijective φ := hφ.bijective_of_nat_card_le (by rw [hA, hQ, hd])
    intro x hx
    obtain ⟨⟨p⟩, hp⟩ := hb.2 ⟨x, hx⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  · intro p p' p'' h
    have := (hcomp p p' p'' _ _ ((hqk _ _).2 (hf p))).1 ((hqk _ _).2 (hf p')) h
    rw [translT_comp] at this
    exact huniq p'' _ _ (hf p'') ((hqk _ _).1 this)

end GlobalTheory.TorsionIso
