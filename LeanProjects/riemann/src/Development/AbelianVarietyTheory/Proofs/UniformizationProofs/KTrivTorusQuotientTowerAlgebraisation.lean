import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TwistedPowTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOfGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilNondegenerateGeneric

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.Principal

theorem finite_points {S : Scheme.{0}} (H : Over S) [IsFinite H.hom] {K : Type} [Field K] [IsAlgClosed K]
    (t : Spec (CommRingCat.of K) ⟶ S) : Finite (Over.mk t ⟶ H) := by
  have hfin := ((pullback.snd H.hom t).finite_preimage_singleton (IsLocalRing.closedPoint K)).to_subtype
  let σ : (Over.mk t ⟶ H) → (Spec (CommRingCat.of K) ⟶ pullback H.hom t) := fun x =>
    pullback.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp _).symm)
  have h₁ : ∀ x, σ x ≫ pullback.fst H.hom t = x.left := fun x => pullback.lift_fst _ _ _
  have h₂ : ∀ x, σ x ≫ pullback.snd H.hom t = 𝟙 _ := fun x => pullback.lift_snd _ _ _
  refine Finite.of_injective (fun x => (⟨σ x (IsLocalRing.closedPoint K),
    Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _⟩ :
      (pullback.snd H.hom t) ⁻¹' {IsLocalRing.closedPoint K})) fun a b hab => ?_
  have e : σ a = σ b :=
    ext_of_apply_closedPoint_eq (K := K) (pullback.snd H.hom t) (h₂ a) (h₂ b) (congrArg Subtype.val hab)
  exact Over.OverMorphism.ext ((h₁ a).symm.trans (e ▸ h₁ b))

theorem exists_pow_eq_one (hG : GlobalFnsSt) {R : Type} [CommRing R] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) {L : LB B.left} (hLB : L.IsLB) (hL : RelAmple B L)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ B) (hx : InK B L x) : ∃ N : ℕ, 1 ≤ N ∧ x ^ N = 1 := by
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG R B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ x : Over.mk t ⟶ B, InK B L x ↔ ∃ y : Over.mk t ⟶ H, y ≫ j = x :=
    fun x => (hK _ rfl _ x).trans (hH _ x)
  have := finite_points H t
  have : Finite (kSubgroup B hLB (Over.mk t)) :=
    Finite.of_surjective (fun y : Over.mk t ⟶ H => (⟨y ≫ j, (hrep _).2 ⟨y, rfl⟩⟩ : kSubgroup B hLB (Over.mk t)))
      fun z => ((hrep z.1).1 z.2).imp fun _ h => Subtype.ext h
  exact ⟨Nat.card (kSubgroup B hLB (Over.mk t)), Nat.card_pos,
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : kSubgroup B hLB (Over.mk t))))⟩

theorem exists_gen_of_inK {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hLB : L.IsLB)
    {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk t ⟶ B) (hx : InK B L x) :
    ∃ u : LB.Gen (translDiff B L x), u.IsGen := by
  obtain ⟨V, hpV, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  refine GlobalTheory.TwistTranslate.gen_of_pull_top hLB _ (fun z => ?_) c hc
  have e : ∀ p q : Spec (CommRingCat.of K), p = q := fun p q => Subsingleton.elim p q
  change (fst (Over.mk t) B).left z ∈ V
  rw [e ((fst (Over.mk t) B).left z) (IsLocalRing.closedPoint K)]
  exact hpV

theorem kTriv_alg : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L := by
  intro hc laws V _ _ _ A G _ _ s t a
  have hdvr : IsDiscreteValuationRing V := s.cdvr.1
  have hchar : CharZero V := s.cdvr.2.2
  refine GlobalTheory.KTrivGeneric.kTriv_of_generic laws.globalFns V a.B a.isAb a.M.L a.M.c a.ample fun x hx => ?_
  obtain ⟨N, hN, hxN⟩ := exists_pow_eq_one laws.globalFns a.isAb a.M.L.isLB a.ample _ x hx
  exact GlobalTheory.UU.cubWeil_nondegenerate_generic hc laws V A G s t a (AlgebraicClosure (FractionRing V)) N hN x hxN fun y hy =>
    GlobalTheory.UU.KerPair.cubWeil_of_gen laws.globalFns _ a.B a.isAb a.M.L a.M.c N _ x y hxN hy
      (exists_gen_of_inK a.M.L.isLB _ x hx)

end GlobalTheory.UU.Principal
