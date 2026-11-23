import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilIntegral

theorem exists_point_in_all {K : Type} [Field K] [IsAlgClosed K] {X Y : Scheme.{0}} (π : X ⟶ Y)
    [LocallyOfFiniteType π] [GeometricallyIntegral π] (x : Sp K ⟶ Y) {J : Type} [Finite J]
    (U : J → X.Opens) (hU : ∀ i, ∃ q : X, q ∈ U i ∧ π q = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ∀ i, g (IsLocalRing.closedPoint K) ∈ U i := by
  have : IsIntegral (pullback π x) :=
    GeometricallyIntegral.geometrically_isIntegral x _ _ (IsPullback.of_hasPullback π x)
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  have hgen : ∀ i, pullback.fst π x (genericPoint (pullback π x :)) ∈ U i := fun i => by
    obtain ⟨q, hq, hx⟩ := hU i
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) q
      (IsLocalRing.closedPoint K) hx
    exact ((genericPoint_specializes z).map (pullback.fst π x).continuous).mem_open (U i).isOpen (hz ▸ hq)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints
    (Z := ⋂ i, ((pullback.fst π x ⁻¹ᵁ U i : (pullback π x).Opens) : Set (pullback π x :))) ⟨_, Set.mem_iInter.2 hgen⟩
    (isOpen_iInter_of_finite fun i => (pullback.fst π x ⁻¹ᵁ U i).isOpen).isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun i => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc _) ∈ U i
    exact (congrArg (fun t => pullback.fst π x t ∈ U i)
      (pointOfClosedPoint_apply (pullback.snd π x) c hc _)).mpr (Set.mem_iInter.1 hcO i)

section Translation

variable {O : Type} [CommRing O]

theorem specO_self_hom : (specO O O).hom = 𝟙 (Sp O) := Spec.map_id _

def toBase (G : Over (Sp O)) : G ⟶ specO O O :=
  Over.homMk G.hom ((congrArg (G.hom ≫ ·) specO_self_hom).trans (Category.comp_id _))

theorem eq_toBase {G : Over (Sp O)} (f : G ⟶ specO O O) : f = toBase G :=
  Over.OverMorphism.ext (((Category.comp_id _).symm.trans
    (congrArg (f.left ≫ ·) specO_self_hom.symm)).trans (Over.w f))

def transl {G : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) : G ⟶ G := 𝟙 G * (toBase G ≫ a)

theorem comp_transl {G T : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) (w : T ⟶ G) :
    w ≫ transl a = w * (toBase T ≫ a) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, eq_toBase (w ≫ toBase G)]

theorem point_comp_transl {G : Over (Sp O)} [GrpObj G] (a z : specO O O ⟶ G) :
    z ≫ transl a = z * a := by
  rw [comp_transl, ← eq_toBase (𝟙 _), Category.id_comp]

theorem transl_inv_comp {G : Over (Sp O)} [GrpObj G] (a : specO O O ⟶ G) :
    transl a⁻¹ ≫ transl a = 𝟙 G := by
  rw [comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one,
    _root_.mul_one]

end Translation

theorem exists_translate_inOpen (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (G : Over (Sp O)) [GrpObj G] [Smooth G.hom]
    [GeometricallyConnected G.hom] (U : G.left.Opens) (x : G.left) (hx : x ∈ U)
    (hx' : G.hom x = IsLocalRing.closedPoint O) (J : Type) [Finite J] (a : J → (specO O O ⟶ G)) :
    ∃ z : specO O O ⟶ G, ∀ i, InOpen U (z * a i) := by
  obtain ⟨-, hk, hlift⟩ := valuationRing_henselian_and_lift_of_isAlgClosed O K
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  have hr : spMap (IsLocalRing.residue O) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) =
      IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  obtain ⟨g, hg, hgU⟩ := exists_point_in_all G.hom (spMap (IsLocalRing.residue O))
    (fun i => (transl (a i)).left ⁻¹ᵁ U) fun i => ⟨(transl (a i)⁻¹).left x, by
      show (transl (a i)).left ((transl (a i)⁻¹).left x) ∈ U
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_inv_comp]
      exact hx, by
      rw [← Scheme.Hom.comp_apply, Over.w, hx', hr]⟩
  obtain ⟨y, hy, hy'⟩ := hlift _ G.hom inferInstance g hg
  refine ⟨Over.homMk y (hy.trans specO_self_hom.symm), fun i => ?_⟩
  rw [← point_comp_transl]
  have h1 : (y ≫ (transl (a i)).left) (IsLocalRing.closedPoint O) ∈ U := by
    have e : g (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = y (IsLocalRing.closedPoint O) := by
      rw [← hy', ← hr]
      rfl
    have := hgU i
    rw [e] at this
    exact this
  exact eq_top_iff.2 fun q _ =>
    ((IsLocalRing.specializes_closedPoint (R := O) q).map
      (y ≫ (transl (a i)).left).continuous).mem_open U.isOpen h1

theorem translatesInto : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), TranslatesInto P := by
  intro p hp C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P U ⟨x, hx, hxp⟩ J _ a
  have hv := P.integers
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI := P.semi.smooth
  haveI := P.semi.geomConnected
  refine exists_translate_inOpen O C P.G U x hx ?_ J a
  refine PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime _).ne_top)
    fun b hb => ?_)
  have h1 : v (algebraMap O C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) fun e => hb (hv.isUnit_of_one' e)
  have h2 : 0 < v (algebraMap O C p) := by
    rw [map_natCast]
    exact pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 hp.out.ne_zero))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
  have h3 : (p : O) ∣ b ^ n := hv.le_iff_dvd.1 (by rw [map_pow, map_pow]; exact hn.le)
  exact (PrimeSpectrum.isPrime _).mem_of_pow_mem n (Ideal.mem_of_dvd _ h3 hxp)

end GlobalTheory.WeilIntegral
