import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRingActionDegenerationLinearUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAddInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianAndSpecialFibre

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

def pushEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y =>
    ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem actPull_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] [IsCommMonObj G] {Λ : Type} [Ring Λ]
    (ρ : RingAct G Λ) (a : Λ) :
    ((actPull f ρ).act a).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ (ρ.act a).left :=
  pullback.lift_fst _ _ _

variable {p : ℕ} {R : Type} [CommRing R] {I : Ideal R} {O : Type} [CommRing O]

theorem isAdicColimit_of_isNilpotent {f : R →+* O} (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) :
    IsAdicColimit I (Over.mk ((specO O S).hom ≫ spMap f)) := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨m, hm⟩ := hS
  have e : (specO O S).hom ≫ spMap f = Spec.map (CommRingCat.ofHom ((algebraMap O S).comp f)) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  rw [e]
  refine isAdicColimit_of_pow I _ (n * m) fun a ha => ?_
  have h₁ : (I ^ n).map f ≤ Ideal.span {(p : O)} := Ideal.map_le_iff_le_comap.2 hn
  have h₂ : f a ∈ Ideal.span {(p : O) ^ m} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono h₁ m ?_
    rw [← Ideal.map_pow, ← pow_mul]
    exact Ideal.mem_map_of_mem f ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h₂
  rw [RingHom.comp_apply, ← hc, map_mul, map_pow, map_natCast, hm, mul_zero]

variable [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} [Algebra O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ]

theorem spMap_comp_algebraMap (f : R →+* O) :
    spMap ((algebraMap O C).comp f) = spMap (algebraMap O C) ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

def ofCompletion (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (ιG : RingAct G Λ)
    {E : SplitExt (Sp R)} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] (d : E.GtDatum H) (ρ : RingAct H Λ)
    (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G)))
    (hnat : ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x)
    (hlin : ∀ T hT (x : T ⟶ H) (a : Λ), J T hT (x ≫ ρ.act a) = J T hT x ≫ ιG.act a)
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) : Point p v O Λ where
  integers := hv
  eps := ε
  A := A'
  oA := oA'
  G := (Over.pullback (spMap f)).obj G
  semi := IsSemiAbelian.pullback _ G hG
  gen := pullback.lift j (A'.A.hom ≫ spMap (algebraMap O C))
    (by rw [hj.1.w, spMap_comp_algebraMap, Category.assoc])
  gen_pull := (isGrpPullback_pullback G (spMap f)).cancel
    (hj.congr (spMap_comp_algebraMap f) (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  oG := actPull (spMap f) ιG
  gen_act a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hact, Category.assoc, actPull_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.lift_snd, Over.w_assoc, Category.assoc]
      exact ((congrArg (_ ≫ ·) (Over.w ((actPull (spMap f) ιG).act a))).trans (pullback.lift_snd _ _ _)).symm
  Ext := GtBaseChange.extBC (spMap f) E
  Gt := (Over.pullback (spMap f)).obj H
  D := (GtBaseChange.isGt_extBC (spMap f) E H d).some
  oGt := actPull (spMap f) ρ
  cmp S _ _ hS := (pushEquiv (isGrpPullback_pullback H (spMap f)) _).trans
    ((J _ (isAdicColimit_of_isNilpotent hf S hS)).trans (pushEquiv (isGrpPullback_pullback G (spMap f)) _).symm)
  cmp_nat S S' _ _ _ _ hS hS' φ x := by
    let k : Over.mk ((specO O S').hom ≫ spMap f) ⟶ Over.mk ((specO O S).hom ≫ spMap f) :=
      Over.homMk (ptMap φ).left (Over.w_assoc (ptMap φ) _)
    have e : ∀ {X : Over (Sp R)} [GrpObj X] (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (ptMap φ ≫ y) =
          k ≫ pushEquiv (isGrpPullback_pullback X (spMap f)) _ y := fun y =>
      Over.OverMorphism.ext (Category.assoc _ _ _)
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hnat]
  cmp_act S _ _ hS a x := by
    have e : ∀ {X : Over (Sp R)} [GrpObj X] [IsCommMonObj X] (α : RingAct X Λ)
        (y : specO O S ⟶ (Over.pullback (spMap f)).obj X),
        pushEquiv (isGrpPullback_pullback X (spMap f)) _ (y ≫ (actPull (spMap f) α).act a) =
          pushEquiv (isGrpPullback_pullback X (spMap f)) _ y ≫ α.act a := fun α y =>
      Over.OverMorphism.ext ((Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) (actPull_fst _ α a)).trans (Category.assoc _ _ _).symm))
    simp only [MulEquiv.trans_apply]
    rw [MulEquiv.symm_apply_eq, e, e, MulEquiv.apply_symm_apply, hlin]

section Unif

variable [IsDomain R] {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G)

theorem exists_comparison : ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H)
    (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T) (J : ∀ T, IsAdicColimit I T → ((T ⟶ H) ≃* (T ⟶ G))),
    (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ T hT w x, J T hT w = x ↔ FormalPoint.IsPointOf U (Φ T w) x) ∧
      ∀ T T' hT hT' (k : T' ⟶ T) (x : T ⟶ H), J T' hT' (k ≫ x) = k ≫ J T hT x := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL hH
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hL (Φ := Φ) hΦ
  exact ⟨H, inferInstance, inferInstance, Φ, J, hH, hΦ, hJ, fun T T' hT hT' k x =>
    (hJ _ hT' _ _).2 (((hJ _ hT x _).1 rfl).pull k (hΦ.1 _ _ k _))⟩

theorem exists_point_of_unif (hG : IsSemiAbelian G) [Module Λ D.toPre.X] {ιD : D.OAct Λ} {ιA : A.OAct Λ}
    {ιG : RingAct G Λ} (hO : U.OLinear Λ ιD ιA ιG) (hv : v.Integers O) (ε : Eps p C) (f : R →+* O)
    (hf : ∃ n : ℕ, ∀ a ∈ I ^ n, f a ∈ Ideal.span {(p : O)})
    (A' : PolAV (Sp C)) (oA' : A'.OAct Λ) (j : A'.A.left ⟶ G.left)
    (hj : IsGrpPullback A'.A G (spMap ((algebraMap O C).comp f)) j)
    (hact : ∀ a, (oA'.act a).left ≫ j = j ≫ (ιG.act a).left) :
    ∃ (H : Over (Sp R)) (_ : GrpObj H) (_ : IsCommMonObj H) (Φ : ∀ T, (T ⟶ H) ≃ GtPt D.toPre T)
      (ρ : RingAct H Λ) (P : Point p v O Λ),
      (splitExt D.toPre).IsGt H ∧ Represents Φ ∧
      (∀ (a : Λ) T (x : T ⟶ H), FormalPoint.IsSmulPt ιD a (Φ T x) (Φ T (x ≫ ρ.act a))) ∧
      P.eps = ε ∧ P.A = A' ∧ HEq P.oA oA' ∧ P.G = (Over.pullback (spMap f)).obj G ∧
      P.Ext = GtBaseChange.extBC (spMap f) (splitExt D.toPre) ∧ P.Gt = (Over.pullback (spMap f)).obj H ∧
      ∃ (πG : P.G.left ⟶ G.left) (πH : P.Gt.left ⟶ H.left) (hπG : IsGrpPullback P.G G (spMap f) πG)
        (hπH : IsGrpPullback P.Gt H (spMap f) πH),
        HEq πG (pullback.fst G.hom (spMap f)) ∧ HEq πH (pullback.fst H.hom (spMap f)) ∧
        HEq (P.gen ≫ πG) j ∧
        (∀ a, (P.oG.act a).left ≫ πG = πG ≫ (ιG.act a).left) ∧
        (∀ a, (P.oGt.act a).left ≫ πH = πH ≫ (ρ.act a).left) ∧
        ∀ (S : Type) [CommRing S] [Algebra O S] (hS : IsNilpotent (p : S)) (x : specO O S ⟶ P.Gt),
          FormalPoint.IsPointOf U (Φ _ (pushPt hπH.1.w x)) (pushPt hπG.1.w (P.cmp S hS x)) := by
  have hL := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨H, _, _, Φ, J, ⟨d⟩, hΦ, hJ, hnat⟩ := exists_comparison U
  obtain ⟨ρ, hρ⟩ := exists_ringAct hL ιD (Φ := Φ) hΦ
  refine ⟨H, inferInstance, inferInstance, Φ, ρ, ofCompletion hv ε f hf hG ιG d ρ J hnat
      (fun T hT x a => (hJ _ hT _ _).2 (((hJ _ hT x _).1 rfl).smul hL hO a (hρ a _ _))) A' oA' j hj hact,
    ⟨d⟩, hΦ, hρ, rfl, rfl, HEq.rfl, rfl, rfl, rfl, _, _, isGrpPullback_pullback G _, isGrpPullback_pullback H _,
    HEq.rfl, HEq.rfl, heq_of_eq (pullback.lift_fst _ _ _), actPull_fst _ ιG, actPull_fst _ ρ, fun S _ _ hS x => ?_⟩
  exact (hJ _ (isAdicColimit_of_isNilpotent hf S hS) _ _).1
    ((pushEquiv (isGrpPullback_pullback G (spMap f)) _).apply_symm_apply _).symm

end Unif

end GlobalTheory.HTLat
