import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelCover

variable {S : Scheme.{0}}

theorem exists_clopen_eq (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤)))
    {T : Over S} (x y : T ⟶ G) (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ U : T.left.Opens, IsClosed (U : Set T.left) ∧
      ∀ (T' : Over S) (h : T' ⟶ T), h ≫ x = h ≫ y ↔ Set.range h.left ⊆ U := by
  have := hG.comm
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion G hn
  obtain ⟨a, ha, -⟩ := LatticeTorsion.existsUnique_torsion G n x hx
  obtain ⟨b, hb, -⟩ := LatticeTorsion.existsUnique_torsion G n y hy
  have hab : a.left ≫ (torsion G n).hom = b.left ≫ (torsion G n).hom := by rw [Over.w, Over.w]
  have o := isOpenImmersion_equalizer_ι_of_unramified _ hab
  have c := isClosedImmersion_equalizer_ι_of_isSeparated _ hab
  refine ⟨(equalizer.ι a.left b.left).opensRange,
    (equalizer.ι a.left b.left).isClosedEmbedding.isClosed_range, fun T' h => ⟨fun e => ?_, fun e => ?_⟩⟩
  · refine range_subset_range_equalizer_ι _ ?_
    have hh : (h ≫ x) ^ n = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have := (LatticeTorsion.existsUnique_torsion G n (h ≫ x) hh).unique (y₁ := h ≫ a) (y₂ := h ≫ b)
      (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb, e])
    exact congrArg (·.left) this
  · have : h ≫ a = h ≫ b := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, Over.comp_left, ← IsOpenImmersion.lift_fac (equalizer.ι a.left b.left) h.left e,
        Category.assoc, Category.assoc, equalizer.condition]
    rw [← ha, ← hb, ← Category.assoc, this, Category.assoc]

abbrev toBaseOver (T : Over S) : T ⟶ Out.baseOver S := Over.homMk T.hom (by simp)

def Good (P : Out.PolAV S) (g N' : ℕ) (c : Γ(S, ⊤)ˣ) (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)) (T : Over S)
    (p : Fin (2 * g) → (T ⟶ P.A)) : Prop :=
  (∀ i, p i ^ (N' ^ 2) = 1) ∧ (∀ i, p i ^ N' = toBaseOver T ≫ Q i) ∧
    ∀ i j, Out.WeilIs P.A P.L (N' ^ 2 : ℕ) (p i) (p j)
      (Units.map T.hom.appTop.hom.toMonoidHom c ^ Out.stdSymp g i j)

theorem units_map_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (h : Y ⟶ Z) (c : Γ(Z, ⊤)ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map h.appTop.hom.toMonoidHom c) =
      Units.map (f ≫ h).appTop.hom.toMonoidHom c := Units.ext (by rw [Scheme.Hom.comp_appTop]; rfl)

theorem exists_rep (hL : Out.Laws) (P : Out.PolAV S) (g N' : ℕ) (c : Γ(S, ⊤)ˣ)
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)) (hN : 0 < N') (hu : IsUnit ((N' ^ 2 : ℕ) : Γ(S, ⊤)))
    (hc : c ^ (N' ^ 2) = 1) (hQ : ∀ i, Q i ^ N' = 1) :
    ∃ (Z : Over S) (p : Fin (2 * g) → (Z ⟶ P.A)), IsFinite Z.hom ∧ Etale Z.hom ∧
      (∀ (T : Over S) (h : T ⟶ Z), Good P g N' c Q T (fun i => h ≫ p i)) ∧
      ∀ (T : Over S) (p' : Fin (2 * g) → (T ⟶ P.A)), Good P g N' c Q T p' → ∃! h : T ⟶ Z, ∀ i, h ≫ p i = p' i := by
  have := P.isAb.comm
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion P.A (hG := P.isAb) hu
  let Z := Out.powObj (torsion P.A (N' ^ 2)) (2 * g)
  have zf : IsFinite Z.hom := LatticeTorsion.prop_powObj @IsFinite _ hfin _
  have ze : Etale Z.hom := LatticeTorsion.prop_powObj @Etale _ het _
  let x : Fin (2 * g) → (Z ⟶ P.A) := fun i => Out.powPr (torsion P.A (N' ^ 2)) i ≫ torsion.ι P.A (N' ^ 2)
  have hx : ∀ i, x i ^ (N' ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  have hx' : ∀ {T : Over S} (h : T ⟶ Z) i, (h ≫ x i) ^ (N' ^ 2) = 1 := fun h i => by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have uZ : IsUnit ((N' ^ 2 : ℕ) : Γ(Z.left, ⊤)) := by simpa using hu.map Z.hom.appTop.hom
  choose U hU hU' using fun i => exists_clopen_eq P.A P.isAb (N' ^ 2) hu (x i ^ N') (toBaseOver Z ≫ Q i)
    (by rw [← pow_mul, Nat.mul_comm, pow_mul, hx, one_pow])
    (by rw [← MonObj.comp_pow, sq, pow_mul, hQ, one_pow, MonObj.comp_one])
  choose V hV hV' using fun i j => exists_clopen_weilIs_iff hL S P (N' ^ 2) Z (x i) (x j)
    (Units.map Z.hom.appTop.hom.toMonoidHom c ^ Out.stdSymp g i j) (pow_pos hN 2) uZ (hx i) (hx j)
    (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow, hc, map_one, one_zpow])
  have cl : IsClopen ((⋂ i, (U i : Set Z.left)) ∩ ⋂ i, ⋂ j, (V i j : Set Z.left)) :=
    (isClopen_iInter_of_finite fun i => ⟨hU i, (U i).isOpen⟩).inter
      (isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => ⟨hV i j, (V i j).isOpen⟩)
  let W : Z.left.Opens := ⟨_, cl.isOpen⟩
  have key : ∀ (T : Over S) (h : T ⟶ Z), Good P g N' c Q T (fun i => h ≫ x i) ↔ Set.range h.left ⊆ W := by
    intro T h
    have e₁ : h ≫ toBaseOver Z = toBaseOver T := Over.OverMorphism.ext (Over.w h)
    have e₂ : ∀ m : ℤ, Units.map h.left.appTop.hom.toMonoidHom (Units.map Z.hom.appTop.hom.toMonoidHom c ^ m) =
        Units.map T.hom.appTop.hom.toMonoidHom c ^ m := fun m => by
      rw [map_zpow, units_map_comp, Over.w]
    refine Iff.trans (and_iff_right (hx' h)) ?_
    show _ ↔ _ ⊆ (⋂ i, (U i : Set Z.left)) ∩ ⋂ i, ⋂ j, (V i j : Set Z.left)
    rw [Set.subset_inter_iff, Set.subset_iInter_iff, Set.subset_iInter_iff]
    refine and_congr (forall_congr' fun i => ?_) (forall_congr' fun i => ?_)
    · rw [← hU', MonObj.comp_pow, ← e₁, Category.assoc]
    · rw [Set.subset_iInter_iff]
      refine forall_congr' fun j => ?_
      rw [← hV', e₂]
  have ci : IsClosedImmersion W.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact cl.isClosed)
  let w : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
  refine ⟨Over.mk (W.ι ≫ Z.hom), fun i => w ≫ x i, inferInstanceAs (IsFinite (W.ι ≫ Z.hom)),
    inferInstanceAs (Etale (W.ι ≫ Z.hom)), fun T h => ?_, fun T p' hp => ?_⟩
  · simp only [← Category.assoc]
    refine (key T (h ≫ w)).2 ?_
    rintro _ ⟨t, rfl⟩
    exact (h.left t).2
  · choose y hy hyu using fun i => LatticeTorsion.existsUnique_torsion P.A (N' ^ 2) (p' i) (hp.1 i)
    let h : T ⟶ Z := (Out.powIsLimit (torsion P.A (N' ^ 2)) (2 * g)).lift (Fan.mk T y)
    have hh : ∀ i, h ≫ Out.powPr (torsion P.A (N' ^ 2)) i = y i := fun i =>
      (Out.powIsLimit (torsion P.A (N' ^ 2)) (2 * g)).fac (Fan.mk T y) ⟨i⟩
    have hp' : ∀ i, h ≫ x i = p' i := fun i => by rw [← hy i, ← hh i, Category.assoc]
    have hr : Set.range h.left ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      exact (key T h).1 (by rw [funext hp']; exact hp)
    let k : T ⟶ Over.mk (W.ι ≫ Z.hom) := Over.homMk (IsOpenImmersion.lift W.ι h.left hr) (by
      show _ ≫ W.ι ≫ Z.hom = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
    have hk : k ≫ w = h := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    refine ⟨k, fun i => by rw [← Category.assoc, hk, hp'], fun k' hk' => ?_⟩
    have : k' ≫ w = h := by
      refine (Out.powIsLimit (torsion P.A (N' ^ 2)) (2 * g)).hom_ext fun ⟨i⟩ => ?_
      refine (hyu i _ ?_).trans (hh i).symm
      exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (hk' i))
    apply Over.OverMorphism.ext
    rw [← cancel_mono W.ι]
    exact congrArg (·.left) (this.trans hk.symm)

theorem exists_spec {R : Type} [CommRing R] (Z : Over (Sp R)) [IsFinite Z.hom] [Etale Z.hom] :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (e : Sp R₁ ≅ Z.left),
      Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ e.hom ≫ Z.hom = spMap (algebraMap R R₁) := by
  have : IsAffine Z.left := isAffine_of_isAffineHom Z.hom
  let φ : CommRingCat.of R ⟶ Γ(Z.left, ⊤) := Spec.preimage (Z.left.isoSpec.inv ≫ Z.hom)
  have hφ : Spec.map φ = Z.left.isoSpec.inv ≫ Z.hom := Spec.map_preimage _
  have h₁ : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  have h₂ : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  letI := φ.hom.toAlgebra
  exact ⟨Γ(Z.left, ⊤), inferInstance, inferInstance, Z.left.isoSpec.symm, h₁, h₂, hφ.symm⟩

theorem good_push_iff {S' : Scheme.{0}} (P : Out.PolAV S) (g N' : ℕ) (c : Γ(S, ⊤)ˣ)
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)) {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ P.A.left}
    (h : IsGrpPullback G' P.A f φ) {L' : LB G'.left} (hL' : L'.IsLB) (hb : LBIso L' (P.L.pull φ))
    (pt : Fin (2 * g) → (Out.baseOver S' ⟶ G')) :
    Good P g N' c Q (Over.mk ((Out.baseOver S').hom ≫ f)) (fun i => pushPt h.1.w (pt i)) ↔
      (∀ i, pt i ^ (N' ^ 2) = 1) ∧ (∀ i, (pt i ^ N').left ≫ φ = f ≫ (Q i).left) ∧
        ∀ i j, Out.WeilIs G' L' (N' ^ 2 : ℕ) (pt i) (pt j)
          (Units.map f.appTop.hom.toMonoidHom c ^ Out.stdSymp g i j) := by
  have := P.isAb.comm
  have pw : ∀ (x : Out.baseOver S' ⟶ G') (m : ℕ), pushPt h.1.w x ^ m = pushPt h.1.w (x ^ m) := fun x m =>
    (map_pow (pushHom h _) x m).symm
  have e : (Out.baseOver S').hom ≫ f = f := Category.id_comp _
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_)
    (forall_congr' fun i => forall_congr' fun j => ?_))
  · rw [pw]
    have o : pushPt h.1.w (1 : Out.baseOver S' ⟶ G') = 1 := map_one (pushHom h _)
    exact ⟨fun e => SymBaseChange.pushPt_injective h (e.trans o.symm), fun e => by rw [e, o]⟩
  · rw [pw]
    have e' : ((Out.baseOver S').hom ≫ f) ≫ (Q i).left = f ≫ (Q i).left := by rw [e]
    exact ⟨fun a => (congrArg (·.left) a).trans e', fun a => Over.OverMorphism.ext (a.trans e'.symm)⟩
  · rw [weilIs_grpPullback_of_comm S S' P.A G' f φ P.L L' P.isLB hL' h hb (Out.baseOver S') _ (pt i) (pt j)
      (pushPt h.1.w (pt i)) (pushPt h.1.w (pt j)) _ rfl rfl]
    have e' : Units.map ((Out.baseOver S').hom ≫ f).appTop.hom.toMonoidHom c =
      Units.map f.appTop.hom.toMonoidHom c := by rw [e]
    exact iff_of_eq (congrArg (fun u => Out.WeilIs P.A P.L (N' ^ 2 : ℕ) _ _ (u ^ Out.stdSymp g i j)) e')

theorem unitS_comp {o : Type} [CommRing o] {S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    unitS (f ≫ s) u = Units.map f.appTop.hom.toMonoidHom (unitS s u) :=
  (units_map_comp f s _).symm

theorem unitS_spMap {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) :=
  Units.ext (congrArg (fun k => k.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem existsUnique_comb (hL : Out.Laws) [IsLocallyNoetherian S] {o : Type} [CommRing o] {k : ℕ} (hk : k ≠ 0)
    (b : TBase o k) (s : S ⟶ Sp o) (P : Out.PolAV S) {g : ℕ} (hg : P.g = g)
    (pt : Fin (2 * g) → (Out.baseOver S ⟶ P.A)) (ht : ∀ i, pt i ^ k = 1)
    (hp : ∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitS s b.ζ ^ Out.stdSymp g i j))
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ P.A) (hy : y ^ k = 1) :
    ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i)
      (fun i => (c i).val) = y := by
  have := P.isAb.comm
  have : NeZero k := ⟨hk⟩
  have cm : ∀ a a' : Over.mk x ⟶ P.A, Commute a a' := fun a a' => _root_.mul_comm a a'
  let u : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
  have tor : ∀ i, (u ≫ pt i) ^ k = 1 := fun i => by rw [← MonObj.comp_pow, ht, MonObj.comp_one]
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, spMap β = x ≫ s := ⟨(Spec.preimage (x ≫ s)).hom, Spec.map_preimage _⟩
  have hK : (k : K) ≠ 0 := by simpa using (b.unit.map β).ne_zero
  have prim : IsPrimitiveRoot (Units.map x.appTop.hom.toMonoidHom (unitS s b.ζ)) k := by
    rw [← unitS_comp, ← hβ, unitS_spMap, ← IsPrimitiveRoot.coe_units_iff]
    exact (b.prim K β).map_of_injective (f := (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
  obtain ⟨hu, hm, -⟩ := hL.weil S P k (Over.mk x)
  have ind := LevelOfPairing.injective_comb (R := fun a b u => Out.WeilIs P.A P.L k a b u) cm hu hm prim _ tor
    (fun i j => (map_zpow (Units.map x.appTop.hom.toMonoidHom) (unitS s b.ζ) _) ▸
      CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB u (hp i j))
  obtain ⟨c, hc⟩ := LevelOfPairing.surjective_comb cm hk _ tor
    (hg ▸ (hL.mulN S P k (Nat.one_le_iff_ne_zero.2 hk)).2.2.2.2 K x hK) ind y hy
  have v : ∀ i, (((c i : ℕ) : ZMod k)).val = c i := fun i => ZMod.val_cast_of_lt (c i).2
  refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_, fun c' hc' => ?_⟩
  · simp only [v]
    exact hc
  · have := ind (fun i => ⟨(c' i).val, ZMod.val_lt _⟩) c (hc'.trans hc.symm)
    funext i
    rw [← this]
    exact (ZMod.natCast_zmod_val _).symm

theorem lbIso_cancel {X Y Z : Scheme.{0}} {L : LB X} {L₁ : LB Y} {L₂ : LB Z} (hL : L.IsLB) (h₁ : L₁.IsLB)
    (h₂ : L₂.IsLB) {ψ₁ : Y ⟶ X} {φ : Z ⟶ Y} {ψ : Z ⟶ X} (e : φ ≫ ψ₁ = ψ) (a : LBIso L₁ (L.pull ψ₁))
    (c : LBIso L₂ (L.pull ψ)) : LBIso L₂ (L₁.pull φ) :=
  c.trans h₂ (pull_isLB hL _) (pull_isLB h₁ _) (LBIso.chartPull
    (chartPullSame L (fun _ : PUnit => ψ) (fun _ => ψ₁) (fun _ => 1) φ fun _ => e.symm)
    (chartPullPull L₁ φ φ rfl) a.symm)

end GlobalTheory.LevelCover

namespace GlobalTheory

open LevelCover in

theorem exists_finiteEtale_level_cover_of_pow_eq_one : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), 0 < N' → β b.ζ ^ (N' ^ 2) = 1 → (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ N' = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ N' = 1 → ∃! c : Ix g N', Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (t₁ : TObj g (N' ^ 2) J b (spMap (algebraMap R R₁) ≫ spMap β)) (ψ₁ : t₁.A.left ⟶ P.A.left), Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ (IsGrpPullback t₁.A P.A (spMap (algebraMap R R₁)) ψ₁ ∧ LBIso t₁.L (P.L.pull ψ₁) ∧ (∀ i, (t₁.act i).left ≫ ψ₁ = ψ₁ ≫ (act i).left) ∧ ∀ i, (t₁.pt i ^ N').left ≫ ψ₁ = (spMap (algebraMap R R₁)) ≫ (Q i).left) ∧ ∀ (R' : Type) [CommRing R'] (y : R →+* R') (t' : TObj g (N' ^ 2) J b (spMap y ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), (IsGrpPullback t'.A P.A (spMap y) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ N').left ≫ ψ = (spMap y) ≫ (Q i).left) → ∃! y₁ : R₁ →+* R', y₁.comp (algebraMap R R₁) = y ∧ (∀ i, (t'.pt i).left ≫ ψ = spMap y₁ ≫ (t₁.pt i).left ≫ ψ₁) ∧ TMap t' t₁ (spMap y₁) := by
  intro hL _ o _ g N' J b R _ _ β P act Q hN hζ ⟨hg, hact, hQ, _⟩
  have hu : IsUnit ((N' ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    simpa using (b.unit.map β).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hc : unitS (spMap β) b.ζ ^ (N' ^ 2) = 1 := by
    have : Units.map β.toMonoidHom b.ζ ^ (N' ^ 2) = 1 := Units.ext hζ
    rw [unitS_spMap, unitOn, ← map_pow, this, map_one]
  obtain ⟨Z, p, zf, ze, good, rep⟩ := exists_rep hL P g N' (unitS (spMap β) b.ζ) Q hN hu hc hQ
  obtain ⟨R₁, _, _, e, fin, et, he⟩ := exists_spec Z
  have : IsNoetherianRing R₁ := IsNoetherianRing.of_finite R R₁
  obtain ⟨P₁, ψ₁, hψ, hg₁, hm, w, hw⟩ := hL.polBaseChange _ _ (spMap (algebraMap R R₁)) P
  have hp : IsGrpPullback P₁.A P.A (spMap (algebraMap R R₁)) ψ₁ := ⟨hψ, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hψ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hψ.w y),
      ← hm]
    rfl⟩
  have hb : LBIso P₁.L (P.L.pull ψ₁) := LBIso.symm ⟨w, hw⟩
  let pt : Fin (2 * g) → (Out.baseOver (Sp R₁) ⟶ P₁.A) := fun i =>
    Over.homMk (hψ.lift (e.hom ≫ (p i).left) (𝟙 _) (by rw [Category.assoc, Over.w, he, Category.id_comp]))
      (hψ.lift_snd _ _ _)
  have hpt : ∀ i, (pt i).left ≫ ψ₁ = e.hom ≫ (p i).left := fun i => hψ.lift_fst _ _ _
  let h₁ : Over.mk ((Out.baseOver (Sp R₁)).hom ≫ spMap (algebraMap R R₁)) ⟶ Z :=
    Over.homMk e.hom (he.trans (Category.id_comp _).symm)
  have g₁ := good _ h₁
  rw [show (fun i => h₁ ≫ p i) = fun i => pushPt hp.1.w (pt i) from
    funext fun i => Over.OverMorphism.ext (hpt i).symm, good_push_iff P g N' _ Q hp P₁.isLB hb,
    ← unitS_comp] at g₁
  obtain ⟨tor, lab, pair⟩ := g₁
  choose act₁ hom₁ ha₁ using fun j => @SymBaseChange.exists_endo _ _ _ _ _ _ _ _ hp (act j) (hact j)
  have ha : ∀ j, (act₁ j).left ≫ ψ₁ = ψ₁ ≫ (act j).left := fun j => by
    have := congrArg (·.left) (ha₁ j (𝟙 _))
    simpa [pushPt] using this
  let t₁ : TObj g (N' ^ 2) J b (spMap (algebraMap R R₁) ≫ spMap β) :=
    { A := P₁.A, ab := P₁.isAb, dim := by rw [← hg, ← hg₁]; exact P₁.smoothDim
      L := P₁.L, isLB := P₁.isLB, rigid := P₁.rigid, sym := P₁.sym, ample := P₁.ample, ktriv := P₁.ktriv
      pt := pt, torsion := tor
      bij := existsUnique_comb hL (pow_pos hN 2).ne' b _ P₁ (hg₁.trans hg) pt tor pair
      pairing := pair, act := act₁, hom := hom₁ }
  refine ⟨R₁, inferInstance, inferInstance, t₁, ψ₁, fin, et, ⟨hp, hb, ha, lab⟩,
    fun R' _ y t' ψ ⟨hp', hb', ha', lab'⟩ => ?_⟩
  obtain ⟨h, hh, hu⟩ := rep _ _ ((good_push_iff P g N' (unitS (spMap β) b.ζ) Q hp' t'.isLB hb' t'.pt).2
    ⟨t'.torsion, lab', fun i j => by rw [← unitS_comp]; exact t'.pairing i j⟩)
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : R₁ →+* R', spMap y₁ = h.left ≫ e.inv :=
    ⟨(Spec.preimage (h.left ≫ e.inv)).hom, Spec.map_preimage _⟩
  have sc : ∀ z : R₁ →+* R', spMap (z.comp (algebraMap R R₁)) = spMap z ≫ spMap (algebraMap R R₁) := fun z =>
    Spec.map_comp (CommRingCat.ofHom (algebraMap R R₁)) (CommRingCat.ofHom z)
  have inj : ∀ {A : Type} [CommRing A] {z z' : A →+* R'}, spMap z = spMap z' → z = z' := fun e =>
    congrArg (·.hom) (Spec.map_injective e)
  have base : spMap y₁ ≫ spMap (algebraMap R R₁) = spMap y := by
    rw [hy₁, ← he, Category.assoc, e.inv_hom_id_assoc, Over.w h]
    exact Category.id_comp _
  have pts : ∀ i, (t'.pt i).left ≫ ψ = spMap y₁ ≫ (pt i).left ≫ ψ₁ := fun i => by
    rw [hpt, hy₁, Category.assoc, e.inv_hom_id_assoc]
    exact (congrArg (·.left) (hh i)).symm
  let φ : t'.A.left ⟶ P₁.A.left := hψ.lift ψ (t'.A.hom ≫ spMap y₁) (by rw [hp'.1.w, Category.assoc, base])
  have φ₁ : φ ≫ ψ₁ = ψ := hψ.lift_fst _ _ _
  have φ₂ : φ ≫ P₁.A.hom = t'.A.hom ≫ spMap y₁ := hψ.lift_snd _ _ _
  refine ⟨y₁, ⟨inj ((sc _).trans base), pts, φ, hp.cancel (hp'.congr base.symm φ₁.symm) φ₂,
    lbIso_cancel P.isLB P₁.isLB t'.isLB φ₁ hb hb', fun i => hψ.hom_ext ?_ ?_, fun j => hψ.hom_ext ?_ ?_⟩,
    fun y₂ ⟨b₂, p₂, _⟩ => inj ?_⟩
  · rw [Category.assoc, φ₁, pts, Category.assoc]
  · show (_ ≫ φ) ≫ _ = (_ ≫ (pt i).left) ≫ _
    rw [Category.assoc, φ₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · show (_ ≫ φ) ≫ _ = (φ ≫ (act₁ j).left) ≫ _
    rw [Category.assoc, φ₁, ha', Category.assoc, ha, ← Category.assoc, φ₁]
  · show (_ ≫ φ) ≫ _ = (φ ≫ (act₁ j).left) ≫ _
    rw [Category.assoc, φ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, φ₂]
  · let h₂ : Over.mk ((Out.baseOver (Sp R')).hom ≫ spMap y) ⟶ Z := Over.homMk (spMap y₂ ≫ e.hom) (by
      show (_ ≫ _) ≫ _ = 𝟙 _ ≫ _
      rw [Category.assoc, he, ← sc, b₂, Category.id_comp])
    have : h₂ = h := hu h₂ fun i => Over.OverMorphism.ext (by
      show (spMap y₂ ≫ e.hom) ≫ _ = (t'.pt i).left ≫ ψ
      rw [p₂, Category.assoc, ← hpt])
    rw [hy₁, ← this]
    show _ = (spMap y₂ ≫ e.hom) ≫ e.inv
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]

theorem exists_finiteEtale_level_cover : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), 0 < N' → (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ N' = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ N' = 1 → ∃! c : Ix g N', Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (t₁ : TObj g (N' ^ 2) J b (spMap (algebraMap R R₁) ≫ spMap β)) (ψ₁ : t₁.A.left ⟶ P.A.left), Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ (IsGrpPullback t₁.A P.A (spMap (algebraMap R R₁)) ψ₁ ∧ LBIso t₁.L (P.L.pull ψ₁) ∧ (∀ i, (t₁.act i).left ≫ ψ₁ = ψ₁ ≫ (act i).left) ∧ ∀ i, (t₁.pt i ^ N').left ≫ ψ₁ = (spMap (algebraMap R R₁)) ≫ (Q i).left) ∧ ∀ (R' : Type) [CommRing R'] (y : R →+* R') (t' : TObj g (N' ^ 2) J b (spMap y ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), (IsGrpPullback t'.A P.A (spMap y) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ N').left ≫ ψ = (spMap y) ≫ (Q i).left) → ∃! y₁ : R₁ →+* R', y₁.comp (algebraMap R R₁) = y ∧ (∀ i, (t'.pt i).left ≫ ψ = spMap y₁ ≫ (t₁.pt i).left ≫ ψ₁) ∧ TMap t' t₁ (spMap y₁) := by
  intro hL hL₂ o _ g N' J b R _ _ _ β P act Q hN
  refine exists_finiteEtale_level_cover_of_pow_eq_one hL hL₂ o g N' J b R β P act Q hN ?_
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
  let π : R →+* FractionRing (R ⧸ q) := (algebraMap (R ⧸ q) _).comp (Ideal.Quotient.mk q)
  have h : π (β b.ζ ^ (N' ^ 2) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, sub_eq_zero]
    exact (b.prim _ (π.comp β)).pow_eq_one
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((IsFractionRing.to_map_eq_zero_iff (K := FractionRing (R ⧸ q))).1 h)

end GlobalTheory
