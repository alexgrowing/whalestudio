import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppTopPullbackSndOfApp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppTopSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp e using h
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X W a
    (fun p => by obtain ⟨y, hy⟩ := hp p; exact ⟨p, y, hy⟩) ha
  exact 𝒰.hom_ext _ _ e

theorem exists_glue {X Y : Scheme.{0}} {I : Type} (U : I → Scheme.{0}) (j : ∀ i, U i ⟶ X) (g : ∀ i, U i ⟶ Y)
    (hj : ∀ i, IsOpenImmersion (j i)) (hc : ∀ p : X, ∃ i, p ∈ Set.range (j i))
    (h : ∀ i i' (y : U i), j i y ∈ Set.range (j i') → ∃ (W : Scheme.{0}) (a : W ⟶ U i) (a' : W ⟶ U i'),
      IsOpenImmersion a ∧ y ∈ Set.range a ∧ a ≫ j i = a' ≫ j i' ∧ a ≫ g i = a' ≫ g i') :
    ∃ G : X ⟶ Y, ∀ i, j i ≫ G = g i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers I U j
    (fun p => by obtain ⟨i, y, hy⟩ := hc p; exact ⟨i, y, hy⟩) hj
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    refine hom_ext_loc fun p => ?_
    obtain ⟨W, a, a', ha, ⟨w, hw⟩, e, e'⟩ := h i i' (pullback.fst (j i) (j i') p)
      ⟨pullback.snd (j i) (j i') p, by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
    have := hj i'
    have h1 : pullback.lift a a' e ≫ pullback.fst (j i) (j i') = a := pullback.lift_fst _ _ _
    have : IsOpenImmersion (pullback.lift a a' e ≫ pullback.fst (j i) (j i')) := by rw [h1]; exact ha
    refine ⟨W, pullback.lift a a' e, IsOpenImmersion.of_comp _ (pullback.fst (j i) (j i')), ⟨w, ?_⟩, ?_⟩
    · apply (pullback.fst (j i) (j i')).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h1, hw]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, e']
  exact ⟨𝒰.glueMorphisms g hg, fun i => 𝒰.ι_glueMorphisms g hg i⟩

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h x y hy.symm
    exact ⟨p, hp⟩

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have e1 : x' = (Over.homMk k hk : T' ⟶ T) ≫ x := Over.OverMorphism.ext hx
  have e2 : y' = (Over.homMk k hk : T' ⟶ T) ≫ y := Over.OverMorphism.ext hy
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem isGrpPullback_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by rw [w, Category.comp_id]⟩, fun T y z y₀ z₀ hy hz => ?_⟩
  refine hom_ext_loc fun q => ?_
  obtain ⟨W, x, B, _, a, hx, hp, ha, hb⟩ := h (T.hom q)
  let k := pullback.fst T.hom x
  let T' : Over W := Over.mk (pullback.snd T.hom x)
  have hk : k ≫ T.hom = T'.hom ≫ x := pullback.condition
  let y' : T' ⟶ B := Over.homMk (ha.1.lift (k ≫ y.left) T'.hom (by rw [Category.assoc, Over.w y, hk]))
    (ha.1.lift_snd _ _ _)
  let z' : T' ⟶ B := Over.homMk (ha.1.lift (k ≫ z.left) T'.hom (by rw [Category.assoc, Over.w z, hk]))
    (ha.1.lift_snd _ _ _)
  have ey : y'.left ≫ a = k ≫ y.left := ha.1.lift_fst _ _ _
  have ez : z'.left ≫ a = k ≫ z.left := ha.1.lift_fst _ _ _
  have e1 := ha.2 T' y' z' (pushPt ha.1.w y') (pushPt ha.1.w z') rfl rfl
  have e2 := hb.2 T' y' z' (pushPt hb.1.w y') (pushPt hb.1.w z') rfl rfl
  have e3 := mul_left_pre (T' := Over.mk (T'.hom ≫ x)) k hk y z (pushPt ha.1.w y') (pushPt ha.1.w z') ey ez
  have e4 := mul_left_pre (T := Over.mk (T.hom ≫ 𝟙 S)) (T' := Over.mk (T'.hom ≫ x)) k
    (by show k ≫ T.hom ≫ 𝟙 S = T'.hom ≫ x; rw [Category.comp_id, hk]) y₀ z₀ (pushPt hb.1.w y') (pushPt hb.1.w z')
    (by show y'.left ≫ a ≫ φ = _; rw [← Category.assoc, ey, hy, Category.assoc])
    (by show z'.left ≫ a ≫ φ = _; rw [← Category.assoc, ez, hz, Category.assoc])
  refine ⟨_, k, inferInstance, (range_of_isPullback (IsPullback.of_hasPullback T.hom x) q).2 hp, ?_⟩
  refine e4.symm.trans (e2.trans ?_)
  rw [← Category.assoc, ← e1, e3, Category.assoc]

theorem lbIso_of_loc (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (rL : Out.Rigidified A L) (rM : Out.Rigidified A M)
    (h : ∀ p : S, ∃ (W B : Scheme.{0}) (x : W ⟶ S) (a : B ⟶ A.left) (c : B ⟶ W),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a c A.hom x ∧ LBIso (L.pull a) (M.pull a)) : LBIso L M := by
  refine exists_gen_of_local_of_section A.left S A.hom (eSec A) (LB.div M L) (LB.isLB_div hM hL) (Over.w η[A])
    (BaseChangeFns.app_surjective hG S A hA S A.left (𝟙 _) (𝟙 _) A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩))
    (fun p => ?_) ?_
  · obtain ⟨W, B, x, a, c, hx, hp, ha, H⟩ := h p
    have : IsOpenImmersion a := MorphismProperty.of_isPullback ha.flip hx
    refine ⟨x.opensRange, hp, ?_⟩
    have hr : Set.range (A.hom ⁻¹ᵁ x.opensRange).ι ⊆ Set.range a := by
      rintro _ ⟨y, rfl⟩
      exact (range_of_isPullback ha _).2 y.2
    have e := IsOpenImmersion.lift_fac a _ hr
    obtain ⟨w, hw⟩ := H.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ x.opensRange).ι) _ _ _ fun _ => e.symm)
      (chartPullSame M (fun _ : PUnit => (A.hom ⁻¹ᵁ x.opensRange).ι) _ _ _ fun _ => e.symm)
    exact gen_chartPull (IsoDescent.chartPullDiv M L _) w hw
  · obtain ⟨u, hu⟩ := rL
    obtain ⟨u', hu'⟩ := rM
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ u hu u' hu'
    exact gen_chartPull (IsoDescent.chartPullDiv M L _) w hw

variable {o : Type} [CommRing o] {S S' S'' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

def IsTM (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem tMap_iff {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} : TMap t' t f ↔ ∃ φ, IsTM t' t f φ := Iff.rfl

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LBIso ((L.pull f).pull h) (L.pull (h ≫ f)) :=
  (PolBaseChange.lbIso_refl (pull_isLB hL (h ≫ f))).chartPull
    (chartPullOut L (fun _ : PUnit => f) (fun _ => 1) h _ fun _ => rfl) (chartPullId _)

theorem lbIso_pull {Y Z : Scheme.{0}} {L M : LB Y} (H : LBIso L M) (h : Z ⟶ Y) : LBIso (L.pull h) (M.pull h) :=
  H.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl)

theorem IsTM.congr {t' : TObj g k J b s'} {t : TObj g k J b s} {f f' : S' ⟶ S} {φ φ' : t'.A.left ⟶ t.A.left}
    (h : IsTM t' t f φ) (e : f = f') (e' : φ = φ') : IsTM t' t f' φ' := e ▸ e' ▸ h

theorem IsTM.comp {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    {φ : t'.A.left ⟶ t.A.left} {φ' : t''.A.left ⟶ t'.A.left} (h' : IsTM t'' t' f' φ') (h : IsTM t' t f φ) :
    IsTM t'' t (f' ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.comp h.1, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) h'.2.1
      (LBIso.trans (pull_isLB t'.isLB _) (pull_isLB (pull_isLB t.isLB _) _) (pull_isLB t.isLB _)
        (lbIso_pull h.2.1 φ') (lbIso_pull_pull t.isLB φ φ'))
  · rw [← Category.assoc, h'.2.2.1, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, h'.2.2.2, Category.assoc, h.2.2.2, Category.assoc]

theorem IsTM.cancel {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    {φ : t'.A.left ⟶ t.A.left} {ψ : t''.A.left ⟶ t.A.left} (h : IsTM t' t f φ) (n : IsTM t'' t (f' ≫ f) ψ) :
    ∃ φ', φ' ≫ φ = ψ ∧ IsTM t'' t' f' φ' := by
  have hp := h.1.1
  let F : t''.A.left ⟶ t'.A.left := hp.lift ψ (t''.A.hom ≫ f') (by rw [n.1.1.w, Category.assoc])
  have hF : F ≫ φ = ψ := hp.lift_fst _ _ _
  have hw : F ≫ t'.A.hom = t''.A.hom ≫ f' := hp.lift_snd _ _ _
  refine ⟨F, hF, h.1.cancel (by rw [hF]; exact n.1) hw, ?_, fun i => ?_, fun j => ?_⟩
  · have H := n.2.1
    rw [← hF] at H
    exact LBIso.trans t''.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) H
      (LBIso.trans (pull_isLB t'.isLB _) (pull_isLB (pull_isLB t.isLB _) _) (pull_isLB t.isLB _)
        (lbIso_pull h.2.1 F) (lbIso_pull_pull t.isLB φ F)).symm
  · apply hp.hom_ext
    · rw [Category.assoc, hF, n.2.2.1, Category.assoc, Category.assoc, h.2.2.1]
    · have a1 : (t''.pt i).left ≫ t''.A.hom = 𝟙 _ := Over.w _
      have a2 : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w _
      rw [Category.assoc, hw, ← Category.assoc, a1, Category.assoc, a2]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, hF, n.2.2.2, Category.assoc, h.2.2.2, ← Category.assoc, hF]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tMap_comp {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ', h'⟩ := tMap_iff.1 h'
  obtain ⟨φ, h⟩ := tMap_iff.1 h
  exact tMap_iff.2 ⟨_, h'.comp h⟩

theorem tMap_cancel {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h⟩ := tMap_iff.1 h
  obtain ⟨ψ, n⟩ := tMap_iff.1 n
  obtain ⟨φ', -, H⟩ := h.cancel n
  exact tMap_iff.2 ⟨_, H⟩

theorem exists_glue_tm (t t' : TObj g k J b s) {I : Type} (W : I → Scheme.{0}) (x : ∀ i, W i ⟶ S)
    (u : ∀ i, TObj g k J b (x i ≫ s)) (a : ∀ i, (u i).A.left ⟶ t.A.left) (a' : ∀ i, (u i).A.left ⟶ t'.A.left)
    (hx : ∀ i, IsOpenImmersion (x i)) (hc : ∀ p : S, ∃ i, p ∈ Set.range (x i))
    (ha : ∀ i, IsTM (u i) t (x i) (a i)) (ha' : ∀ i, IsTM (u i) t' (x i) (a' i))
    (hp : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ S), ∃ w : TObj g k J b (z ≫ s), TMap w t z)
    (hu : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ S) (w : TObj g k J b (z ≫ s)) φ φ', IsOpenImmersion z →
      IsTM w t' z φ → IsTM w t' z φ' → φ = φ') :
    ∃ φ : t.A.left ⟶ t'.A.left, ∀ i, a i ≫ φ = a' i := by
  have hao : ∀ i, IsOpenImmersion (a i) := fun i => MorphismProperty.of_isPullback (ha i).1.1.flip (hx i)
  refine exists_glue _ a a' hao (fun q => ?_) fun i i' y hy => ?_
  · obtain ⟨i, hi⟩ := hc (t.A.hom q)
    exact ⟨i, (range_of_isPullback (ha i).1.1 q).2 hi⟩
  · have := hx i
    have := hx i'
    have := hao i
    have h1 := (range_of_isPullback (ha i).1.1 (a i y)).1 ⟨y, rfl⟩
    have h2 := (range_of_isPullback (ha i').1.1 (a i y)).1 hy
    obtain ⟨R, z, hz, hq, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := t.A.hom (a i y)) ⟨h1, h2⟩
    have e1 := IsOpenImmersion.lift_fac (x i) z (fun p hp => (hr hp).1)
    have e2 := IsOpenImmersion.lift_fac (x i') z (fun p hp => (hr hp).2)
    obtain ⟨w, hw⟩ := hp R z
    obtain ⟨c, hw⟩ := tMap_iff.1 hw
    obtain ⟨d, hd, Hd⟩ := (ha i).cancel (hw.congr e1.symm rfl)
    obtain ⟨d', hd', Hd'⟩ := (ha i').cancel (hw.congr e2.symm rfl)
    have hco : IsOpenImmersion c := MorphismProperty.of_isPullback hw.1.1.flip hz
    have : IsOpenImmersion (d ≫ a i) := by rw [hd]; exact hco
    refine ⟨_, d, d', IsOpenImmersion.of_comp d (a i), ?_, hd.trans hd'.symm,
      hu R z w _ _ hz ((Hd.comp (ha' i)).congr e1 rfl) ((Hd'.comp (ha' i')).congr e2 rfl)⟩
    obtain ⟨q, hq⟩ := (range_of_isPullback hw.1.1 (a i y)).2 hq
    refine ⟨q, (a i).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hd, hq]

theorem tMap_of_loc (hG : Out.GlobalFnsSt) (t t' : TObj g k J b s)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (u : TObj g k J b (x ≫ s)),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x)
    (hp : ∀ (t : TObj g k J b s) (R : Type) [CommRing R] (z : Sp R ⟶ S), ∃ w : TObj g k J b (z ≫ s), TMap w t z)
    (hu : ∀ (t : TObj g k J b s) (R : Type) [CommRing R] (z : Sp R ⟶ S) (w : TObj g k J b (z ≫ s)) φ φ',
      IsOpenImmersion z → IsTM w t z φ → IsTM w t z φ' → φ = φ') : TMap t t' (𝟙 S) := by
  choose W x u hx hc ha ha' using h
  choose a ha using fun p => tMap_iff.1 (ha p)
  choose a' ha' using fun p => tMap_iff.1 (ha' p)
  obtain ⟨φ, hφ⟩ := exists_glue_tm t t' W x u a a' hx (fun p => ⟨p, hc p⟩) ha ha' (hp t) (hu t')
  obtain ⟨φ', hφ'⟩ := exists_glue_tm t' t W x u a' a hx (fun p => ⟨p, hc p⟩) ha' ha (hp t') (hu t)
  have ext : ∀ {Y : Scheme.{0}} {f f' : t.A.left ⟶ Y}, (∀ p, a p ≫ f = a p ≫ f') → f = f' := fun H =>
    hom_ext_loc fun q => ⟨_, a (t.A.hom q), MorphismProperty.of_isPullback (ha _).1.1.flip (hx _),
      (range_of_isPullback (ha _).1.1 q).2 (hc _), H _⟩
  have ext' : ∀ {Y : Scheme.{0}} {f f' : t'.A.left ⟶ Y}, (∀ p, a' p ≫ f = a' p ≫ f') → f = f' := fun H =>
    hom_ext_loc fun q => ⟨_, a' (t'.A.hom q), MorphismProperty.of_isPullback (ha' _).1.1.flip (hx _),
      (range_of_isPullback (ha' _).1.1 q).2 (hc _), H _⟩
  have : IsIso φ := ⟨φ', ext fun p => by rw [← Category.assoc, hφ, hφ', Category.comp_id],
    ext' fun p => by rw [← Category.assoc, hφ', hφ, Category.comp_id]⟩
  have gp : IsGrpPullback t.A t'.A (𝟙 S) φ :=
    isGrpPullback_of_loc φ (ext fun p => by rw [← Category.assoc, hφ, (ha p).1.1.w, (ha' p).1.1.w])
      fun p => ⟨W p, x p, (u p).A, inferInstance, a p, hx p, hc p, (ha p).1, by rw [hφ]; exact (ha' p).1⟩
  refine ⟨φ, gp, ?_, fun i => hom_ext_loc fun p => ⟨W p, x p, hx p, hc p, ?_⟩, fun j => ext fun p => ?_⟩
  · refine lbIso_of_loc hG t.ab t.isLB (pull_isLB t'.isLB _) t.rigid (PolBaseChange.rigidified_pull gp t'.rigid)
      fun p => ⟨W p, _, x p, a p, _, hx p, hc p, (ha p).1.1, ?_⟩
    have H := (ha' p).2.1
    rw [← hφ] at H
    exact LBIso.trans (pull_isLB t.isLB _) (u p).isLB (pull_isLB (pull_isLB t'.isLB _) _) (ha p).2.1.symm
      (LBIso.trans (u p).isLB (pull_isLB t'.isLB _) (pull_isLB (pull_isLB t'.isLB _) _) H
        (lbIso_pull_pull t'.isLB φ (a p)).symm)
  · rw [← Category.assoc, ← (ha p).2.2.1, Category.assoc, hφ, (ha' p).2.2.1, Category.id_comp]
  · rw [← Category.assoc, ← (ha p).2.2.2, Category.assoc, hφ, (ha' p).2.2.2, ← Category.assoc, hφ]

end GlobalTheory.FamRep
end
