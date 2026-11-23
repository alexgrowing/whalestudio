import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsogOfSurjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsogenyPullbackHeckeModuliObject
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.QuotGlue

section Cover

variable {I : Type} {X Y S : Scheme.{0}} {V : I → Scheme.{0}}

theorem cover_ext (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) {a b : X ⟶ Y}
    (h : ∀ i, f i ≫ a = f i ≫ b) : a = b :=
  Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers I V f hc) a b h

theorem cover_glue (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) (g : ∀ i, V i ⟶ Y)
    (h : ∀ i j, pullback.fst (f i) (f j) ≫ g i = pullback.snd _ _ ≫ g j) : ∃ a : X ⟶ Y, ∀ i, f i ≫ a = g i :=
  ⟨Scheme.Cover.glueMorphisms (Scheme.Cover.mkOfCovers I V f hc) g h,
    Scheme.Cover.ι_glueMorphisms (Scheme.Cover.mkOfCovers I V f hc) g h⟩

theorem cover_pull {f : ∀ i, V i ⟶ S} (hc : ∀ x, ∃ i y, f i y = x) {p : X ⟶ S} {W : I → Scheme.{0}}
    {φ : ∀ i, W i ⟶ X} {q : ∀ i, W i ⟶ V i} (h : ∀ i, IsPullback (φ i) (q i) p (f i)) (x : X) : ∃ i y, φ i y = x := by
  obtain ⟨i, y, hy⟩ := hc (p x)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (h i) x y hy.symm
  exact ⟨i, z, hz⟩

theorem cover_prop (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] (f : ∀ i, V i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) {p : X ⟶ S} {W : I → Scheme.{0}}
    {φ : ∀ i, W i ⟶ X} {q : ∀ i, W i ⟶ V i} (h : ∀ i, IsPullback (φ i) (q i) p (f i)) (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers I V f hc) fun i => ?_
  change Q (pullback.snd p (f i))
  rw [← (h i).isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem exists_point_lift (f : ∀ i, V i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x)
    {k : Type} [Field k] (x : Sp k ⟶ S) : ∃ (i : I) (x' : Sp k ⟶ V i), x' ≫ f i = x := by
  obtain ⟨i, y, hy⟩ := hc (x (default : PrimeSpectrum k))
  refine ⟨i, IsOpenImmersion.lift (f i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  exact ⟨y, hy.trans (congrArg x (Subsingleton.elim (α := PrimeSpectrum k) _ _))⟩

end Cover

section Grp

variable {I : Type} {S : Scheme.{0}} {V : I → Scheme.{0}} {f : ∀ i, V i ⟶ S} [∀ i, IsOpenImmersion (f i)]
  {G₁ G₂ : Over S} {G₁' G₂' : ∀ i, Over (V i)}
  [GrpObj G₁] [GrpObj G₂] [∀ i, GrpObj (G₁' i)] [∀ i, GrpObj (G₂' i)]
  {φ₁ : ∀ i, (G₁' i).left ⟶ G₁.left} {φ₂ : ∀ i, (G₂' i).left ⟶ G₂.left}

theorem mul_comp (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsGrpPullback (G₁' i) G₁ (f i) (φ₁ i))
    (h₂ : ∀ i, IsGrpPullback (G₂' i) G₂ (f i) (φ₂ i)) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i) [∀ i, IsMonHom (ψ' i)]
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) (T : Over S) (x y : T ⟶ G₁) :
    (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  refine Over.OverMorphism.ext (cover_ext (fun i => pullback.fst T.hom (f i))
    (cover_pull hc fun i => IsPullback.of_hasPullback T.hom (f i)) fun i => ?_)
  have H := IsPullback.of_hasPullback T.hom (f i)
  let q := pullback.fst T.hom (f i)
  let W : Over (V i) := Over.mk (pullback.snd T.hom (f i))
  let l : (T ⟶ G₁) → (W ⟶ G₁' i) := fun z => Over.homMk
    ((h₁ i).1.lift (q ≫ z.left) (pullback.snd T.hom (f i)) (by rw [Category.assoc, Over.w z]; exact H.w))
    ((h₁ i).1.lift_snd _ _ _)
  have hl : ∀ z, (l z).left ≫ φ₁ i = q ≫ z.left := fun z => (h₁ i).1.lift_fst _ _ _
  let q' : Over.mk (W.hom ≫ f i) ⟶ T := Over.homMk q H.w
  have hl' : ∀ z, (q' ≫ z ≫ ψ).left = (l z ≫ ψ' i).left ≫ φ₂ i := fun z => by
    show q ≫ z.left ≫ ψ.left = ((l z).left ≫ (ψ' i).left) ≫ φ₂ i
    rw [Category.assoc, hψ, ← Category.assoc (l z).left, hl, Category.assoc]
  have e₁ := (h₁ i).2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
  have e₂ := (h₂ i).2 W (l x ≫ ψ' i) (l y ≫ ψ' i) (q' ≫ x ≫ ψ) (q' ≫ y ≫ ψ) (hl' x) (hl' y)
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← MonObj.mul_comp (l x) (l y) (ψ' i)] at e₂
  replace e₂ : _ = (l x * l y).left ≫ (ψ' i).left ≫ φ₂ i := e₂.trans (Category.assoc _ _ _)
  rw [hψ, ← Category.assoc, ← e₁] at e₂
  refine Eq.trans ?_ e₂.symm
  exact (Category.assoc _ _ _).symm

theorem isMonHom (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsGrpPullback (G₁' i) G₁ (f i) (φ₁ i))
    (h₂ : ∀ i, IsGrpPullback (G₂' i) G₂ (f i) (φ₂ i)) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i) [∀ i, IsMonHom (ψ' i)]
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) : IsMonHom ψ := by
  refine ⟨?_, ?_⟩
  · have h := mul_comp hc h₁ h₂ ψ ψ' hψ (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ ψ = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul_comp hc h₁ h₂ ψ ψ' hψ (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

omit [GrpObj G₁] [∀ i, GrpObj (G₁' i)] in

theorem kerSet (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsPullback (φ₁ i) (G₁' i).hom G₁.hom (f i))
    (h₂ : ∀ i, IsPullback (φ₂ i) (G₂' i).hom G₂.hom (f i))
    (he : ∀ i, η[G₂' i].left ≫ φ₂ i = f i ≫ η[G₂].left) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i)
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) (K : Set G₁.left) (hK : ∀ i, KerSet (ψ' i) (φ₁ i ⁻¹' K)) :
    KerSet ψ K := by
  intro k _ _ x z
  obtain ⟨i, x', hj⟩ := exists_point_lift f hc x
  let z' : Over.mk x' ⟶ G₁' i := Over.homMk ((h₁ i).lift z.left x' (by rw [Over.w z]; exact hj.symm))
    ((h₁ i).lift_snd _ _ _)
  have hz : z'.left ≫ φ₁ i = z.left := (h₁ i).lift_fst _ _ _
  have a₁ : (z' ≫ ψ' i).left ≫ φ₂ i = (z ≫ ψ).left := by
    rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, hz]
    rfl
  have a₂ : (1 : Over.mk x' ⟶ G₂' i).left ≫ φ₂ i = (1 : Over.mk x ⟶ G₂).left := by
    show (x' ≫ η[G₂' i].left) ≫ φ₂ i = x ≫ η[G₂].left
    rw [Category.assoc, he, ← Category.assoc, hj]
  have b₁ : z ≫ ψ = 1 ↔ z' ≫ ψ' i = 1 :=
    ⟨fun h => Over.OverMorphism.ext ((h₂ i).hom_ext (by rw [a₁, a₂, h]) ((Over.w _).trans (Over.w _).symm)),
      fun h => Over.OverMorphism.ext (by rw [← a₁, ← a₂, h])⟩
  have pt : ∀ a, φ₁ i (z'.left a) = z.left a := fun a => congrArg (fun q => q a) hz
  rw [b₁, hK i k x' z']
  constructor
  · rintro h _ ⟨a, rfl⟩
    rw [← pt]
    exact h ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    show φ₁ i (z'.left a) ∈ K
    rw [pt]
    exact h ⟨_, rfl⟩

end Grp

theorem lbIso_of_cover {I : Type} {S : Scheme.{0}} {V X' : I → Scheme.{0}} [IsReduced S] (A : Over S) [GrpObj A]
    [IsCommMonObj A] (M : LB A.left) (hA : IsAbelianScheme A) (hM : M.IsLB) (ha : Out.RelAmple A M)
    {f : ∀ i, V i ⟶ S} (hc : ∀ x, ∃ i y, f i y = x)
    {φ : ∀ i, X' i ⟶ A.left} {g : ∀ i, X' i ⟶ V i} (h : ∀ i, IsPullback (φ i) (g i) A.hom (f i)) {P Q : LB A.left}
    (hP : P.IsLB) (hQ : Q.IsLB) (hi : ∀ i, LBIso (P.pull (φ i)) (Q.pull (φ i))) (s : (P.pull (eSec A)).Gen)
    (hs : s.IsGen) (t : (Q.pull (eSec A)).Gen) (ht : t.IsGen) : LBIso P Q := by
  refine GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds S A M hA hM ha S A.left (𝟙 S) (𝟙 _) A.hom (LB.div Q P)
    (IsPullback.id_horiz _) (LB.isLB_div hQ hP) ?_ (eSec A) (Over.w η[A]) ?_
  · refine dense_univ.mono fun p _ => ?_
    obtain ⟨i, p', rfl⟩ := hc p
    obtain ⟨w, hw⟩ := hi i
    obtain ⟨c, hc⟩ := gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q (φ i)) w hw
    let x' : Sp ((V i).residueField p') ⟶ V i := (V i).fromSpecResidueField p'
    refine ⟨(V i).residueField p', inferInstance, x' ≫ f i, pullback (g i) x', pullback.fst (g i) x' ≫ φ i,
      pullback.snd (g i) x',
      ⟨(default : PrimeSpectrum ((V i).residueField p')), congrArg (f i) (Scheme.fromSpecResidueField_apply p' _)⟩,
      (IsPullback.of_hasPullback (g i) x').paste_horiz (h i), ?_⟩
    exact gen_chartPull (chartPullSame (LB.div Q P) (K := PUnit) _ (fun _ => φ i) (fun _ => 1) (pullback.fst (g i) x')
      fun _ => rfl) c hc
  · obtain ⟨w, hw⟩ := GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    exact gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q _) w hw

set_option backward.isDefEq.respectTransparency.types false in
theorem isFinite_local : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem isIsog_of_cover {I : Type} {p : ℕ} {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp (KA l)} {V : I → Scheme.{0}}
    {s' : ∀ i, V i ⟶ Sp (KA l)} {f : ∀ i, V i ⟶ S} [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x)
    {o₁ o₂ : Ob D l s} {o₁' o₂' : ∀ i, Ob D l (s' i)} (n₁ : ∀ i, ObjMap (o₁' i) o₁ (f i))
    (n₂ : ∀ i, ObjMap (o₂' i) o₂ (f i)) (ψ : o₁.t.G ⟶ o₂.t.G) (ψ' : ∀ i, (o₁' i).t.G ⟶ (o₂' i).t.G)
    (hψ : ∀ i, (ψ' i).left ≫ (n₂ i).cm.F = (n₁ i).cm.F ≫ ψ.left) (hI : ∀ i, IsIsog (o₁' i) (o₂' i) p (ψ' i)) :
    IsIsog o₁ o₂ p ψ := by
  have hm := fun i => (hI i).1.1
  have io₁ : ∀ i, IsOpenImmersion (n₁ i).cm.F := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n₁ i).cart.1.flip inferInstance
  have io₂ : ∀ i, IsOpenImmersion (n₂ i).cm.F := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n₂ i).cart.1.flip inferInstance
  have c₁ := cover_pull hc fun i => (n₁ i).cart.1
  have c₂ := cover_pull hc fun i => (n₂ i).cart.1
  have pb : ∀ i, IsPullback (n₁ i).cm.F (ψ' i).left ψ.left (n₂ i).cm.F := fun i => by
    refine IsPullback.of_bot ?_ (hψ i).symm (n₂ i).cart.1
    rw [Over.w, Over.w]
    exact (n₁ i).cart.1
  have hmon : IsMonHom ψ := isMonHom hc (fun i => (n₁ i).cart) (fun i => (n₂ i).cart) ψ ψ' hψ
  have sec : ∀ {a : 𝟙_ (Over S) ⟶ o₁.t.G} {b : 𝟙_ (Over S) ⟶ o₂.t.G} {a' : ∀ i, 𝟙_ (Over (V i)) ⟶ (o₁' i).t.G}
      {b' : ∀ i, 𝟙_ (Over (V i)) ⟶ (o₂' i).t.G}, (∀ i, (a' i).left ≫ (n₁ i).cm.F = f i ≫ a.left) →
      (∀ i, (b' i).left ≫ (n₂ i).cm.F = f i ≫ b.left) →
      (∀ i, a' i ≫ ψ' i = b' i) → a ≫ ψ = b := fun {a b a' b'} ha hb h =>
    Over.OverMorphism.ext (cover_ext f hc fun i => by
      rw [← hb, ← h, Over.comp_left, Over.comp_left, Category.assoc, hψ, ← Category.assoc, ← Category.assoc, ha])
  have : IsZariskiLocalAtTarget @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale)
  have := isFinite_local
  refine ⟨⟨hmon, cover_prop @IsFinite _ c₂ pb fun i => (hI i).1.2.1, cover_prop @Etale _ c₂ pb fun i => (hI i).1.2.2.1,
    cover_prop @Surjective _ c₂ pb fun i => (hI i).1.2.2.2.1,
    fun a => Over.OverMorphism.ext (cover_ext _ c₁ fun i => ?_), ?_⟩, fun p' hp a =>
    ⟨sec (fun i => (n₁ i).eta _) (fun i => (n₂ i).eta _) fun i => ((hI i).2 p' hp a).1,
      sec (fun i => (n₁ i).etaA _) (fun i => (n₂ i).etaA _) fun i => ((hI i).2 p' hp a).2⟩⟩
  · have e := congrArg (fun q => q.left) ((hI i).1.2.2.2.2.1 a)
    simp only [Over.comp_left] at e ⊢
    rw [← Category.assoc, ← (n₁ i).act, Category.assoc, ← hψ, ← Category.assoc, e, Category.assoc, (n₂ i).act,
      ← Category.assoc, hψ, Category.assoc]
  · have hP : (lbPow o₁.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁.t.PP.isLB _ _
    have hQ := pull_isLB o₂.t.PP.isLB ψ.left
    obtain ⟨c, hc'⟩ := GlobalTheory.IsogDescent.exists_gen_pow o₁.t.PP.L _ ((p ^ 2 : ℕ) : ℤ) o₁.t.PP.rig o₁.t.PP.rigGen
    obtain ⟨d₁, hd₁⟩ := gen_chartPull (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ))
      (eSec o₁.t.G) (fun _ => eSec o₁.t.G) fun _ => (Category.comp_id _).symm) c hc'
    obtain ⟨d₂, hd₂⟩ := gen_chartPull (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) (fun _ => 1)
      (eSec o₁.t.G) (fun _ => eSec o₂.t.G) fun _ => (congrArg (fun q => q.left) hmon.one_hom).symm)
      o₂.t.PP.rig o₂.t.PP.rigGen
    refine lbIso_of_cover o₁.t.G o₁.t.PP.L (GlobalTheory.ObjDim.isAbelianScheme o₁) o₁.t.PP.isLB o₁.ample hc
      (fun i => (n₁ i).cart.1) hP hQ (fun i => ?_) d₁ hd₁ d₂ hd₂
    have hP' : (lbPow (o₁' i).t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb (o₁' i).t.PP.isLB _ _
    obtain ⟨w₁, hw₁, -⟩ := (n₁ i).lin
    obtain ⟨w₂, hw₂, -⟩ := (n₂ i).lin
    have i₁ : LBIso (lbPow (o₁' i).t.PP.L (p ^ 2)) ((lbPow o₁.t.PP.L (p ^ 2)).pull (n₁ i).cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) _ (n₁ i).cm.F _
        fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
        (iso_linComb ((isGen_iff w₁).1 hw₁) (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ)))
    have i₂ : LBIso ((o₂' i).t.PP.L.pull (ψ' i).left) ((o₂.t.PP.L.pull ψ.left).pull (n₁ i).cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) _ (n₁ i).cm.F _
        fun _ => hψ i)
        (iso_linComb ((isGen_iff w₂).1 hw₂) (K := PUnit) (fun _ => (ψ' i).left) (fun _ => 1))
    exact LBIso.trans (pull_isLB hP _) hP' (pull_isLB hQ _) i₁.symm
      (LBIso.trans hP' (pull_isLB (o₂' i).t.PP.isLB _) (pull_isLB hQ _) (hI i).1.2.2.2.2.2 i₂)

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} (f : S' ⟶ S) (hf : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [hf]; exact ((congrArg (s' ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)).symm) o

theorem exists_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') : ∃ m'' : ObjMap o'' o (f' ≫ f), m''.cm.F = m'.cm.F ≫ m.cm.F :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem exists_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (hg : f' ≫ f = g)
    (m : ObjMap o' o f) (m'' : ObjMap o'' o g) : ∃ m' : ObjMap o'' o' f', m''.cm.F = m'.cm.F ≫ m.cm.F := by
  subst hg
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem exists_restrict {p : ℕ} {S V T X : Scheme.{0}} {s : S ⟶ Sp (KA l)} {sV : V ⟶ Sp (KA l)} {sT : T ⟶ Sp (KA l)}
    {sX : X ⟶ Sp (KA l)} {o : Ob D l s} {K : Set o.t.G.left} {f : V ⟶ S} {oV a : Ob D l sV} (m : ObjMap oV o f)
    {ψ : oV.t.G ⟶ a.t.G} (hI : IsIsog oV a p ψ) (hK : KerSet ψ (m.cm.F ⁻¹' K)) {u : Ob D l sX} {c : V ⟶ X}
    (n : ObjMap a u c) {g : T ⟶ S} {oT : Ob D l sT} (mT : ObjMap oT o g) (g' : T ⟶ V) (hg : g' ≫ f = g)
    (hs : g' ≫ sV = sT) :
    ∃ (r : oT.t.G.left ⟶ oV.t.G.left) (aT : Ob D l sT) (ψT : oT.t.G ⟶ aT.t.G) (nT : ObjMap aT u (g' ≫ c)),
      r ≫ m.cm.F = mT.cm.F ∧ IsIsog oT aT p ψT ∧ KerSet ψT (mT.cm.F ⁻¹' K) ∧
        ψT.left ≫ nT.cm.F = r ≫ ψ.left ≫ n.cm.F := by
  obtain ⟨r, hr⟩ := exists_cancel hg m mT
  obtain ⟨aT, ⟨b⟩⟩ := exists_pull g' hs a
  obtain ⟨⟨ψT, hψ, -⟩, h⟩ := GlobalTheory.HkFam.isog_pull E H D l p V T sV sT g' oV a oT aT r b ψ
  obtain ⟨nT, hn⟩ := exists_comp n b
  have hψ' : ψT.left ≫ b.cm.F = r.cm.F ≫ ψ.left := hψ
  refine ⟨r.cm.F, aT, ψT, nT, hr.symm, (h ψT hψ).1 hI, ?_, ?_⟩
  · have := (h ψT hψ).2 _ hI.1.1 hK
    rw [hr]
    convert this using 1
    ext x
    simp only [Set.mem_preimage, Scheme.Hom.comp_apply]
  · rw [hn, reassoc_of% hψ']

theorem overlap (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} {S V₁ V₂ : Scheme.{0}} [IsReduced S]
    {s : S ⟶ Sp (KA l)} {o : Ob D l s} {K : Set o.t.G.left} (hA : admitted l 𝔓 p) (hH : HeckeSet D o.t 𝔓 p i K)
    {f₁ : V₁ ⟶ S} {f₂ : V₂ ⟶ S} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {o₁ a₁ : Ob D l (f₁ ≫ s)} {o₂ a₂ : Ob D l (f₂ ≫ s)} (m₁ : ObjMap o₁ o f₁) (m₂ : ObjMap o₂ o f₂)
    {ψ₁ : o₁.t.G ⟶ a₁.t.G} {ψ₂ : o₂.t.G ⟶ a₂.t.G} (hI₁ : IsIsog o₁ a₁ p ψ₁) (hI₂ : IsIsog o₂ a₂ p ψ₂)
    (hK₁ : KerSet ψ₁ (m₁.cm.F ⁻¹' K)) (hK₂ : KerSet ψ₂ (m₂.cm.F ⁻¹' K)) {c₁ : V₁ ⟶ Xo.X} {c₂ : V₂ ⟶ Xo.X}
    (hc₁ : c₁ ≫ Xo.s = f₁ ≫ s) (hc₂ : c₂ ≫ Xo.s = f₂ ≫ s) (n₁ : ObjMap a₁ Xo.univ c₁) (n₂ : ObjMap a₂ Xo.univ c₂) :
    pullback.fst f₁ f₂ ≫ c₁ = pullback.snd f₁ f₂ ≫ c₂ ∧
      pullback.fst m₁.cm.F m₂.cm.F ≫ ψ₁.left ≫ n₁.cm.F = pullback.snd m₁.cm.F m₂.cm.F ≫ ψ₂.left ≫ n₂.cm.F := by
  let g : pullback f₁ f₂ ⟶ S := pullback.fst f₁ f₂ ≫ f₁
  have : IsReduced (pullback f₁ f₂) := isReduced_of_isOpenImmersion g
  have e₂ : pullback.snd f₁ f₂ ≫ f₂ = g := pullback.condition.symm
  obtain ⟨oT, ⟨mT⟩⟩ := exists_pull g rfl o
  have hs₁ : pullback.fst f₁ f₂ ≫ f₁ ≫ s = g ≫ s := (Category.assoc _ _ _).symm
  have hs₂ : pullback.snd f₁ f₂ ≫ f₂ ≫ s = g ≫ s := by rw [← e₂, Category.assoc]
  obtain ⟨r₁, b₁, χ₁, k₁, hr₁, hJ₁, hL₁, hk₁⟩ := exists_restrict m₁ hI₁ hK₁ n₁ mT (pullback.fst f₁ f₂) rfl hs₁
  obtain ⟨r₂, b₂, χ₂, k₂, hr₂, hJ₂, hL₂, hk₂⟩ := exists_restrict m₂ hI₂ hK₂ n₂ mT (pullback.snd f₁ f₂) e₂ hs₂
  have hHT := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S _ o.t oT.t g mT.toSABMap o.proper).2 K).1 hH
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i _ (g ≫ s) oT b₁ b₂ χ₁ χ₂ _ _ _ k₁ k₂ hA hHT
    (by rw [Category.assoc, hc₁, hs₁]) (by rw [Category.assoc, hc₂, hs₂]) hJ₁ hJ₂ hL₁ hL₂
  refine ⟨h₁, ?_⟩
  have h₃ : r₁ ≫ ψ₁.left ≫ n₁.cm.F = r₂ ≫ ψ₂.left ≫ n₂.cm.F := hk₁.symm.trans (Eq.trans h₂ hk₂)
  have io₁ : IsOpenImmersion m₁.cm.F :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₁.cart.1.flip inferInstance
  have io₂ : IsOpenImmersion m₂.cm.F :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₂.cart.1.flip inferInstance
  let t : pullback m₁.cm.F m₂.cm.F ⟶ pullback f₁ f₂ :=
    pullback.lift (pullback.fst _ _ ≫ o₁.t.G.hom) (pullback.snd _ _ ≫ o₂.t.G.hom) (by
      rw [Category.assoc, Category.assoc, ← m₁.cart.1.w, ← m₂.cart.1.w, pullback.condition_assoc])
  let w : pullback m₁.cm.F m₂.cm.F ⟶ oT.t.G.left := mT.cart.1.lift (pullback.fst _ _ ≫ m₁.cm.F) t (by
    rw [Category.assoc, m₁.cart.1.w]
    simp only [t, g, pullback.lift_fst_assoc, Category.assoc])
  have hw : w ≫ mT.cm.F = pullback.fst _ _ ≫ m₁.cm.F := mT.cart.1.lift_fst _ _ _
  have w₁ : w ≫ r₁ = pullback.fst _ _ := by
    rw [← cancel_mono m₁.cm.F, Category.assoc, hr₁, hw]
  have w₂ : w ≫ r₂ = pullback.snd _ _ := by
    rw [← cancel_mono m₂.cm.F, Category.assoc, hr₂, hw, pullback.condition]
  rw [← w₁, ← w₂]
  exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) h₃).trans (Category.assoc _ _ _).symm)

end GlobalTheory.QuotGlue

open GlobalTheory.QuotGlue in

theorem GlobalTheory.hasQuot_of_openCover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → (∀ q : S, ∃ (U : S.Opens) (o' : Ob D l (U.ι ≫ s)) (m : ObjMap o' o U.ι), q ∈ U ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K)) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S _ s o K hA hH h
  choose U o' m hU a ψ hI hK using h
  have hrep : ∀ q, ∃ c : (U q).toScheme ⟶ Xo.X, c ≫ Xo.s = (U q).ι ≫ s ∧ Nonempty (ObjMap (a q) Xo.univ c) :=
    fun q => (Xo.rep _ _ (isReduced_of_isOpenImmersion (U q).ι) (a q)).exists
  choose c hc hn using hrep
  have n := fun q => (hn q).some
  have cov : ∀ x : S, ∃ (q : S) (y : (U q).toScheme), (U q).ι y = x := fun x => ⟨x, ⟨x, hU x⟩, rfl⟩
  have io : ∀ q, IsOpenImmersion (m q).cm.F := fun q =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (m q).cart.1.flip inferInstance
  have covG := cover_pull cov fun q => (m q).cart.1
  have ov := fun q q' => overlap Xo hA hH (m q) (m q') (hI q) (hI q') (hK q) (hK q') (hc q) (hc q') (n q) (n q')
  obtain ⟨F, hF⟩ := cover_glue (fun q => (U q).ι) cov c fun q q' => (ov q q').1
  obtain ⟨Φ, hΦ⟩ := cover_glue (fun q => (m q).cm.F) covG (fun q => (ψ q).left ≫ (n q).cm.F) fun q q' => (ov q q').2
  have hFs : F ≫ Xo.s = s := cover_ext _ cov fun q => by rw [← Category.assoc, hF, hc]
  obtain ⟨o₂, ⟨n₂⟩⟩ := exists_pull F hFs Xo.univ
  have hw : Φ ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ F := cover_ext _ covG fun q => by
    rw [← Category.assoc, hΦ, Category.assoc, (n q).cart.1.w, ← Category.assoc, Over.w, ← Category.assoc,
      (m q).cart.1.w, Category.assoc, hF]
  let χ : o.t.G ⟶ o₂.t.G := Over.homMk (n₂.cart.1.lift Φ o.t.G.hom hw) (n₂.cart.1.lift_snd _ _ _)
  have hχ : χ.left ≫ n₂.cm.F = Φ := n₂.cart.1.lift_fst _ _ _
  choose b hb using fun q => exists_cancel (hF q) n₂ (n q)
  have hψ : ∀ q, (ψ q).left ≫ (b q).cm.F = (m q).cm.F ≫ χ.left := fun q => by
    refine n₂.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hχ, hΦ, hb]
    · rw [Category.assoc, Category.assoc, Over.w, (b q).cart.1.w, (m q).cart.1.w, ← Category.assoc, Over.w]
  exact ⟨o₂, χ, isIsog_of_cover cov m b χ ψ hψ hI, kerSet cov (fun q => (m q).cart.1) (fun q => (b q).cart.1)
    (fun q => (b q).cm.e_comm.trans (by rw [(b q).base]; rfl)) χ ψ hψ K hK⟩

end
