import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawReducedBaseAbelianSchemeOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCmTripleMapDescendGroupQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.IsogDescent

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G₁ G₂ : Over S} {G₁' G₂' : Over S'}

theorem over_ext {T G : Over S} [IsReduced T.left] [IsSeparated G.hom] {a b : T ⟶ G} {W : Scheme.{0}}
    (q : W ⟶ T.left) [Surjective q] (h : q ≫ a.left = q ≫ b.left) : a = b :=
  Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom ((Over.w a).trans (Over.w b).symm) q h)

variable [GrpObj G₁] [GrpObj G₂] [GrpObj G₁'] [GrpObj G₂'] {φ₁ : G₁'.left ⟶ G₁.left} {φ₂ : G₂'.left ⟶ G₂.left}

theorem mul_comp [Surjective f] [IsSeparated G₂.hom] (h₁ : IsGrpPullback G₁' G₁ f φ₁)
    (h₂ : IsGrpPullback G₂' G₂ f φ₂) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂') [IsMonHom ψ']
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (T : Over S) [IsReduced T.left] (x y : T ⟶ G₁) :
    (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  have H := IsPullback.of_hasPullback T.hom f
  let q := pullback.fst T.hom f
  let W : Over S' := Over.mk (pullback.snd T.hom f)
  let l : (T ⟶ G₁) → (W ⟶ G₁') := fun z => Over.homMk
    (h₁.1.lift (q ≫ z.left) (pullback.snd T.hom f) (by rw [Category.assoc, Over.w z]; exact H.w))
    (h₁.1.lift_snd _ _ _)
  have hl : ∀ z, (l z).left ≫ φ₁ = q ≫ z.left := fun z => h₁.1.lift_fst _ _ _
  let q' : Over.mk (W.hom ≫ f) ⟶ T := Over.homMk q H.w
  have hl' : ∀ z, (q' ≫ z ≫ ψ).left = (l z ≫ ψ').left ≫ φ₂ := fun z => by
    show q ≫ z.left ≫ ψ.left = ((l z).left ≫ ψ'.left) ≫ φ₂
    rw [Category.assoc, hψ, ← Category.assoc (l z).left, hl, Category.assoc]
  have e₁ := h₁.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
  have e₂ := h₂.2 W (l x ≫ ψ') (l y ≫ ψ') (q' ≫ x ≫ ψ) (q' ≫ y ≫ ψ) (hl' x) (hl' y)
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← MonObj.mul_comp (l x) (l y) ψ'] at e₂
  replace e₂ : _ = (l x * l y).left ≫ ψ'.left ≫ φ₂ := e₂.trans (Category.assoc _ _ _)
  rw [hψ, ← Category.assoc, ← e₁] at e₂
  refine over_ext q ?_
  refine Eq.trans ?_ e₂.symm
  exact (Category.assoc _ _ _).symm

theorem isMonHom [IsReduced S] [Surjective f] [Smooth G₁.hom] [IsSeparated G₂.hom] (h₁ : IsGrpPullback G₁' G₁ f φ₁)
    (h₂ : IsGrpPullback G₂' G₂ f φ₂) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂') [IsMonHom ψ']
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) : IsMonHom ψ := by
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have : Smooth (G₁ ⊗ G₁).hom := inferInstanceAs (Smooth (pullback.fst G₁.hom G₁.hom ≫ G₁.hom))
  have : IsReduced (G₁ ⊗ G₁).left := GlobalTheory.isReduced_of_smooth_of_isReduced (G₁ ⊗ G₁).hom
  refine ⟨?_, ?_⟩
  · have h := mul_comp h₁ h₂ ψ ψ' hψ (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ ψ = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul_comp h₁ h₂ ψ ψ' hψ (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem kerSet [Surjective f] [IsSeparated G₂.hom] (h₁ : IsPullback φ₁ G₁'.hom G₁.hom f)
    (h₂ : IsPullback φ₂ G₂'.hom G₂.hom f) (he : η[G₂'].left ≫ φ₂ = f ≫ η[G₂].left) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂')
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (K : Set G₁.left) (hK : KerSet ψ' (φ₁ ⁻¹' K)) : KerSet ψ K := by
  intro k _ _ x z
  obtain ⟨w, -⟩ := (pullback.fst x f).surjective (default : PrimeSpectrum k)
  let k' := AlgebraicClosure ((pullback x f).residueField w)
  let u : Sp k' ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField w) k')) ≫ (pullback x f).fromSpecResidueField w
  let j : Sp k' ⟶ Sp k := u ≫ pullback.fst x f
  let x' : Sp k' ⟶ S' := u ≫ pullback.snd x f
  have hj : j ≫ x = x' ≫ f := by simp only [j, x', Category.assoc, pullback.condition]
  have : Surjective j := ⟨fun a => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  let z' : Over.mk x' ⟶ G₁' := Over.homMk (h₁.lift (j ≫ z.left) x' (by rw [Category.assoc, Over.w z]; exact hj))
    (h₁.lift_snd _ _ _)
  have hz : z'.left ≫ φ₁ = j ≫ z.left := h₁.lift_fst _ _ _
  have a₁ : (z' ≫ ψ').left ≫ φ₂ = j ≫ (z ≫ ψ).left := by
    rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, hz, Category.assoc]
    rfl
  have a₂ : (1 : Over.mk x' ⟶ G₂').left ≫ φ₂ = j ≫ (1 : Over.mk x ⟶ G₂).left := by
    show (x' ≫ η[G₂'].left) ≫ φ₂ = j ≫ x ≫ η[G₂].left
    rw [Category.assoc, he, ← Category.assoc, ← hj, Category.assoc]
  have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have b₁ : z ≫ ψ = 1 ↔ z' ≫ ψ' = 1 :=
    ⟨fun h => Over.OverMorphism.ext (h₂.hom_ext (by rw [a₁, a₂, h]) ((Over.w _).trans (Over.w _).symm)),
      fun h => over_ext (T := Over.mk x) j (by rw [← a₁, ← a₂, h])⟩
  have pt : ∀ a, φ₁ (z'.left a) = z.left (j a) := fun a => congrArg (fun q => q a) hz
  rw [b₁, hK k' x' z']
  constructor
  · rintro h _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := j.surjective a
    rw [← pt]
    exact h ⟨a', rfl⟩
  · rintro h _ ⟨a, rfl⟩
    show φ₁ (z'.left a) ∈ K
    rw [pt]
    exact h ⟨_, rfl⟩

end Grp

section Bundle

theorem exists_gen_pow {X Y : Scheme.{0}} (L : LB X) (e : Y ⟶ X) (n : ℤ) (t : (L.pull e).Gen) (ht : t.IsGen) :
    ∃ c : (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => n)).Gen, c.IsGen := by
  refine ⟨⟨fun j => (t.s j) ^ n⟩, fun i j => ?_⟩
  refine (map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans ((mul_zpow _ _ _).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
  simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem lbIso_of_surjective {S S' X' : Scheme.{0}} [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (M : LB A.left) (hA : IsAbelianScheme A) (hM : M.IsLB) (ha : Out.RelAmple A M) {f : S' ⟶ S} [Surjective f]
    {φ : X' ⟶ A.left} {g : X' ⟶ S'} (h : IsPullback φ g A.hom f) {P Q : LB A.left} (hP : P.IsLB) (hQ : Q.IsLB)
    (hi : LBIso (P.pull φ) (Q.pull φ)) (s : (P.pull (eSec A)).Gen) (hs : s.IsGen) (t : (Q.pull (eSec A)).Gen)
    (ht : t.IsGen) : LBIso P Q := by
  refine GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds S A M hA hM ha S A.left (𝟙 S) (𝟙 _) A.hom (LB.div Q P)
    (IsPullback.id_horiz _) (LB.isLB_div hQ hP) ?_ (eSec A) (Over.w η[A]) ?_
  · obtain ⟨w, hw⟩ := hi
    obtain ⟨c, hc⟩ := gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q φ) w hw
    refine dense_univ.mono fun p _ => ?_
    obtain ⟨p', rfl⟩ := f.surjective p
    let x' : Sp (S'.residueField p') ⟶ S' := S'.fromSpecResidueField p'
    refine ⟨S'.residueField p', inferInstance, x' ≫ f, pullback g x', pullback.fst g x' ≫ φ, pullback.snd g x',
      ⟨(default : PrimeSpectrum (S'.residueField p')), congrArg f (Scheme.fromSpecResidueField_apply p' _)⟩,
      (IsPullback.of_hasPullback g x').paste_horiz h, ?_⟩
    exact gen_chartPull (chartPullSame (LB.div Q P) (K := PUnit) _ (fun _ => φ) (fun _ => 1) (pullback.fst g x')
      fun _ => rfl) c hc
  · obtain ⟨w, hw⟩ := GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    exact gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q _) w hw

end Bundle

end GlobalTheory.IsogDescent

open GlobalTheory.IsogDescent in

theorem GlobalTheory.isIsog_of_surjective_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G) (ψ' : o₁'.t.G ⟶ o₂'.t.G), Surjective f → ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → IsIsog o₁' o₂' p ψ' → IsFinite ψ.left → Etale ψ.left → IsIsog o₁ o₂ p ψ ∧ ∀ K, KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) → KerSet ψ K := by
  intro E _ _ _ H D l p S S' _ s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ ψ' hf hψ ⟨⟨hm, _, _, hsurj, hact, hL⟩, hlev⟩ hfin het
  have := o₁.t.semi.smooth
  have := o₂.proper
  have : IsReduced o₁.t.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced o₁.t.G.hom
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have : Surjective n₁.cm.F := MorphismProperty.of_isPullback (P := @Surjective) n₁.cart.1.flip hf
  have : Surjective n₂.cm.F := MorphismProperty.of_isPullback (P := @Surjective) n₂.cart.1.flip hf
  have hψ : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := hψ
  have hmon : IsMonHom ψ := isMonHom n₁.cart n₂.cart ψ ψ' hψ
  have sec : ∀ {a : 𝟙_ (Over S) ⟶ o₁.t.G} {b : 𝟙_ (Over S) ⟶ o₂.t.G} {a' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {b' : 𝟙_ (Over S') ⟶ o₂'.t.G}, a'.left ≫ n₁.cm.F = f ≫ a.left → b'.left ≫ n₂.cm.F = f ≫ b.left →
      a' ≫ ψ' = b' → a ≫ ψ = b := fun {a b a' b'} ha hb h =>
    over_ext (T := 𝟙_ (Over S)) f (by
      rw [← hb, ← h, Over.comp_left, Over.comp_left, Category.assoc, hψ, ← Category.assoc, ← Category.assoc, ha])
  refine ⟨⟨⟨hmon, hfin, het, ?_, fun a => over_ext n₁.cm.F ?_, ?_⟩, fun p' hp a =>
    ⟨sec (n₁.eta _) (n₂.eta _) (hlev p' hp a).1, sec (n₁.etaA _) (n₂.etaA _) (hlev p' hp a).2⟩⟩, fun K hK =>
    kerSet n₁.cart.1 n₂.cart.1 (n₂.cm.e_comm.trans (by rw [n₂.base]; rfl)) ψ ψ' hψ K hK⟩
  · have : Surjective (n₁.cm.F ≫ ψ.left) := by rw [← hψ]; infer_instance
    exact Surjective.of_comp n₁.cm.F _
  · have e := congrArg (fun q => q.left) (hact a)
    simp only [Over.comp_left] at e ⊢
    rw [← Category.assoc, ← n₁.act, Category.assoc, ← hψ, ← Category.assoc, e, Category.assoc, n₂.act,
      ← Category.assoc, hψ, Category.assoc]
  · have hP : (lbPow o₁.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁.t.PP.isLB _ _
    have hP' : (lbPow o₁'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁'.t.PP.isLB _ _
    have hQ := pull_isLB o₂.t.PP.isLB ψ.left
    obtain ⟨c, hc⟩ := exists_gen_pow o₁.t.PP.L _ ((p ^ 2 : ℕ) : ℤ) o₁.t.PP.rig o₁.t.PP.rigGen
    obtain ⟨c₁, hc₁⟩ := gen_chartPull (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ))
      (eSec o₁.t.G) (fun _ => eSec o₁.t.G) fun _ => (Category.comp_id _).symm) c hc
    obtain ⟨c₂, hc₂⟩ := gen_chartPull (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) (fun _ => 1)
      (eSec o₁.t.G) (fun _ => eSec o₂.t.G) fun _ => (congrArg (fun q => q.left) hmon.one_hom).symm)
      o₂.t.PP.rig o₂.t.PP.rigGen
    refine lbIso_of_surjective o₁.t.G o₁.t.PP.L (GlobalTheory.ObjDim.isAbelianScheme o₁) o₁.t.PP.isLB o₁.ample n₁.cart.1 hP hQ
      ?_ c₁ hc₁ c₂ hc₂
    obtain ⟨w₁, hw₁, -⟩ := n₁.lin
    obtain ⟨w₂, hw₂, -⟩ := n₂.lin
    have i₁ : LBIso (lbPow o₁'.t.PP.L (p ^ 2)) ((lbPow o₁.t.PP.L (p ^ 2)).pull n₁.cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) _ n₁.cm.F _
        fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
        (iso_linComb ((isGen_iff w₁).1 hw₁) (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ)))
    have i₂ : LBIso (o₂'.t.PP.L.pull ψ'.left) ((o₂.t.PP.L.pull ψ.left).pull n₁.cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) _ n₁.cm.F _ fun _ => hψ)
        (iso_linComb ((isGen_iff w₂).1 hw₂) (K := PUnit) (fun _ => ψ'.left) (fun _ => 1))
    exact LBIso.trans (pull_isLB hP _) hP' (pull_isLB hQ _) i₁.symm
      (LBIso.trans hP' (pull_isLB o₂'.t.PP.isLB _) (pull_isLB hQ _) hL i₂)

end
