import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackLocalOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SurjectiveAppOfPullbackSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftShearMapSquareZeroAbelianSchemes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem comp_eq_of_pair : ∀ (h n : ℕ) (B B' B₁ B₂ : Type) [CommRing B] [CommRing B'] [CommRing B₁] [CommRing B₂] (b : TBase B n) (ζ' : B') (ζ₁ : B₁) (ζ₂ : B₂) (T T₁ T₂ : Scheme.{0}) (sc : T ⟶ Sp B') (su : T ⟶ Sp B) (s₁ : T₁ ⟶ Sp B₁) (s₂ : T₂ ⟶ Sp B₂) (c : SiegPre h n ζ' sc) (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (c₂ : SiegPre h n ζ₂ s₂) (p₁ : T₁ ⟶ T) (p₂ : T₂ ⟶ T) (φ₁ : c₁.A.left ⟶ c.A.left) (ψ₁ : c₁.A.left ⟶ u.A.left) (φ₂ : c₂.A.left ⟶ c.A.left) (ψ₂ : c₂.A.left ⟶ u.A.left), 3 ≤ n → Odd n → u.Principal → SRelBy c₁ c 1 1 p₁ φ₁ → SRelBy c₁ u 1 1 p₁ ψ₁ → SRelBy c₂ c 1 1 p₂ φ₂ → SRelBy c₂ u 1 1 p₂ ψ₂ → ∀ (Z : Scheme.{0}) (g₁ : Z ⟶ c₁.A.left) (g₂ : Z ⟶ c₂.A.left), g₁ ≫ φ₁ = g₂ ≫ φ₂ → g₁ ≫ ψ₁ = g₂ ≫ ψ₂ := by
  intro h n B B' B₁ B₂ _ _ _ _ b ζ' ζ₁ ζ₂ T T₁ T₂ sc su s₁ s₂ c u c₁ c₂ p₁ p₂ φ₁ ψ₁ φ₂ ψ₂ hn ho hu m₁ k₁ m₂ k₂ Z g₁ g₂ e
  obtain ⟨-, hφ₁, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₁
  obtain ⟨-, hφ₂, -⟩ := (sRelBy_one_iff _ _ _ _).1 m₂
  have hz : (g₁ ≫ c₁.A.hom) ≫ p₁ = (g₂ ≫ c₂.A.hom) ≫ p₂ := by
    rw [Category.assoc, Category.assoc, ← hφ₁.1.w, ← hφ₂.1.w, reassoc_of% e]
  obtain ⟨⟨o, ho'⟩, -⟩ := GlobalTheory.siegPre_pullback h n B₁ ζ₁ T₁ Z s₁ ((g₁ ≫ c₁.A.hom) ≫ s₁) (g₁ ≫ c₁.A.hom) c₁ rfl
  obtain ⟨κ, hκ⟩ := exists_of_siegPB ho'
  have a₁ := comp_by m₁ hκ
  rw [hz] at a₁
  obtain ⟨κ', hκ', hκ'b⟩ := cancel_by m₂ a₁
  have n₁ := comp_by k₁ hκ
  have n₂ := comp_by k₂ hκ'b
  rw [← hz] at n₂
  have r := GlobalTheory.SiegRigid.eq_of_sRelBy h n n 1 B B₁ b ζ₁ T Z su _ u o _ _ _ hn ho hu n₁ n₂
  obtain ⟨-, hκg, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ
  obtain ⟨-, hκ'g, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ'b
  have hl : g₁ ≫ c₁.A.hom = 𝟙 Z ≫ g₁ ≫ c₁.A.hom := (Category.id_comp _).symm
  have h₁ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ = g₁ := hκg.1.lift_fst _ _ _
  have h₀ : hκg.1.lift g₁ (𝟙 Z) hl ≫ o.A.hom = 𝟙 Z := hκg.1.lift_snd _ _ _
  have h₂ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' = g₂ := by
    apply hφ₂.1.hom_ext
    · rw [Category.assoc, hκ', ← Category.assoc, h₁, e]
    · rw [Category.assoc, hκ'g.1.w, ← Category.assoc, h₀, Category.id_comp]
  calc g₁ ≫ ψ₁ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ ≫ ψ₁ := by rw [← Category.assoc, h₁]
    _ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' ≫ ψ₂ := by rw [r]
    _ = g₂ ≫ ψ₂ := by rw [← Category.assoc, h₂]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem isPullback_of_sRelBy {h n : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S}
    {φ : c'.A.left ⟶ c.A.left} (m : SRelBy c' c 1 1 f φ) : IsPullback φ c'.A.hom c.A.hom f :=
  ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1.1

theorem iso_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (b : TBase B n) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n (b.ζ : B) su), 3 ≤ n → Odd n → u.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV u j) → ∃ φ : c.A.left ⟶ u.A.left, IsIso φ ∧ φ ≫ u.A.hom = c.A.hom ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ) := by
  intro g n B B' _ _ b ζ' S sc su c u hn ho hu hloc
  choose V j cV hj hx m k using hloc
  choose φV hm using fun x => exists_of_siegPB (m x)
  choose ψV hk using fun x => exists_of_siegPB (k x)
  have pφ : ∀ x, IsPullback (φV x) (cV x).A.hom c.A.hom (j x) := fun x => isPullback_of_sRelBy (hm x)
  have pψ : ∀ x, IsPullback (ψV x) (cV x).A.hom u.A.hom (j x) := fun x => isPullback_of_sRelBy (hk x)
  have oφ : ∀ x, IsOpenImmersion (φV x) := fun x => MorphismProperty.of_isPullback (pφ x).flip (hj x)
  have oψ : ∀ x, IsOpenImmersion (ψV x) := fun x => MorphismProperty.of_isPullback (pψ x).flip (hj x)
  let 𝒰 : c.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) φV
    (fun a => ⟨c.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pφ (c.A.hom a)) a).2 (hx _)⟩) oφ
  let 𝒰' : u.A.left.OpenCover := Scheme.Cover.mkOfCovers S (fun x => (cV x).A.left) ψV
    (fun a => ⟨u.A.hom a, (GlobalTheory.GrpLoc.range_of_isPullback (pψ (u.A.hom a)) a).2 (hx _)⟩) oψ
  have pair := fun x y => comp_eq_of_pair g n B B' B' B' b ζ' ζ' ζ' S (V x) (V y) sc su (j x ≫ sc) (j y ≫ sc) c u
    (cV x) (cV y) (j x) (j y) (φV x) (ψV x) (φV y) (ψV y) hn ho hu (hm x) (hk x) (hm y) (hk y)
  have compat : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ ψV x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ ψV y :=
    fun x y => pair x y _ _ _ pullback.condition
  let φ := 𝒰.glueMorphisms ψV compat
  have hφ : ∀ x, φV x ≫ φ = ψV x := fun x => 𝒰.ι_glueMorphisms ψV compat x
  have hw : φ ≫ u.A.hom = c.A.hom := by
    refine 𝒰.hom_ext _ _ fun x => ?_
    show φV x ≫ φ ≫ u.A.hom = φV x ≫ c.A.hom
    rw [reassoc_of% (hφ x), (pψ x).w, (pφ x).w]
  have key : ∀ x y (Z : Scheme.{0}) (g₁ : Z ⟶ (cV x).A.left) (g₂ : Z ⟶ (cV y).A.left),
      g₁ ≫ ψV x = g₂ ≫ ψV y → g₁ ≫ φV x = g₂ ≫ φV y := by
    intro x y Z g₁ g₂ e
    have e₁ : (g₁ ≫ φV x) ≫ c.A.hom = (g₂ ≫ (cV y).A.hom) ≫ j y := by
      calc (g₁ ≫ φV x) ≫ c.A.hom = g₁ ≫ φV x ≫ φ ≫ u.A.hom := by rw [hw, Category.assoc]
        _ = g₁ ≫ ψV x ≫ u.A.hom := by rw [reassoc_of% (hφ x)]
        _ = g₂ ≫ ψV y ≫ u.A.hom := by rw [reassoc_of% e]
        _ = _ := by rw [(pψ y).w, Category.assoc]
    let t := (pφ y).lift (g₁ ≫ φV x) (g₂ ≫ (cV y).A.hom) e₁
    have t₁ : t ≫ φV y = g₁ ≫ φV x := (pφ y).lift_fst _ _ _
    have t₂ : t ≫ (cV y).A.hom = g₂ ≫ (cV y).A.hom := (pφ y).lift_snd _ _ _
    have t₃ : t ≫ ψV y = g₁ ≫ ψV x := pair y x _ t g₁ t₁
    have tg : t = g₂ := (pψ y).hom_ext (t₃.trans e) t₂
    rw [← t₁, tg]
  have compat' : ∀ x y, pullback.fst (𝒰'.f x) (𝒰'.f y) ≫ φV x = pullback.snd (𝒰'.f x) (𝒰'.f y) ≫ φV y :=
    fun x y => key x y _ _ _ pullback.condition
  let ψ := 𝒰'.glueMorphisms φV compat'
  have hψ : ∀ x, ψV x ≫ ψ = φV x := fun x => 𝒰'.ι_glueMorphisms φV compat' x
  have i₁ : φ ≫ ψ = 𝟙 _ := 𝒰.hom_ext _ _ fun x => by
    show φV x ≫ φ ≫ ψ = φV x ≫ 𝟙 _
    rw [reassoc_of% (hφ x), hψ x, Category.comp_id]
  have i₂ : ψ ≫ φ = 𝟙 _ := 𝒰'.hom_ext _ _ fun x => by
    show ψV x ≫ ψ ≫ φ = ψV x ≫ 𝟙 _
    rw [reassoc_of% (hψ x), hφ x, Category.comp_id]
  exact ⟨φ, ⟨ψ, i₁, i₂⟩, hw, fun x => ⟨V x, j x, cV x, φV x, hj x, hx x, hm x, by rw [hφ x]; exact hk x⟩⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegPBDescent

theorem siegPB_id_of_local : ∀ (g n : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S : Scheme.{0}) (sc : S ⟶ Sp B') (su : S ⟶ Sp B) (c : SiegPre g n ζ' sc) (u : SiegPre g n ζ su) (φ : c.A.left ⟶ u.A.left), IsIso φ → φ ≫ u.A.hom = c.A.hom → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n ζ' (j ≫ sc)) (φV : cV.A.left ⟶ c.A.left), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SRelBy cV c 1 1 j φV ∧ SRelBy cV u 1 1 j (φV ≫ φ)) → SiegPB c u (𝟙 S) := by
  intro g n B B' _ _ ζ ζ' S sc su c u φ hi hw hloc
  have gp : IsGrpPullback c.A u.A (𝟙 S) φ := GlobalTheory.GrpLoc.isGrpPullback_local_on_base S c.A u.A φ hi hw fun p => by
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    exact ⟨V, j, cV.A, inferInstance, φV, hj, hx, ((sRelBy_one_iff _ _ _ _).1 m).choose_spec.1,
      ((sRelBy_one_iff _ _ _ _).1 k).choose_spec.1⟩
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 S ≫ (u.lev a).left := fun a => by
    refine GlobalTheory.GrpLoc.hom_ext_loc fun p => ?_
    obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
    obtain ⟨-, -, -, -, lm⟩ := (sRelBy_one_iff _ _ _ _).1 m
    obtain ⟨-, -, -, -, lk⟩ := (sRelBy_one_iff _ _ _ _).1 k
    refine ⟨V, j, hj, hx, ?_⟩
    rw [Category.id_comp, ← reassoc_of% (lm a), ← lk a]
  have gp₂ : IsGrpPullback (G2 c.A) (G2 u.A) (𝟙 S) φ₂ := GlobalTheory.ShearLift.isGrpPullback_tensor gp gp sq.1 sq.2
  have rL : Out.Rigidified (G2 c.A) c.P :=
    (CechPic.cls_eq_zero_iff (pull_isLB c.isLB _)).1 (by rw [CechPic.cls_pull c.isLB]; exact cls_eSec c)
  have rL' : Out.Rigidified (G2 u.A) u.P :=
    (CechPic.cls_eq_zero_iff (pull_isLB u.isLB _)).1 (by rw [CechPic.cls_pull u.isLB]; exact cls_eSec u)
  have hiso : LBIso c.P (u.P.pull φ₂) :=
    GlobalTheory.RigidLocal.lbIso_of_local GlobalTheory.abelianSchemeLaws_all.1.globalFns S (G2 c.A) (G2 u.A) c.P u.P φ₂
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) c.isLB u.isLB rL rL' gp₂ fun p => by
        obtain ⟨V, j, cV, φV, hj, hx, m, k⟩ := hloc p
        obtain ⟨φV₂, gm, sm, im, -⟩ := (sRelBy_one_iff _ _ _ _).1 m
        obtain ⟨ψV₂, -, sk, ik, -⟩ := (sRelBy_one_iff _ _ _ _).1 k
        have e₂ : φV₂ ≫ φ₂ = ψV₂ := GlobalTheory.SiegDesc.isSquare_comp rfl sm sq sk
        refine ⟨V, (G2 cV.A).left, j, (G2 cV.A).hom, φV₂, hj, hx, GlobalTheory.SiegDesc.isPullback_of_isSquare gm.1 sm, ?_⟩
        rw [e₂]
        exact im.symm.trans (pull_isLB c.isLB _) cV.isLB (pull_isLB u.isLB _) ik
  exact ⟨φ, φ₂, gp, sq, hiso, lev⟩

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem glue_classifying : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ ∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ SiegPB cV F.univ (j ≫ f) := by
  intro g n hg hn ho F S s' c hloc
  choose V j cV hj hx m f hfs hpb using hloc
  let 𝒰 : S.OpenCover := Scheme.Cover.mkOfCovers S V j (fun x => ⟨x, hx x⟩) hj
  have key : ∀ x y, pullback.fst (j x) (j y) ≫ f x = pullback.snd (j x) (j y) ≫ f y := by
    intro x y
    obtain ⟨⟨cP, hcP⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (pullback (j x) (j y)) s'
      (pullback.fst (j x) (j y) ≫ j x ≫ s') (pullback.fst (j x) (j y) ≫ j x) c (Category.assoc _ _ _)
    have hcP' : SiegPB cP c (pullback.snd (j x) (j y) ≫ j y) := by rw [← pullback.condition]; exact hcP
    have h₁ := pb_comp (hpb x) (pb_cancel (m x) hcP)
    have h₂ := pb_comp (hpb y) (pb_cancel (m y) hcP')
    refine GlobalTheory.SiegUniq.eq_of_siegPB g n hg hn ho F _ _ cP _ _ ?_ ?_ h₁ h₂
    · rw [Category.assoc, hfs x]
    · rw [Category.assoc, hfs y, pullback.condition_assoc]
  let φ := 𝒰.glueMorphisms f key
  have hφ : ∀ x, j x ≫ φ = f x := fun x => 𝒰.ι_glueMorphisms f key x
  refine ⟨φ, 𝒰.hom_ext _ _ fun x => ?_, fun x => ⟨V x, j x, cV x, hj x, hx x, m x, by rw [hφ x]; exact hpb x⟩⟩
  show j x ≫ φ ≫ F.s = j x ≫ s'
  rw [reassoc_of% (hφ x), hfs x]

end GlobalTheory.SiegZar

namespace GlobalTheory.SiegZar
open GlobalTheory.SiegelPullComp

theorem classified_of_local : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal → (∀ x : S, ∃ (V : Scheme.{0}) (j : V ⟶ S) (cV : SiegPre g n (zetaAway n) (j ≫ s')), IsOpenImmersion j ∧ x ∈ Set.range j ∧ SiegPB cV c j ∧ ∃ f : V ⟶ F.X, f ≫ F.s = j ≫ s' ∧ SiegPB cV F.univ f) → ∃ f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F S s' c _ hloc
  obtain ⟨f, hf, hl⟩ := glue_classifying g n hg hn ho F S s' c hloc
  have hn0 : n ≠ 0 := by omega
  obtain ⟨⟨u, hu⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) F.X S F.s (f ≫ F.s) f F.univ rfl
  have hup : u.Principal := hpr u hu F.princ
  obtain ⟨φ, hi, hw, hφ⟩ := iso_of_local g n (cycAway n) (cycAway n) (cycBase hn0) (zetaAway n) S s' (f ≫ F.s) c u
    hn ho hup fun x => by
      obtain ⟨V, j, cV, hj, hx, h₁, h₂⟩ := hl x
      exact ⟨V, j, cV, hj, hx, h₁, pb_cancel hu h₂⟩
  have e := pb_comp hu (siegPB_id_of_local g n (cycAway n) (cycAway n) _ (zetaAway n) S s' (f ≫ F.s) c u φ hi hw hφ)
  rw [Category.id_comp] at e
  exact ⟨f, hf, e⟩

end GlobalTheory.SiegZar
