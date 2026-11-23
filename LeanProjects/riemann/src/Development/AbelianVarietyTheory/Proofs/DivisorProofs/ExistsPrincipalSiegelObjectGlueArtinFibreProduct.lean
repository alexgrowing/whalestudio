import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfGaloisDescendedData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandGlueFlatArtinianFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOverArtinFibreProductIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlueArtinianLocalFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleGlueMilnorPatchingArtinLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqZeroOfPullbacksEqZeroArtinFibreProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreProductSpecFieldPointFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPrincipalArtinianOfPrincipalPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinGlue
open GlobalTheory.SiegelDescent GlobalTheory.SiegDesc GlobalTheory.CechPic

theorem lem_ab : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A₁ : Over (Spec R₁)) [GrpObj A₁] (A₂ : Over (Spec R₂)) [GrpObj A₂] (A₀ : Over (Spec R₀)) [GrpObj A₀] (ψ₁ : A₀.left ⟶ A₁.left) (ψ₂ : A₀.left ⟶ A₂.left), IsAbelianScheme A₁ → IsAbelianScheme A₂ → IsGrpPullback A₀ A₁ (Spec.map g₁) ψ₁ → IsGrpPullback A₀ A₂ (Spec.map g₂) ψ₂ → ∃ (A : Over (Spec P)) (_ : GrpObj A) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A ∧ IsGrpPullback A₁ A (Spec.map f₁) φ₁ ∧ IsGrpPullback A₂ A (Spec.map f₂) φ₂ ∧ ψ₁ ≫ φ₁ = ψ₂ ≫ φ₂ := GlobalTheory.T.abelianScheme_glue_artinian_local_fibreProduct

theorem lem_lb : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (X : Over (Spec P)) (X₁ : Over (Spec R₁)) (X₂ : Over (Spec R₂)) (X₀ : Over (Spec R₀)) (j₁ : X₁.left ⟶ X.left) (j₂ : X₂.left ⟶ X.left) (i₁ : X₀.left ⟶ X₁.left) (i₂ : X₀.left ⟶ X₂.left), Flat X.hom → IsPullback j₁ X₁.hom X.hom (Spec.map f₁) → IsPullback j₂ X₂.hom X.hom (Spec.map f₂) → IsPullback i₁ X₀.hom X₁.hom (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → i₂ ≫ X₂.hom = X₀.hom ≫ Spec.map g₂ → ∀ (L₁ : LB X₁.left) (L₂ : LB X₂.left), L₁.IsLB → L₂.IsLB → LBIso (L₁.pull i₁) (L₂.pull i₂) → ∃ L : LB X.left, L.IsLB ∧ LBIso L₁ (L.pull j₁) ∧ LBIso L₂ (L.pull j₂) := GlobalTheory.T.exists_lineBundle_glue_milnorPatching_artinLocal

theorem lem_triv : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (A : Over (Spec P)) [GrpObj A] (A₁ : Over (Spec R₁)) (A₂ : Over (Spec R₂)) (φ₁ : A₁.left ⟶ A.left) (φ₂ : A₂.left ⟶ A.left), IsAbelianScheme A → IsPullback φ₁ A₁.hom A.hom (Spec.map f₁) → IsPullback φ₂ A₂.hom A.hom (Spec.map f₂) → ∀ c : GlobalTheory.CechPic.Pic A.left, GlobalTheory.CechPic.pull φ₁ c = 0 → GlobalTheory.CechPic.pull φ₂ c = 0 → c = 0 := GlobalTheory.T.pic_eq_zero_of_pullbacks_eq_zero_artinFibreProduct

theorem lem_pt : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec P), (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₁, y ≫ Spec.map f₁ = x) ∨ (∃ y : Spec (CommRingCat.of k) ⟶ Spec R₂, y ≫ Spec.map f₂ = x) := GlobalTheory.T.fibreProduct_spec_fieldPoint_factors

theorem lem_princ : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := GlobalTheory.T.siegel_principal_artinian_of_principal_pullback

theorem geom_transfer {S S' : Scheme.{0}} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B} {h M : ℕ}
    (c : SiegPre h M ζ s') (A₀ : Over S) [GrpObj A₀] [IsCommMonObj A₀] (f : S' ⟶ S) (φ : c.A.left ⟶ A₀.left)
    (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A₀)) (hs : s' = f ≫ s)
    (hp : IsGrpPullback c.A A₀ f φ) (hP₀ : P₀.IsLB)
    (diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ))
    (hlev : ∀ a, (c.lev a).left ≫ φ = f ≫ (lev₀ a).left) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (y : Sp k ⟶ S') (hy : y ≫ f = x) (β : B →+* k) (z : kˣ) (hx : x ≫ s = spMap β)
    (hz : (z : k) = β ζ) :
    (∀ a, (toUnit (Over.mk x) ≫ lev₀ a = 1 ↔ ∃ b, a = M • b)) ∧
    (∀ g : Over.mk x ⟶ A₀, g ^ M = 1 → ∃ a, toUnit _ ≫ lev₀ a = g) ∧
    ∀ a b, Out.WeilIs A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) M (toUnit (Over.mk x) ≫ lev₀ a) (toUnit _ ≫ lev₀ b)
      (unitOn (z ^ (2 * omegaStd a b))) := by
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ f := hp.1.w
  obtain ⟨g₁, g₂, g₃⟩ := c.geom k y β z (by rw [hs, ← Category.assoc, hy, hx]) hz
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk y) (Over.mk x) (𝟙 _) ((Category.id_comp _).trans hy.symm)
  have σinj : Function.Injective σ := fun u v e => Over.OverMorphism.ext (by
    simpa using ((hσ u _).1 rfl).symm.trans ((hσ v _).1 e.symm))
  have pt : ∀ a, (toUnit (Over.mk y) ≫ c.lev a).left ≫ φ = (toUnit (Over.mk x) ≫ lev₀ a).left := fun a => by
    change (y ≫ (c.lev a).left) ≫ φ = x ≫ (lev₀ a).left
    rw [Category.assoc, hlev, ← Category.assoc, hy]
  have σlev : ∀ a, σ (toUnit _ ≫ lev₀ a) = toUnit _ ≫ c.lev a := fun a =>
    (hσ _ _).2 ((pt a).trans (Category.id_comp _).symm)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    have H := (GlobalTheory.weilIs_grpPullback_of_comm _ _ A₀ c.A f φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    exact weilIs_congr hy _ _ _ _ _ _ (pt a) (pt b) _ H

theorem spec_isPushout (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀)
    (hP : IsPullback f₁ f₂ g₁ g₂) (hl : IsLocalRing P) (ha : IsArtinianRing P) (s₁ : Function.Surjective g₁)
    (s₂ : Function.Surjective g₂) : IsPushout (Spec.map g₁) (Spec.map g₂) (Spec.map f₁) (Spec.map f₂) := by
  have w : Spec.map g₁ ≫ Spec.map f₁ = Spec.map g₂ ≫ Spec.map f₂ := by
    rw [← Spec.map_comp, ← Spec.map_comp, hP.w]
  exact GlobalTheory.T.flat_over_artinFibreProduct_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hl ha s₁ s₂ (Over.mk (𝟙 _)) (Over.mk (𝟙 _)) (Over.mk (𝟙 _))
    (Over.mk (𝟙 _)) (Spec.map f₁) (Spec.map f₂) (Spec.map g₁) (Spec.map g₂) (show Flat (𝟙 (Spec P)) from inferInstance) (IsPullback.id_vert _)
    (IsPullback.id_vert _) (IsPullback.id_vert _) w (by simp)

theorem nontrivial_of_pt (R : CommRingCat.{0}) (k : Type) [Field k] (y : Spec (CommRingCat.of k) ⟶ Spec R) :
    Nontrivial R := by
  obtain ⟨pt⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y.base pt⟩

theorem exists_principal_glue : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)) (c₂ : SiegPre g n (zetaAway n) (Spec.map f₂ ≫ Spec.map β)), c₁.Principal → c₂.Principal → (∃ c₀ : SiegPre g n (zetaAway n) (Spec.map g₁ ≫ Spec.map f₁ ≫ Spec.map β), SiegPB c₀ c₁ (Spec.map g₁) ∧ SiegPB c₀ c₂ (Spec.map g₂)) → ∃ c : SiegPre g n (zetaAway n) (Spec.map β), c.Principal ∧ SiegPB c₁ c (Spec.map f₁) ∧ SiegPB c₂ c (Spec.map f₂) := by
  intro g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ β c₁ c₂ hp₁ hp₂ hc₀
  obtain ⟨c₀, ⟨ψ₁, ψ₁₂, hψ₁, sψ₁, iψ₁, lψ₁⟩, ⟨ψ₂, ψ₂₂, hψ₂, sψ₂, iψ₂, lψ₂⟩⟩ := hc₀
  obtain ⟨A, instA, φ₁, φ₂, hA, hφ₁, hφ₂, hcomm⟩ :=
    lem_ab P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ c₁.A c₂.A c₀.A ψ₁ ψ₂ c₁.ab c₂.ab hψ₁ hψ₂
  haveI := hA.comm
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨φ₁₂, sφ₁⟩ := exists_isSquare hφ₁.1.w
  obtain ⟨φ₂₂, sφ₂⟩ := exists_isSquare hφ₂.1.w
  obtain ⟨χ₂, sχ⟩ := exists_isSquare (f := Spec.map g₁ ≫ Spec.map f₁) (φ := ψ₁ ≫ φ₁)
    (by rw [Category.assoc, hφ₁.1.w]; exact (reassoc_of% hψ₁.1.w) _)
  have e₁₂ : ψ₁₂ ≫ φ₁₂ = χ₂ := isSquare_comp rfl sψ₁ sφ₁ sχ
  have e₂₂ : ψ₂₂ ≫ φ₂₂ = χ₂ := isSquare_comp hcomm.symm sψ₂ sφ₂ sχ
  have flat : Flat (G2 A).hom := by
    haveI := hAA.smooth
    infer_instance
  have hiso₀ : LBIso (c₁.P.pull ψ₁₂) (c₂.P.pull ψ₂₂) :=
    LBIso.trans (pull_isLB c₁.isLB _) c₀.isLB (pull_isLB c₂.isLB _) iψ₁.symm iψ₂
  obtain ⟨L, hL, w₁, w₂⟩ := lem_lb P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ (G2 A) (G2 c₁.A) (G2 c₂.A)
    (G2 c₀.A) φ₁₂ φ₂₂ ψ₁₂ ψ₂₂ flat (isPullback_of_isSquare hφ₁.1 sφ₁) (isPullback_of_isSquare hφ₂.1 sφ₂)
    (isPullback_of_isSquare hψ₁.1 sψ₁) (e₁₂.trans e₂₂.symm) (isSquare_w hψ₂.1.w sψ₂) c₁.P c₂.P c₁.isLB c₂.isLB
    hiso₀
  have clsP₁ : cls c₁.P c₁.isLB = pull φ₁₂ (cls L hL) := by
    rw [← cls_pull hL φ₁₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₁
  have clsP₂ : cls c₂.P c₂.isLB = pull φ₂₂ (cls L hL) := by
    rw [← cls_pull hL φ₂₂ (pull_isLB hL _)]
    exact (cls_eq_iff _ _).2 w₂
  have rig : ∀ (a₁ : c₁.A ⟶ c₁.A ⊗ c₁.A) (a₂ : c₂.A ⟶ c₂.A ⊗ c₂.A) (a : A ⟶ A ⊗ A),
      a₁.left ≫ φ₁₂ = φ₁ ≫ a.left → a₂.left ≫ φ₂₂ = φ₂ ≫ a.left →
      (∃ t : (c₁.P.pull a₁.left).Gen, t.IsGen) → (∃ t : (c₂.P.pull a₂.left).Gen, t.IsGen) →
      ∃ t : (L.pull a.left).Gen, t.IsGen := by
    intro a₁ a₂ a e₁ e₂ t₁ t₂
    refine (cls_eq_zero_iff (pull_isLB hL _)).1 ?_
    rw [cls_pull hL _ (pull_isLB hL _)]
    refine lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ A c₁.A c₂.A φ₁ φ₂ hA hφ₁.1 hφ₂.1 _ ?_ ?_
    · rw [← pull_comp, ← e₁, pull_comp, ← clsP₁, ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _)]
      exact (cls_eq_zero_iff _).2 t₁
    · rw [← pull_comp, ← e₂, pull_comp, ← clsP₂, ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _)]
      exact (cls_eq_zero_iff _).2 t₂
  have one₁ := one_comp hφ₁ c₁.A A φ₁ hφ₁.1.w
  have one₂ := one_comp hφ₂ c₂.A A φ₂ hφ₂.1.w
  have idφ₁ : (𝟙 c₁.A : c₁.A ⟶ c₁.A).left ≫ φ₁ = φ₁ ≫ (𝟙 A : A ⟶ A).left := by simp
  have idφ₂ : (𝟙 c₂.A : c₂.A ⟶ c₂.A).left ≫ φ₂ = φ₂ ≫ (𝟙 A : A ⟶ A).left := by simp
  have symm : LBIso L (L.pull (lift (snd A A) (fst A A)).left) := by
    have sw₁ := lift_square sφ₁ sφ₁.2.symm sφ₁.1.symm
    have sw₂ := lift_square sφ₂ sφ₂.2.symm sφ₂.1.symm
    refine (cls_eq_iff hL (pull_isLB hL _)).1 (sub_eq_zero.1 (lem_triv P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
      (G2 A) (G2 c₁.A) (G2 c₂.A) φ₁₂ φ₂₂ hAA (isPullback_of_isSquare hφ₁.1 sφ₁)
      (isPullback_of_isSquare hφ₂.1 sφ₂) _ ?_ ?_))
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₁, pull_comp, ← clsP₁,
        ← cls_pull c₁.isLB _ (pull_isLB c₁.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₁.symm
    · rw [map_sub, cls_pull hL _ (pull_isLB hL _), ← pull_comp, ← sw₂, pull_comp, ← clsP₂,
        ← cls_pull c₂.isLB _ (pull_isLB c₂.isLB _), sub_eq_zero]
      exact (cls_eq_iff _ _).2 c₂.symm

  have hpo := spec_isPushout P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂
  have levc : ∀ a, Spec.map g₁ ≫ (c₁.lev a).left ≫ φ₁ = Spec.map g₂ ≫ (c₂.lev a).left ≫ φ₂ := fun a => by
    simp only [← Category.assoc]
    rw [← lψ₁ a, ← lψ₂ a, Category.assoc, Category.assoc, hcomm]
  have sec : ∀ {X : Scheme.{0}} {Bv : Over X} (u : 𝟙_ (Over X) ⟶ Bv), u.left ≫ Bv.hom = 𝟙 X := fun u => by
    simpa using Over.w u
  have hlev : ∀ a, ∃ l : 𝟙_ (Over (Spec P)) ⟶ A, Spec.map f₁ ≫ l.left = (c₁.lev a).left ≫ φ₁ ∧
      Spec.map f₂ ≫ l.left = (c₂.lev a).left ≫ φ₂ := fun a =>
    ⟨Over.homMk (hpo.desc _ _ (levc a)) (by
      refine hpo.hom_ext ?_ ?_
      · rw [← Category.assoc, hpo.inl_desc, Category.assoc, hφ₁.1.w, ← Category.assoc, sec]
        simp
      · rw [← Category.assoc, hpo.inr_desc, Category.assoc, hφ₂.1.w, ← Category.assoc, sec]
        simp), hpo.inl_desc _ _ _, hpo.inr_desc _ _ _⟩
  choose lev hl₁ hl₂ using hlev
  obtain ⟨ρ₁, hρ₁⟩ := exists_liftHom hφ₁ (𝟙_ _) (𝟙_ _) (Spec.map f₁)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨ρ₂, hρ₂⟩ := exists_liftHom hφ₂ (𝟙_ _) (𝟙_ _) (Spec.map f₂)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ρl₁ : ∀ a, ρ₁ (lev a) = c₁.lev a := fun a => (hρ₁ _ _).2 (hl₁ a).symm
  have ρl₂ : ∀ a, ρ₂ (lev a) = c₂.lev a := fun a => (hρ₂ _ _).2 (hl₂ a).symm
  have inj : ∀ x y : 𝟙_ (Over (Spec P)) ⟶ A, ρ₁ x = ρ₁ y → ρ₂ x = ρ₂ y → x = y := fun x y e₁ e₂ =>
    Over.OverMorphism.ext (hpo.hom_ext
      (by rw [← (hρ₁ x _).1 rfl, ← (hρ₁ y _).1 rfl, e₁])
      (by rw [← (hρ₂ x _).1 rfl, ← (hρ₂ y _).1 rfl, e₂]))
  have diag₁ : LBIso (c₁.P.pull (lift (𝟙 c₁.A) (𝟙 c₁.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₁) :=
    lbIso_square c₁.isLB hL w₁ (lift_square sφ₁ idφ₁ idφ₁)
  have diag₂ : LBIso (c₂.P.pull (lift (𝟙 c₂.A) (𝟙 c₂.A)).left) ((L.pull (lift (𝟙 A) (𝟙 A)).left).pull φ₂) :=
    lbIso_square c₂.isLB hL w₂ (lift_square sφ₂ idφ₂ idφ₂)
  let c : SiegPre g n (zetaAway n) (Spec.map β) :=
    { A := A, ab := hA, P := L, isLB := hL
      rig₁ := rig _ _ _ (lift_square sφ₁ one₁ idφ₁) (lift_square sφ₂ one₂ idφ₂) c₁.rig₁ c₂.rig₁
      rig₂ := rig _ _ _ (lift_square sφ₁ idφ₁ one₁) (lift_square sφ₂ idφ₂ one₂) c₁.rig₂ c₂.rig₂
      symm := symm, lev := lev
      lev_add := fun a b => inj _ _ (by rw [map_mul, ρl₁, ρl₁, ρl₁, c₁.lev_add])
        (by rw [map_mul, ρl₂, ρl₂, ρl₂, c₂.lev_add])
      lev_tors := fun a => inj _ _ (by rw [map_pow, ρl₁, c₁.lev_tors, map_one])
        (by rw [map_pow, ρl₂, c₂.lev_tors, map_one])
      geom := by
        intro k _ _ x β' z hx hz
        rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ k x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact geom_transfer c₁ A (Spec.map f₁) φ₁ L lev rfl hφ₁ hL diag₁ (fun a => (hl₁ a).symm) k x y hy β' z hx hz
        · exact geom_transfer c₂ A (Spec.map f₂) φ₂ L lev rfl hφ₂ hL diag₂ (fun a => (hl₂ a).symm) k x y hy β' z hx hz }
  have pb₁ : SiegPB c₁ c (Spec.map f₁) := ⟨φ₁, φ₁₂, hφ₁, sφ₁, w₁, fun a => (hl₁ a).symm⟩
  have pb₂ : SiegPB c₂ c (Spec.map f₂) := ⟨φ₂, φ₂₂, hφ₂, sφ₂, w₂, fun a => (hl₂ a).symm⟩
  refine ⟨c, ?_, pb₁, pb₂⟩
  rcases lem_pt P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hs₁ hs₂ (IsLocalRing.ResidueField P)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue P))) with ⟨y, -⟩ | ⟨y, -⟩
  · haveI := nontrivial_of_pt R₁ _ y
    exact lem_princ g n hn hodd P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ inferInstance β c c₁ pb₁ hp₁
  · haveI := nontrivial_of_pt R₂ _ y
    exact lem_princ g n hn hodd P R₂ R₁ R₀ f₂ f₁ g₂ g₁ hP.flip hloc hart hs₂ hs₁ inferInstance β c c₂ pb₂ hp₂

end GlobalTheory.ArtinGlue
