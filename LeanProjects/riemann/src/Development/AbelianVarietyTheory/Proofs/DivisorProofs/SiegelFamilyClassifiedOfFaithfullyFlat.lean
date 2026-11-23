import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFpqcDesc

open GlobalTheory.SiegPBDescent GlobalTheory.SiegelPullComp

variable {h n : ℕ} {B B' B₁ : Type} [CommRing B] [CommRing B'] [CommRing B₁] {ζ' : B'} {ζ₁ : B₁}
  {T T₁ : Scheme.{0}} {s₁ : T₁ ⟶ Sp B₁}

theorem siegPB_id_of_fpqc (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} (c : SiegPre h n ζ' sc)
    (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (p : T₁ ⟶ T) [Flat p] [QuasiCompact p] [Surjective p]
    (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SiegPB c₁ c p) (k : SiegPB c₁ u p) : SiegPB c u (𝟙 T) := by
  obtain ⟨φ₁, hm⟩ := exists_of_siegPB m
  obtain ⟨ψ₁, hk⟩ := exists_of_siegPB k
  obtain ⟨φ₁₂, hφ, sq₁, iso₁, lev₁⟩ := (sRelBy_one_iff _ _ _ _).1 hm
  obtain ⟨ψ₁₂, hψ, sq₂, iso₂, lev₂⟩ := (sRelBy_one_iff _ _ _ _).1 hk
  have : Epi p := Flat.epi_of_flat_of_surjective p
  have : Flat φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Surjective φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : QuasiCompact φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Flat ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : Surjective ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : QuasiCompact ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : EffectiveEpi φ₁ := inferInstance
  have : EffectiveEpi ψ₁ := inferInstance
  let φ := EffectiveEpi.desc φ₁ ψ₁ (comp_eq_of_comp_eq b hn ho hu hm hk)
  have hφψ : φ₁ ≫ φ = ψ₁ := EffectiveEpi.fac _ _ _
  have w : φ ≫ u.A.hom = c.A.hom := by
    rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψ.1.w, hφ.1.w]
  have : Mono φ := mono_of_fac hφ.1 hψ.1 hφψ w
  let ψ := EffectiveEpi.desc ψ₁ φ₁ (fun g₁ g₂ e => by
    rw [← cancel_mono φ, Category.assoc, Category.assoc, hφψ]; exact e)
  have hψφ : ψ₁ ≫ ψ = φ₁ := EffectiveEpi.fac _ _ _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψφ, Category.comp_id],
    by rw [← cancel_epi ψ₁, ← Category.assoc, hψφ, hφψ, Category.comp_id]⟩
  have gp : IsGrpPullback c.A u.A (𝟙 T) φ :=
    GlobalTheory.ObjDescent.isGrpPullback_id hφ hψ φ hφψ (w.trans (Category.comp_id _).symm)
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 T ≫ (u.lev a).left := fun a => by
    rw [Category.id_comp, ← cancel_epi p, ← Category.assoc, ← lev₁ a, Category.assoc, hφψ, lev₂ a]
  have he : eSec (G2 c.A) ≫ φ₂ = eSec (G2 u.A) := by
    have e₀ : eSec c.A ≫ φ = 𝟙 _ ≫ eSec u.A := (cubeMapOf gp).e_comm
    rw [Category.id_comp] at e₀
    apply pullback.hom_ext
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (fst u.A u.A).left = eSec (G2 u.A) ≫ (fst u.A u.A).left
      rw [Category.assoc, sq.1, ← Category.assoc, eSec_fst, eSec_fst, e₀]
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (snd u.A u.A).left = eSec (G2 u.A) ≫ (snd u.A u.A).left
      rw [Category.assoc, sq.2, ← Category.assoc, eSec_snd, eSec_snd, e₀]
  have hiso : LBIso c.P (u.P.pull φ₂) := by
    have h₁ := c.isLB
    have h₂ := pull_isLB u.isLB φ₂
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ₂ (CechPic.cls _ u.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have hsq := GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 sq₁
    have e₂ : φ₁₂ ≫ φ₂ = ψ₁₂ := GlobalTheory.SiegDesc.isSquare_comp hφψ sq₁ sq sq₂
    have cl₁ : CechPic.cls c₁.P c₁.isLB = CechPic.pull φ₁₂ (CechPic.cls c.P c.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB c.isLB _)).2 iso₁
    have cl₂ : CechPic.cls c₁.P c₁.isLB = CechPic.pull ψ₁₂ (CechPic.cls u.P u.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB u.isLB _)).2 iso₂
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns T T₁ p (G2 c.A) _
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) hN inferInstance inferInstance inferInstance
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, he, cls_eSec u, cls_eSec c, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← hsq.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp, e₂,
        ← cl₂, ← cl₁, sub_self, map_zero]
  exact siegPB_of ((sRelBy_one_iff _ _ _ _).2 ⟨φ₂, gp, sq, hiso, lev⟩)

theorem siegPB_of_fpqc_cover (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁)
    (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y) (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal)
    [Flat p] [QuasiCompact p] [Surjective p] (m : SiegPB c₁ c p) (k : SiegPB c₁ u (p ≫ f)) : SiegPB c u f := by
  obtain ⟨⟨u', hu'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h n B (b.ζ : B) Y S sY (f ≫ sY) f u rfl
  have k' : SiegPB c₁ u' p := pb_cancel hu' k
  have e := pb_comp hu' (siegPB_id_of_fpqc b c u' c₁ p hn ho (hpr u' hu' hu) m k')
  rwa [Category.id_comp] at e

theorem classified_of_faithfullyFlat : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R R').comp β)), SiegPB c' c (spMap (algebraMap R R')) → ∃ f : Sp R' ⟶ F.X, f ≫ F.s = spMap ((algebraMap R R').comp β) ∧ SiegPB c' F.univ f) → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F R R' _ _ _ _ β c _ H
  have hn0 : n ≠ 0 := by omega
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have : Flat π := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective π := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : QuasiCompact π := inferInstance
  have hcomp : π ≫ spMap β = spMap ((algebraMap R R').comp β) := by
    simp only [π, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R) (Sp R') (spMap β)
    (spMap ((algebraMap R R').comp β)) π c hcomp
  obtain ⟨f', hf's, hf'⟩ := H c' hc'
  have hagree : pullback.fst π π ≫ f' = pullback.snd π π ≫ f' := by
    obtain ⟨⟨c₁, hc₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R') (pullback π π)
      (spMap ((algebraMap R R').comp β)) (pullback.fst π π ≫ spMap ((algebraMap R R').comp β))
      (pullback.fst π π) c' rfl
    have a₁ : SiegPB c₁ F.univ (pullback.fst π π ≫ f') := pb_comp hf' hc₁
    have b₁ : SiegPB c₁ c (pullback.fst π π ≫ π) := pb_comp hc' hc₁
    rw [pullback.condition] at b₁
    have b₂ : SiegPB c₁ c' (pullback.snd π π) := pb_cancel hc' b₁
    have a₂ : SiegPB c₁ F.univ (pullback.snd π π ≫ f') := pb_comp hf' b₂
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn ho F _ _ c₁ _ _ (by rw [Category.assoc, hf's]) ?_ a₁ a₂
    rw [Category.assoc, hf's, ← hcomp, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : IsRegularEpi π := isRegularEpi_of_flat_of_surjective_of_isAffine π
  let f := EffectiveEpi.desc π f' (fun g₁ g₂ e => by
    have := congrArg (pullback.lift g₁ g₂ e ≫ ·) hagree
    rwa [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] at this)
  have hf : π ≫ f = f' := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨f, ?_, ?_⟩
  · rw [← cancel_epi π, ← Category.assoc, hf, hf's, hcomp]
  · exact siegPB_of_fpqc_cover g n (cycAway n) (cycBase hn0) (Sp R) (Sp R') F.X (spMap β) _ F.s c c' F.univ π f
      hn ho F.princ hc' (by rw [hf]; exact hf')

end GlobalTheory.SiegFpqcDesc
