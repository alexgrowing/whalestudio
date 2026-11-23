import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigidStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyObjMapOfFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.SiegelPullComp
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegPBDescent

variable {h n : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}

theorem sRelBy_one_iff (c' : SiegPre h n ζ' s') (c : SiegPre h n ζ s) (f : S' ⟶ S) (φ : c'.A.left ⟶ c.A.left) :
    SRelBy c' c 1 1 f φ ↔ ∃ φ₂, IsGrpPullback c'.A c.A f φ ∧ IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂) ∧
      ∀ a, (c'.lev a).left ≫ φ = f ≫ (c.lev a).left := by
  simp only [SRelBy, pow_one]
  exact ⟨fun ⟨x, ⟨ψ, y, z⟩, w⟩ => ⟨ψ, x, y, z, w⟩, fun ⟨ψ, x, y, z, w⟩ => ⟨x, ⟨ψ, y, z⟩, w⟩⟩

theorem exists_of_siegPB {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S} (m : SiegPB c' c f) :
    ∃ φ, SRelBy c' c 1 1 f φ :=
  (sRel_one_one_iff c' c f).2 m

theorem siegPB_of {c' : SiegPre h n ζ' s'} {c : SiegPre h n ζ s} {f : S' ⟶ S} {φ} (m : SRelBy c' c 1 1 f φ) :
    SiegPB c' c f :=
  (sRel_one_one_iff c' c f).1 ⟨φ, m⟩

theorem comp_by {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {ψ : c''.A.left ⟶ c'.A.left} (m : SRelBy c' c 1 1 f φ)
    (m' : SRelBy c'' c' 1 1 f' ψ) : SRelBy c'' c 1 1 (f' ≫ f) (ψ ≫ φ) := by
  rw [sRelBy_one_iff] at m m' ⊢
  obtain ⟨φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨ψ₂, hψ, hs', hw', hl'⟩ := m'
  refine ⟨ψ₂ ≫ φ₂, hψ.comp hφ, ⟨?_, ?_⟩, ?_, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem cancel_by {c : SiegPre h n ζ s} {c' : SiegPre h n ζ' s'} {c'' : SiegPre h n ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} {φ : c'.A.left ⟶ c.A.left} {χ : c''.A.left ⟶ c.A.left} (m : SRelBy c' c 1 1 f φ)
    (n : SRelBy c'' c 1 1 (f' ≫ f) χ) : ∃ F, F ≫ φ = χ ∧ SRelBy c'' c' 1 1 f' F := by
  rw [sRelBy_one_iff] at m n
  obtain ⟨φ₂, hφ, hs, hw, hl⟩ := m
  obtain ⟨χ₂, hχ, hs', hw', hl'⟩ := n
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hF, (sRelBy_one_iff _ _ _ _).2 ⟨F₂, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨h₁, h₂⟩, ?_, fun a => ?_⟩⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a).left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a)
      have a₂ : (c'.lev a).left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem eSec_sq {X : Scheme.{0}} (A : Over X) [GrpObj A] :
    eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec (A ⊗ A) := by
  unfold eSec
  rw [← Over.comp_left]
  congr 1
  ext <;> simp [Hom.one_def]

theorem cls_eSec (c : SiegPre h n ζ s) : CechPic.pull (eSec (G2 c.A)) (CechPic.cls c.P c.isLB) = 0 := by
  obtain ⟨t, ht⟩ := c.rig₁
  have z := (CechPic.cls_eq_zero_iff (pull_isLB c.isLB _)).2 ⟨t, ht⟩
  rw [CechPic.cls_pull c.isLB] at z
  rw [← eSec_sq, CechPic.pull_comp, z, map_zero]

theorem eSec_fst {X : Scheme.{0}} (A : Over X) [GrpObj A] : eSec (A ⊗ A) ≫ (fst A A).left = eSec A := by
  unfold eSec
  rw [← Over.comp_left]
  congr 1
  simp

theorem eSec_snd {X : Scheme.{0}} (A : Over X) [GrpObj A] : eSec (A ⊗ A) ≫ (snd A A).left = eSec A := by
  unfold eSec
  rw [← Over.comp_left]
  congr 1
  simp

theorem mono_of_fac {T T₁ : Scheme.{0}} {G G' : Over T} {G₁ : Over T₁} [GrpObj G] [GrpObj G₁] {p : T₁ ⟶ T} [Flat p]
    [Surjective p] {φ₁ : G₁.left ⟶ G.left} {ψ₁ : G₁.left ⟶ G'.left} {φ : G.left ⟶ G'.left}
    (hφ : IsPullback φ₁ G₁.hom G.hom p) (hψ : IsPullback ψ₁ G₁.hom G'.hom p) (e : φ₁ ≫ φ = ψ₁)
    (w : φ ≫ G'.hom = G.hom) : Mono φ := by
  constructor
  intro W a b hab
  have hw : a ≫ G.hom = b ≫ G.hom := by rw [← w, ← Category.assoc, hab, Category.assoc]
  have : Epi (pullback.fst (a ≫ G.hom) p) := Flat.epi_of_flat_of_surjective _
  have ca : (pullback.fst (a ≫ G.hom) p ≫ a) ≫ G.hom = pullback.snd (a ≫ G.hom) p ≫ p := by
    rw [Category.assoc, pullback.condition]
  have cb : (pullback.fst (a ≫ G.hom) p ≫ b) ≫ G.hom = pullback.snd (a ≫ G.hom) p ≫ p := by
    rw [Category.assoc, ← hw, pullback.condition]
  have eq : hφ.lift _ _ ca = hφ.lift _ _ cb := by
    apply hψ.hom_ext
    · rw [← e, ← Category.assoc, ← Category.assoc, hφ.lift_fst, hφ.lift_fst, Category.assoc, Category.assoc, hab]
    · rw [hφ.lift_snd, hφ.lift_snd]
  rw [← cancel_epi (pullback.fst (a ≫ G.hom) p), ← hφ.lift_fst _ _ ca, ← hφ.lift_fst _ _ cb, eq]

section Core

variable {T T₁ : Scheme.{0}} {B₁ : Type} [CommRing B₁] {ζ₁ : B₁} {s₁ : T₁ ⟶ Sp B₁}

theorem comp_eq_of_comp_eq (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} {c : SiegPre h n ζ' sc}
    {u : SiegPre h n (b.ζ : B) su} {c₁ : SiegPre h n ζ₁ s₁} {p : T₁ ⟶ T} {φ₁ : c₁.A.left ⟶ c.A.left}
    {ψ₁ : c₁.A.left ⟶ u.A.left} (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SRelBy c₁ c 1 1 p φ₁)
    (k : SRelBy c₁ u 1 1 p ψ₁) {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ c₁.A.left) (e : g₁ ≫ φ₁ = g₂ ≫ φ₁) :
    g₁ ≫ ψ₁ = g₂ ≫ ψ₁ := by
  obtain ⟨-, hφ, -⟩ := (sRelBy_one_iff _ _ _ _).1 m
  have hz : (g₁ ≫ c₁.A.hom) ≫ p = (g₂ ≫ c₁.A.hom) ≫ p := by
    rw [Category.assoc, Category.assoc, ← hφ.1.w, ← Category.assoc, e, Category.assoc]
  obtain ⟨⟨o, ho'⟩, -⟩ := GlobalTheory.siegPre_pullback h n B₁ ζ₁ T₁ Z s₁ ((g₁ ≫ c₁.A.hom) ≫ s₁) (g₁ ≫ c₁.A.hom) c₁ rfl
  obtain ⟨κ, hκ⟩ := exists_of_siegPB ho'
  have k₁ := comp_by m hκ
  rw [hz] at k₁
  obtain ⟨κ', hκ', hκ'b⟩ := cancel_by m k₁
  have n₁ := comp_by k hκ
  have n₂ := comp_by k hκ'b
  rw [← hz] at n₂
  have r := GlobalTheory.T.principal_siegel_object_odd_level_rigid h n n 1 B B₁ b ζ₁ T Z su _ u o _ _ _ hn ho hu n₁ n₂
  obtain ⟨-, hκg, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ
  obtain ⟨-, hκ'g, -⟩ := (sRelBy_one_iff _ _ _ _).1 hκ'b
  have hl : g₁ ≫ c₁.A.hom = 𝟙 Z ≫ g₁ ≫ c₁.A.hom := (Category.id_comp _).symm
  have h₁ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ = g₁ := hκg.1.lift_fst _ _ _
  have h₀ : hκg.1.lift g₁ (𝟙 Z) hl ≫ o.A.hom = 𝟙 Z := hκg.1.lift_snd _ _ _
  have h₂ : hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' = g₂ := by
    apply hφ.1.hom_ext
    · rw [Category.assoc, hκ', ← Category.assoc, h₁, e]
    · rw [Category.assoc, hκ'g.1.w, ← Category.assoc, h₀, Category.id_comp]
  calc g₁ ≫ ψ₁ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ ≫ ψ₁ := by rw [← Category.assoc, h₁]
    _ = hκg.1.lift g₁ (𝟙 Z) hl ≫ κ' ≫ ψ₁ := by rw [r]
    _ = g₂ ≫ ψ₁ := by rw [← Category.assoc, h₂]

theorem siegPB_id_of_cover (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} (c : SiegPre h n ζ' sc)
    (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (p : T₁ ⟶ T) [IsFinite p] [Etale p] [Surjective p]
    (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SiegPB c₁ c p) (k : SiegPB c₁ u p) : SiegPB c u (𝟙 T) := by
  obtain ⟨φ₁, hm⟩ := exists_of_siegPB m
  obtain ⟨ψ₁, hk⟩ := exists_of_siegPB k
  obtain ⟨φ₁₂, hφ, sq₁, iso₁, lev₁⟩ := (sRelBy_one_iff _ _ _ _).1 hm
  obtain ⟨ψ₁₂, hψ, sq₂, iso₂, lev₂⟩ := (sRelBy_one_iff _ _ _ _).1 hk
  have : QuasiCompact p := inferInstance
  have : Flat p := inferInstance
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

end Core

end GlobalTheory.SiegPBDescent

namespace GlobalTheory

theorem siegPB_of_finite_etale_cover : ∀ (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁) (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y), 3 ≤ n → Odd n → u.Principal → IsFinite p → Etale p → Surjective p → SiegPB c₁ c p → SiegPB c₁ u (p ≫ f) → SiegPB c u f := by
  intro h n B _ b S S₁ Y s s₁ sY c c₁ u p f hn ho hu _ _ _ m k
  obtain ⟨⟨u', hu'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h n B (b.ζ : B) Y S sY (f ≫ sY) f u rfl
  have k' : SiegPB c₁ u' p := SiegelPullComp.pb_cancel hu' k
  have e := SiegelPullComp.pb_comp hu' (SiegPBDescent.siegPB_id_of_cover b c u' c₁ p hn ho (hpr u' hu' hu) m k')
  rwa [Category.id_comp] at e

end GlobalTheory
