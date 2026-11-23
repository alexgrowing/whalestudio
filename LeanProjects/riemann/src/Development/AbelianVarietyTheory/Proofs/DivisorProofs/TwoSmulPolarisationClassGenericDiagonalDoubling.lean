import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DiagPic

open GlobalTheory.CechPic

theorem pull_inv {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull (GrpObj.inv : A.A ⟶ A.A).left (cls A.L A.isLB) = cls A.L A.isLB := by
  obtain ⟨U, hU, ht⟩ := A.sym (default : PrimeSpectrum K)
  have h := (cls_eq_zero_iff (LB.isLB_linComb A.isLB _ _)).2 ht
  rw [cls_linComb A.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, add_neg_eq_zero] at h
  have hr : Set.range (𝟙 A.A.left : A.A.left ⟶ A.A.left) ⊆ Set.range (A.A.hom ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    intro x _
    have e : A.A.hom x = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    show A.A.hom x ∈ U
    rw [e]
    exact hU
  have h' := congrArg (pull (IsOpenImmersion.lift (A.A.hom ⁻¹ᵁ U).ι (𝟙 _) hr)) h
  rwa [← pull_comp, ← pull_comp, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac, Category.id_comp,
    pull_id] at h'

theorem pull_one {S : Scheme.{0}} (A : PolAV S) {T : Over S} :
    pull (1 : T ⟶ A.A).left (cls A.L A.isLB) = 0 := by
  have h := (cls_eq_zero_iff (pull_isLB A.isLB _)).2 A.rigid
  rw [cls_pull A.isLB] at h
  rw [Hom.one_def, Over.comp_left, pull_comp]
  exact (congrArg _ h).trans (map_zero _)

theorem lam_self {K : Type} [Field K] (A : PolAV (Sp K)) :
    lam (cls A.L A.isLB) (𝟙 A.A) (𝟙 A.A) = 2 • cls A.L A.isLB := by
  have h := lam_mul_left A.isLB (GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB) (𝟙 A.A) (𝟙 A.A)⁻¹ (𝟙 A.A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls A.L A.isLB) (𝟙 A.A)⁻¹ (𝟙 A.A) = -(2 • cls A.L A.isLB) := by
    rw [lam, inv_mul_cancel, pull_one, Hom.inv_def, Category.id_comp, pull_inv, Over.id_left, pull_id]
    abel
  rw [e] at h
  exact (add_neg_eq_zero.1 h.symm)

theorem pull_sq {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull ((𝟙 A.A) ^ 2 : A.A ⟶ A.A).left (cls A.L A.isLB) = 4 • cls A.L A.isLB := by
  have h := lam_self A
  rw [lam, pull_one, Over.id_left, pull_id, add_zero, sub_sub, sub_eq_iff_eq_add] at h
  rw [pow_two, h]
  abel

end GlobalTheory.Mum.DiagPic

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem two_smul_cls_eq_pull_diag_and_pull_sq : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (c : GlobalTheory.CechPic.Pic (pullback G.hom (jK R))) (d : GlobalTheory.CechPic.Pic G.left) (hL : (A.L.pull gen.hom.left).IsLB) (hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB), c = GlobalTheory.CechPic.cls (A.L.pull gen.hom.left) hL → d = GlobalTheory.CechPic.cls (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) hP → 2 • c = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) d ∧ ∃ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left ∧ GlobalTheory.CechPic.pull φ c = 4 • c := by
  intro R _ _ G _ _ A gen hgen PP hExt c d hL hP hc hd
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have hc' : c = pull gen.hom.left (cls A.L A.isLB) := hc
  refine ⟨?_, ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left, ?_, ?_⟩
  · obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
      (isGrpPullback_pullback G (jK R))
    have h₁ := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hExt.1 g₂)).2 (hExt.2 g₂ hg₂)
    have h₂ := (cls_cube_two hL (fst _ _) (snd _ _) (LB.isLB_linComb hL _ _)).symm.trans h₁
    have h₃ := congrArg (pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left) h₂
    have e : (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left ≫ g₂ =
        pullback.fst G.hom (jK R) ≫ (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left := by
      apply pullback.hom_ext
      · show (_ ≫ g₂) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
        rw [Category.assoc, hg₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · show (_ ≫ g₂) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
        rw [Category.assoc, hg₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    rw [pull_lam, lift_fst, lift_snd, cls_pull hExt.1, ← pull_comp, e, pull_comp, cls_pull A.isLB, lam_pull,
      Category.id_comp] at h₃
    have h₄ := pull_lam gen.hom (cls A.L A.isLB) (𝟙 _) (𝟙 _)
    rw [Category.comp_id, DiagPic.lam_self, map_nsmul] at h₄
    rw [hc', hd]
    exact h₄.trans h₃
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) = (Over.pullback (jK R)).map ((𝟙 G) ^ 2) := by
      rw [pow_two, pow_two, Functor.map_mul, CategoryTheory.Functor.map_id]
    rw [e]
    exact pullback.lift_fst _ _ _
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) ≫ gen.hom = gen.hom ≫ (𝟙 A.A) ^ 2 := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    have h := congrArg (pull gen.hom.left) (DiagPic.pull_sq A)
    rw [← pull_comp, ← Over.comp_left, ← e, Over.comp_left, pull_comp, map_nsmul] at h
    rw [hc']
    exact h

end GlobalTheory.Mum
