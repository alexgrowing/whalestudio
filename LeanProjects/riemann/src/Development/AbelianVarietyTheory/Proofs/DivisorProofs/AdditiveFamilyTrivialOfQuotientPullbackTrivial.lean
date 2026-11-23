import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualInjPull

theorem smooth_of_dimLe {S : Scheme.{0}} {A C : Over S} (h : DimLe A C) {g : ℕ}
    (hA : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension g C.hom := by
  have h1 : SmoothOfRelativeDimension g (pullback.snd A.hom (𝟙 S)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom (𝟙 S)) hA
  have h2 := h g S (𝟙 S) h1
  have sq : IsPullback (inv (pullback.fst C.hom (𝟙 S))) C.hom (pullback.snd C.hom (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h2

theorem isIso_of_mono' {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B)
    (hB' : IsAbelianScheme B') {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    (hg' : SmoothOfRelativeDimension g B'.hom) (x : B ⟶ B') [Mono x] : IsIso x := by
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem evc_of_iso {S : Scheme.{0}} {A T X U Y : Over S} {M : LB (A ⊗ T).left} {N : LB (X ⊗ U).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : A ⊗ T ⟶ X) (g : A ⊗ T ⟶ U) (e : LBIso M (ev N f g))
    (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN (lift a t ≫ f) (lift a t ≫ g) := by
  have c : cls M hM = cls _ (pull_isLB hN _) := (cls_eq_iff hM (pull_isLB hN _)).2 e
  rw [← evc_ev hN f g (pull_isLB hN _) a t, evc, evc, c]

theorem triv_of_triv_pull : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  intro K _ _ A A' B _ _ _ g P P' q hA hA' hB hgA' hgB hD hq hP' haP' eP T M hM haM hT
  obtain ⟨C, _, Q, hC, hdim, hQ⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare _ A' hA'
  have hgC : SmoothOfRelativeDimension g C.hom := smooth_of_dimLe hdim hgA'
  have hP := hD.isLB
  have hQl := hQ.isLB
  have hR : (ev Q (fst A C ≫ q) (snd A C)).IsLB := pull_isLB hQl _
  have haR : IsAdditive (ev Q (fst A C ≫ q) (snd A C)) := by
    refine (isAdditive_iff hR).2 fun Y a a' t ↦ ?_
    rw [evc_ev hQl, evc_ev hQl, evc_ev hQl]
    simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff hQl).1 hQ.additive Y _ _ t
  obtain ⟨s, hs, -⟩ := hQ.univ B P' hP' haP'
  obtain ⟨r, hr, -⟩ := hD.univ C _ hR haR
  have hsr : s ≫ r = 𝟙 B := by
    refine GlobalTheory.AbDual.IsDual.eq_of_evc hD ?_
    have e1 := evc_of_iso hR hP _ _ hr (fst A B) (snd A B ≫ s)
    have e1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A B) (snd A B ≫ s)
    have e2 := evc_of_iso hP' hQl _ _ hs (fst A B ≫ q) (snd A B)
    have e3 : evc hP' (fst A B ≫ q) (snd A B) = evc hP (fst A B) (snd A B) := by
      rw [← cls_ev hP' _ _ (pull_isLB hP' _), (cls_eq_iff _ hP).2 eP, evc, lift_fst_snd, Over.id_left, pull_id]
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at e1 e1' e2
    rw [Category.comp_id, ← e3, e2, ← e1', e1]
  obtain ⟨c, hc, -⟩ := hQ.univ T M hM haM
  have hcr : c ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ c)
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ c)
    have f2 := evc_of_iso hM hQl _ _ hc (fst A T ≫ q) (snd A T)
    have f3 := (triv_ev_iff hM _ _).1 hT
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1' f2
    rw [← f1, f1', ← f2, f3]))
  have h1r : (1 : T ⟶ C) ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ (1 : T ⟶ C))
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ (1 : T ⟶ C))
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1'
    rw [← f1, f1', MonObj.comp_one, evc_one_right hQl hQ.zero]))
  haveI : IsSplitMono s := IsSplitMono.mk' ⟨r, hsr⟩
  haveI : IsIso s := isIso_of_mono' hB hC hgB hgC s
  have hrinv : r = inv s := (IsIso.inv_eq_of_hom_inv_id hsr).symm
  haveI : IsIso r := by rw [hrinv]; infer_instance
  have hc1 : c = 1 := (cancel_mono r).1 (hcr.trans h1r.symm)
  refine (cls_eq_zero_iff hM).1 ?_
  rw [(cls_eq_iff hM (pull_isLB hQl _)).2 hc, cls_ev hQl, hc1, MonObj.comp_one, evc_one_right hQl hQ.zero]
end GlobalTheory.DualInjPull
