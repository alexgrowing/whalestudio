import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsomorphismMonHomDescendsFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullDegIdOfCommonFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FieldDesc
open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_comp_proj {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  exact GlobalTheory.PullDegCompGen.exists_isPullDeg_of_valW D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)

theorem exists_finite_common_pull : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (E₁ E₂ : DegPre K) (E' : DegPre L), IsPullDeg β E₁ E' → IsPullDeg β E₂ E' → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (E₃ : DegPre K'), io.Finite ∧ Nonempty (IsPullDeg io E₁ E₃) ∧ Nonempty (IsPullDeg io E₂ E₃) := by
  intro K L _ _ _ β E₁ E₂ E' h₁ h₂
  haveI := h₁.e_hom
  haveI := h₂.e_hom
  obtain ⟨K', _, io, Ω, _, j, l, φ, hfin, hl, hφ, hcomp⟩ :=
    GlobalTheory.T.isomorphism_mon_hom_descends_finite_extension K L β E₁.P.A E₂.P.A E₁.P.isAb E₂.P.isAb (h₁.e.symm ≪≫ h₂.e) (by dsimp; infer_instance)
  have hP := GlobalTheory.polBaseChange_holds
  obtain ⟨E₃, h₃, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP K K' io E₁ ⊤ (FieldPull.nonempty_psiOn_field E₁) trivial
  obtain ⟨E₄, h₄, -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP K K' io E₂ ⊤ (FieldPull.nonempty_psiOn_field E₂) trivial
  obtain ⟨E'', h', -, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hP L Ω j E' ⊤ (FieldPull.nonempty_psiOn_field E') trivial
  obtain ⟨c₁, pc₁⟩ : ∃ c : IsPullDeg (l.comp io) E₁ E'', proj c = proj h' ≫ proj h₁ := by
    rw [hl]; exact exists_comp_proj j.injective h₁ h'
  obtain ⟨c₂, pc₂⟩ : ∃ c : IsPullDeg (l.comp io) E₂ E'', proj c = proj h' ≫ proj h₂ := by
    rw [hl]; exact exists_comp_proj j.injective h₂ h'
  obtain ⟨g₃, pg₃⟩ := FieldPull.exists_isPullDeg_cancel K K' Ω io l E₁ E₃ E'' h₃ c₁
  obtain ⟨g₄, pg₄⟩ := FieldPull.exists_isPullDeg_cancel K K' Ω io l E₂ E₄ E'' h₄ c₂
  have w₁ : proj h' ≫ E'.P.A.hom = E''.P.A.hom ≫ spMap j := (pull_grp h').1.w
  have w₃ : proj g₃ ≫ E₃.P.A.hom = E''.P.A.hom ≫ spMap l := (pull_grp g₃).1.w
  have w₄ : proj g₄ ≫ E₄.P.A.hom = E''.P.A.hom ≫ spMap l := (pull_grp g₄).1.w
  have key : proj g₃ ≫ h₃.e.hom.left ≫ φ.hom.left = proj g₄ ≫ h₄.e.hom.left := by
    apply pullback.hom_ext
    · have := hcomp E''.P.A.left (proj h' ≫ h₁.e.hom.left) (proj g₃ ≫ h₃.e.hom.left) E''.P.A.hom
        (by simp only [Category.assoc]; exact (pc₁.symm.trans pg₃.symm))
        (by rw [Category.assoc]; exact (congrArg (proj h' ≫ ·) (Over.w h₁.e.hom)).trans w₁)
        (by rw [Category.assoc]; exact (congrArg (proj g₃ ≫ ·) (Over.w h₃.e.hom)).trans w₃)
      simp only [Category.assoc] at this ⊢
      rw [← this]
      have e₁ : h₁.e.hom.left ≫ (h₁.e.symm ≪≫ h₂.e).hom.left = h₂.e.hom.left := by
        rw [Iso.trans_hom, Iso.symm_hom, Over.comp_left, ← Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
          Over.id_left, Category.id_comp]
      rw [reassoc_of% e₁]
      exact (pg₄.trans pc₂).symm
    · simp only [Category.assoc]
      have a := Over.w φ.hom
      have b := Over.w h₃.e.hom
      have c := Over.w h₄.e.hom
      erw [a, b, w₃, c, w₄]
  let Ψ : E₃.P.A ≅ E₄.P.A := h₃.e ≪≫ φ ≪≫ h₄.e.symm
  haveI := h₃.e_hom
  haveI := h₄.e_hom
  haveI := hφ
  have hΨ : IsMonHom Ψ.hom := by dsimp [Ψ]; infer_instance
  have cΨ : g₃.e.hom.left ≫ pullback.fst E₃.P.A.hom (specOf l) ≫ Ψ.hom.left =
      g₄.e.hom.left ≫ pullback.fst E₄.P.A.hom (specOf l) := by
    have k2 : (proj g₃ ≫ h₃.e.hom.left ≫ φ.hom.left) ≫ h₄.e.inv.left = proj g₄ := by
      rw [key, Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]
    refine Eq.trans ?_ k2
    simp only [Ψ, Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc]
  obtain ⟨q⟩ := GlobalTheory.T.nonempty_pullDeg_id_of_common_fieldExtension K' Ω l E₄ E₃ E'' g₄ g₃ Ψ hΨ cΨ
  have hh := nonempty_isPullDeg_comp_of_injective K K' K' io (RingHom.id K') E₂ E₄ E₃ (fun _ _ h => h) ⟨h₄⟩ ⟨q⟩
  rw [RingHom.id_comp] at hh
  exact ⟨K', inferInstance, io, E₃, hfin, ⟨h₃⟩, hh⟩

end GlobalTheory.FieldDesc
