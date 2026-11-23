import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPullbackComposite
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

namespace GlobalTheory.ThetaDescent

open Limits (pullback)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.RigSymSubring

private theorem isPullback_sq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom f) :
    IsPullback (GlobalTheory.sqMap h.w) (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : GlobalTheory.sqMap h.w ≫ (fst G G).left = (fst G' G').left ≫ φ := pullback.lift_fst _ _ _
  have e₂ : GlobalTheory.sqMap h.w ≫ (snd G G).left = (snd G' G').left ≫ φ := pullback.lift_snd _ _ _
  have a' : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have a : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have b := a'.paste_horiz h
  rw [← e₁, ← h.w] at b
  have c := (IsPullback.of_right b e₂ a).paste_vert h
  rw [Over.w, Over.w] at c
  exact c

private theorem sq_comp {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} {φ : A'.left ⟶ A.left} {φ' : A''.left ⟶ A'.left}
    {χ : A''.left ⟶ A.left} (w : φ ≫ A.hom = A'.hom ≫ f) (w' : φ' ≫ A'.hom = A''.hom ≫ g)
    (w'' : χ ≫ A.hom = A''.hom ≫ k) (e : φ' ≫ φ = χ) :
    GlobalTheory.sqMap w' ≫ GlobalTheory.sqMap w = GlobalTheory.sqMap w'' := by
  subst e
  apply pullback.hom_ext
  · simp only [GlobalTheory.sqMap, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [GlobalTheory.sqMap, pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

private theorem exists_finset (Ω : Type) [Field Ω] (R₀ : Subring Ω) (P₀ : PPAS (Sp R₀)) (PΩ : PPAS (Sp Ω))
    (ρ : PΩ.A.left ⟶ P₀.A.left) (h : PΩ.IsPull P₀ (spMap R₀.subtype) ρ) (L : LB PΩ.A.left) (hL : L.IsLB)
    (hs : Out.Sym PΩ.A L) (hc : PΩ.c = lam (cls L hL) (fst PΩ.A PΩ.A) (snd PΩ.A PΩ.A))
    (M : LB P₀.A.left) (hM : M.IsLB) (e : cls L hL = pull ρ (cls M hM)) :
    ∃ s : Finset Ω, ∀ (R₁ : Subring Ω) (h : R₀ ≤ R₁), (s : Set Ω) ⊆ R₁ →
      ∃ (Q : PPAS (Sp R₁)) (ψ : Q.A.left ⟶ P₀.A.left),
        Q.IsPull P₀ (spMap (Subring.inclusion h)) ψ ∧ Q.HasTheta := by
  classical
  obtain ⟨H, hρ⟩ := h
  have := P₀.isAb.proper
  have : IsProper (P₀.A ⊗ P₀.A).hom :=
    inferInstanceAs (IsProper (pullback.fst P₀.A.hom P₀.A.hom ≫ P₀.A.hom))
  have e₂ : pull ρ (pull (GrpObj.inv : P₀.A ⟶ P₀.A).left (cls M hM)) = pull ρ (cls M hM) := by
    have h₂ := cls_of_sym hL hs
    rwa [e, ← pull_comp, PolBaseChange.inv_comm H, pull_comp] at h₂
  have e₁ : pull (GlobalTheory.sqMap H.1.w) P₀.c =
      pull (GlobalTheory.sqMap H.1.w) (lam (cls M hM) (fst P₀.A P₀.A) (snd P₀.A P₀.A)) := by
    rw [← hρ, hc, e, PPAS.pull_sqMap_lam H]
  obtain ⟨F₁, h₁⟩ := pic_descends Ω R₀ _ _ (PΩ.A ⊗ PΩ.A).hom (P₀.A ⊗ P₀.A).hom _ _ _
    (isPullback_sq H.1) e₁
  obtain ⟨F₂, h₂⟩ := pic_descends Ω R₀ _ _ PΩ.A.hom P₀.A.hom ρ _ _ H.1 e₂
  refine ⟨F₁ ∪ F₂, fun R₁ h hF => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨Q, π, -, H₁, hQ⟩ := PPAS.exists_pull _ _ P₀ (spMap (Subring.inclusion h))
  have a := h₁ R₁ h hF.1 _ _ _ (isPullback_sq H₁.1)
  have b := h₂ R₁ h hF.2 _ Q.A.hom π H₁.1
  refine ⟨Q, π, ⟨H₁, hQ⟩, M.pull π, pull_isLB hM π, sym_of_cls (pull_isLB hM π) ?_, ?_⟩
  · rw [cls_pull hM, ← pull_comp, PolBaseChange.inv_comm H₁, pull_comp, b]
  · rw [hQ, a, PPAS.pull_sqMap_lam H₁, cls_pull hM]

end GlobalTheory.ThetaDescent

open GlobalTheory.ThetaDescent GlobalTheory.CechPic in
theorem _root_.GlobalTheory.T.theta_descent_finite_extension : ∀ (K : Type) [Field K] (P : PPAS (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (PΩ : PPAS (Sp Ω)) (ψ : PΩ.A.left ⟶ P.A.left), PΩ.IsPull P (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ψ → PΩ.HasTheta → ∃ (F : Type) (_ : Field F) (_ : Algebra K F), FiniteDimensional K F ∧ ∃ (Q : PPAS (Sp F)) (ψ' : Q.A.left ⟶ P.A.left), Q.IsPull P (Spec.map (CommRingCat.ofHom (algebraMap K F))) ψ' ∧ Q.HasTheta := by
  classical
  rintro K _ P Ω _ _ _ PΩ ψ ⟨H, hψ⟩ ⟨L, hL, hs, hc⟩
  have := P.isAb.proper
  obtain ⟨R, M, ρ, ⟨t, ht⟩, hM, hρ₁, hρ₂, hI⟩ :=
    GlobalTheory.LBDescent.exists_fg_lb (k := K) (C := Ω) P.A.hom PΩ.A.hom ψ H.1 L hL
  let R₀ : Subring Ω := R.toSubring
  let i₀ : K →+* R₀ := (algebraMap K Ω).codRestrict R₀ fun x => R.algebraMap_mem x
  let j₀ : R →+* R₀ := R.val.toRingHom.codRestrict R₀ fun x => x.2
  obtain ⟨P₀, φ₀, -, H₀, hc₀⟩ := PPAS.exists_pull _ _ P (spMap i₀)
  have es : spMap (algebraMap K Ω) = spMap R₀.subtype ≫ spMap i₀ := spMap_comp i₀ R₀.subtype
  let ρ₀ : PΩ.A.left ⟶ P₀.A.left := H₀.1.lift ψ (PΩ.A.hom ≫ spMap R₀.subtype)
    (by rw [Category.assoc, ← es]; exact H.1.w)
  have a₁ : ρ₀ ≫ φ₀ = ψ := H₀.1.lift_fst _ _ _
  have a₂ : ρ₀ ≫ P₀.A.hom = PΩ.A.hom ≫ spMap R₀.subtype := H₀.1.lift_snd _ _ _
  have HΩ : IsGrpPullback PΩ.A P₀.A (spMap R₀.subtype) ρ₀ :=
    IsGrpPullback.cancel H₀ (H.congr es a₁.symm) a₂
  have hΩ : PΩ.IsPull P₀ (spMap R₀.subtype) ρ₀ :=
    ⟨HΩ, by rw [hψ, hc₀, ← pull_comp, sq_comp H₀.1.w HΩ.1.w H.1.w a₁]⟩
  let r : P₀.A.left ⟶ Limits.pullback P.A.hom (spMap (algebraMap K R)) :=
    Limits.pullback.lift φ₀ (P₀.A.hom ≫ spMap j₀) (by
      rw [H₀.1.w, Category.assoc, spMap_comp_ring]
      rfl)
  have hr : ρ₀ ≫ r = ρ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, a₁, hρ₁]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, a₂, hρ₂, Category.assoc,
        spMap_comp_ring]
      rfl
  have e : cls L hL = pull ρ₀ (cls (M.pull r) (pull_isLB hM r)) := by
    rw [cls_pull hM, ← pull_comp, hr, ← cls_pull hM ρ (pull_isLB hM ρ)]
    exact (cls_eq_iff _ _).2 hI
  obtain ⟨s, hs'⟩ := exists_finset Ω R₀ P₀ PΩ ρ₀ hΩ L hL hs hc _ _ e
  let F : IntermediateField K Ω := IntermediateField.adjoin K ((t ∪ s : Finset Ω) : Set Ω)
  have hF : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hsub : ((t ∪ s : Finset Ω) : Set Ω) ⊆ F := IntermediateField.subset_adjoin _ _
  rw [Finset.coe_union, Set.union_subset_iff] at hsub
  have hle : R₀ ≤ F.toSubalgebra.toSubring := by
    have : R ≤ F.toSubalgebra := by
      rw [← ht]
      exact Algebra.adjoin_le hsub.1
    exact this
  obtain ⟨Q, π, ⟨H₁, hQ⟩, hθ⟩ := hs' F.toSubalgebra.toSubring hle hsub.2
  let j : F.toSubalgebra.toSubring →+* F := F.toSubalgebra.toSubring.subtype.codRestrict F fun x => x.2
  have hp : Q.IsPull P (spMap (Subring.inclusion hle) ≫ spMap i₀) (π ≫ φ₀) :=
    ⟨H₁.comp H₀, by rw [hQ, hc₀, ← pull_comp, sq_comp H₀.1.w H₁.1.w (H₁.comp H₀).1.w rfl]⟩
  have fin := PPAS.isPull_hasTheta_pull _ _ _ P _ (spMap j) ⟨Q, _, hp, hθ⟩
  have ef : spMap j ≫ spMap (Subring.inclusion hle) ≫ spMap i₀ =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [spMap_comp_ring, spMap_comp_ring]
    rfl
  rw [ef] at fin
  exact ⟨F, inferInstance, inferInstance, hF, fin⟩
