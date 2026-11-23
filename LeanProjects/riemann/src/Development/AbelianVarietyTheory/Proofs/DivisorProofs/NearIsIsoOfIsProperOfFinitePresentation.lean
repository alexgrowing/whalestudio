import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIsPerfectOfAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

section Fibre

open GlobalTheory.NearFibreIso

theorem near_isIso_of_isProper_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [IsProper f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, _, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H
  obtain ⟨U, U', k, k', f'', H', _, ⟨z, rfl⟩, hQ'⟩ :=
    near_isClosedImmersion (g ≫ s) f' K y (by rw [Scheme.Hom.comp_apply]; exact hx)
  have H'' := H'.paste_vert H
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H''
  have : IsOpenImmersion (k' ≫ g') :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'' inferInstance
  have : Flat (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have : LocallyOfFinitePresentation (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have h := GlobalTheory.AbMonoIsoAny.near_isIso_of_finitePresentation ((k ≫ g) ≫ s) f'' K z
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hx)
  have h' := Near.of_pullback f H'' h
  rwa [Scheme.Hom.comp_apply] at h'

theorem isIso_of_geometric_fibres {S X Y : Scheme.{0}} (p : X ⟶ S) (f : Y ⟶ X) [IsProper f]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation (f ≫ p)] [Flat (f ≫ p)]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso (pullback.snd f (pullback.fst p t))) :
    IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : LocallyOfFinitePresentation (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    let K := AlgebraicClosure (s y').asIdeal.ResidueField
    have hK : RingHom.ker (algebraMap Γ(S, U) K) = (s y').asIdeal := by
      rw [IsScalarTower.algebraMap_eq Γ(S, U) (s y').asIdeal.ResidueField K, ← RingHom.comap_ker,
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (s y').asIdeal.ResidueField K).injective,
        ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    let t : Sp K ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) K)
    have hi := h K (t ≫ j)
    have : IsIso (pullback.snd f' (pullback.fst s t)) := by
      have H := (IsPullback.of_hasPullback f' (pullback.fst s t)).flip.paste_vert HY.flip
      have H₀ := (IsPullback.of_hasPullback f (pullback.fst p (t ≫ j))).flip
      have hu : (pullback.fst s t ≫ gX) ≫ p = pullback.snd s t ≫ t ≫ j := by
        rw [Category.assoc, HX.w, pullback.condition_assoc]
      have e : pullback.lift _ _ hu ≫ pullback.fst p (t ≫ j) = pullback.fst s t ≫ gX := pullback.lift_fst _ _ _
      have H₁ := IsPullback.of_bot' (h₁₁ := pullback.snd f' (pullback.fst s t)) (v₁₂ := pullback.lift _ _ hu)
        (by rw [e]; exact H) H₀
      exact (MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip hi
    have h := near_isIso_of_isProper_of_finitePresentation s f' K y' hK
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

end Fibre

variable {S : Scheme.{0}} {A B D : Over S} [GrpObj A] [GrpObj B] [GrpObj D]

theorem isIso_of_isIso_pullback (hB : IsAbelianScheme B) (hD : IsAbelianScheme D) (x : B ⟶ D)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map x)) : IsIso x := by
  have := hB.proper
  have := hB.smooth
  have := hD.proper
  have := hD.smooth
  have : IsProper (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left D.hom
  have : Flat (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left := isIso_of_geometric_fibres D.hom x.left fun Ω _ _ t ↦ by
    have := h Ω t
    have hi : IsIso ((Over.pullback t).map x).left :=
      (Over.forget _).map_isIso ((Over.pullback t).map x)
    have H : IsPullback (pullback.fst B.hom t) ((Over.pullback t).map x).left x.left (pullback.fst D.hom t) := by
      refine IsPullback.of_bot (h₃₁ := t) (v₂₁ := pullback.snd D.hom t) (v₂₂ := D.hom) ?_ ?_
        (IsPullback.of_hasPullback D.hom t)
      · have e : ((Over.pullback t).map x).left ≫ pullback.snd D.hom t = pullback.snd B.hom t :=
          Over.w ((Over.pullback t).map x)
        rw [e, Over.w]
        exact IsPullback.of_hasPullback B.hom t
      · exact (pullback.lift_fst _ _ _).symm
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem additive_of_cube (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B)))
    (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive P ∧ IsAdditive (swap P) := by
  have key : ∀ (T : Over S) (a b c : T ⟶ A ⊗ B),
      evc hP ((a * b * c) ≫ fst A B) ((a * b * c) ≫ snd A B) - evc hP ((a * b) ≫ fst A B) ((a * b) ≫ snd A B) -
        evc hP ((a * c) ≫ fst A B) ((a * c) ≫ snd A B) - evc hP ((b * c) ≫ fst A B) ((b * c) ≫ snd A B) +
        evc hP (a ≫ fst A B) (a ≫ snd A B) + evc hP (b ≫ fst A B) (b ≫ snd A B) +
        evc hP (c ≫ fst A B) (c ≫ snd A B) - evc hP ((1 : T ⟶ A ⊗ B) ≫ fst A B) ((1 : T ⟶ A ⊗ B) ≫ snd A B) = 0 := by
    intro T a b c
    have h := hC S (A ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) P hP T a b c
    have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left)
      ![1, -1, -1, -1, 1, 1, 1, -1]
    have e := (cls_eq_zero_iff hl).2 h
    rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
    simp only [evc, lift_comp_fst_snd]
    rw [← e]
    abel
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := key Y (lift a 1) (lift a' 1) (lift 1 t)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := key Y (lift 1 t) (lift 1 t') (lift a 1)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel

theorem IsDual.isIso_of_cls {P : LB (A ⊗ B).left} {Q : LB (A ⊗ D).left} (hP : IsDual A B P) (hQ : IsDual A D Q)
    {x : B ⟶ D} (e : cls P hP.isLB = evc hQ.isLB (fst A B) (snd A B ≫ x)) : IsIso x := by
  obtain ⟨y, hy, -⟩ := hP.univ D Q hQ.isLB hQ.additive
  have e' : cls Q hQ.isLB = evc hP.isLB (fst A D) (snd A D ≫ y) := (cls_eq_iff hQ.isLB (pull_isLB hP.isLB _)).2 hy
  refine ⟨y, BirigidLift.dual_ext hP ?_, BirigidLift.dual_ext hQ ?_⟩
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e', ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e,
      Category.comp_id]
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e',
      Category.comp_id]

theorem principalPol_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem →
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
      ∀ c : GlobalTheory.CechPic.Pic (A ⊗ A).left, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c →
        ∃ (P : LB (A ⊗ A).left) (hP : P.IsLB), GlobalTheory.CechPic.cls P hP = c ∧ GlobalTheory.AbDual.IsDual A A P := by
  intro hD hC S A _ hA c hc
  obtain ⟨P, hP, rfl⟩ := cls_surj c
  refine ⟨P, hP, rfl, ?_⟩
  obtain ⟨a₁, a₂⟩ := additive_of_cube hC hA hA hP ((triv_ev_iff hP _ _).2 hc.1) ((triv_ev_iff hP _ _).2 hc.2.1)
  obtain ⟨D, _, Q, hD', -, q, q'⟩ := hD S A hA
  obtain ⟨x, hx, e⟩ := BirigidLift.exists_hom q q'.additive hP a₁ a₂
  have ix : IsIso x := isIso_of_isIso_pullback hA hD' x fun Ω _ _ s ↦ by
    obtain ⟨L, hL, -, hK, hc'⟩ := hc.2.2 Ω s
    have f := isGrpPullback_pullback A s
    have d := isGrpPullback_pullback D s
    have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA f
    have := hA₀.comm
    obtain ⟨g, hg⟩ := AbelianDim.exists_relDim Ω _ hA₀
    have p₀ := PerfectDual.isDual_of_isPerfect hD _ _ hA₀ hA₀ hg hg (isPerfect_lam hL hK)
    obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback f d
    have hQ := pull_isLB q.isLB m
    have q₀ := q.baseChange f d m₁ m₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
    refine p₀.isIso_of_cls q₀ ?_
    have l₁ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (fst A A).left = (fst _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_fst (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    have l₂ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (snd A A).left = (snd _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_snd (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    rw [← BirigidLift.pull_evc_eq l₁ l₂ m₁ m₂ q.isLB hQ (x := x) (pullback.lift_fst _ _ _).symm, ← e, hc']
    exact cls_cube_two hL _ _ _
  exact isDual_of_iso S A A D P Q q hP x ix hx ((cls_eq_iff hP (pull_isLB q.isLB _)).1 e)

end GlobalTheory.AbDual
