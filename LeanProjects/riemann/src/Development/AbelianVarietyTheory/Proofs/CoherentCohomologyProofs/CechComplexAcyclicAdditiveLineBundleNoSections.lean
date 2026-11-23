import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyZeroEquivSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyFiniteOfAffineCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankCechLBHomologyExtProdStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.PicZeroVan

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A : C) [GrpObj A] :
    IsIso (lift μ[A] (snd A A)) := by
  have hμ : μ[A] = fst A A * snd A A := by simp [Hom.mul_def]
  refine ⟨lift (fst A A * (snd A A)⁻¹) (snd A A), ?_, ?_⟩
  · ext
    · rw [Category.assoc, lift_fst, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, hμ]
      simp
    · simp
  · ext
    · rw [Category.assoc, lift_fst, hμ, comp_mul, lift_fst, lift_snd]
      simp
    · simp

theorem isPullback_mul_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    IsPullback μ[A].left (snd A A).left A.hom A.hom := by
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    IsPullback.of_hasPullback A.hom A.hom
  have := isIso_shear A
  have : IsIso (lift μ[A] (snd A A)).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (lift μ[A] (snd A A))))
  have h₁ : IsPullback (lift μ[A] (snd A A)).left (snd A A).left (snd A A).left (𝟙 A.left) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Over.comp_left, lift_snd, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz h₀
  rwa [← Over.comp_left, lift_fst, Category.id_comp] at h₂

theorem exists_fin_affine_cover (Z : Scheme.{0}) [CompactSpace Z] :
    ∃ (n : ℕ) (E : Fin n → Z.Opens), (∀ i, IsAffineOpen (E i)) ∧ ⨆ i, E i = ⊤ := by
  obtain ⟨s, hs, e⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
    (X := Z) (U := Set.univ)).1 ⟨isCompact_univ, isOpen_univ⟩
  have := hs.fintype
  refine ⟨Fintype.card s, fun i => ((Fintype.equivFin s).symm i).1.1,
    fun i => ((Fintype.equivFin s).symm i).1.2, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ (Set.univ : Set Z) := trivial
  rw [e] at hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hx⟩ := hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨Fintype.equivFin s ⟨i, hi⟩, by simpa using hx⟩

theorem prod_res_pullU_one {X X' : Scheme.{0}} {J : Type} [Fintype J] (φ : J → (X' ⟶ X))
    (ε : J → ℤ) (W : X'.Opens) (V : J → X.Opens) (h : ∀ k, W ≤ φ k ⁻¹ᵁ V k) :
    ∏ k, res (h k) (pullU (φ k) (V k) 1) ^ ε k = 1 := by
  simp

theorem linComb_g_eq_one {X X' : Scheme.{0}} (L : LB X) (hL : ∀ i j, L.g i j = 1) {J : Type}
    [Fintype J] (φ : J → (X' ⟶ X)) (ε : J → ℤ) (i j : J → L.ι) :
    (L.LinComb φ ε).g i j = 1 := by
  have h := prod_res_pullU_one φ ε (L.wchart φ i ⊓ L.wchart φ j) (fun k => L.U (i k) ⊓ L.U (j k))
    (fun k => le_inf (inf_le_left.trans (LB.wchart_le L φ i k))
      (inf_le_right.trans (LB.wchart_le L φ j k)))
  simp only [← hL] at h
  exact h

theorem tw_pull_triv {X X' : Scheme.{0}} (N : LB X') (π : X' ⟶ X) :
    tw N ((Inh.trivLB X).pull π) 0 = tw N ((Inh.trivLB X).pull π) 1 := by
  have h : ∀ i j, ((Inh.trivLB X).pull π).g i j = 1 := fun i j =>
    linComb_g_eq_one (Inh.trivLB X) (fun _ _ => rfl) _ _ i j
  simp only [tw, pw, h, one_zpow]

theorem nontrivial_secOnR_triv {R : Type} [CommRing R] {X : Scheme.{0}} [Nonempty X]
    (f : X ⟶ Spec (CommRingCat.of R)) : Nontrivial (SecOnR f (Inh.trivLB X) ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := inferInstance
  exact ((SecOnR.of f _ ⊤).symm ≪≫ₗ secOnTrivEquiv ⊤).toEquiv.nontrivial

theorem cechLB_acyclic_of_additive : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → (∃ w : LB.Iso (M.pull μ[P.A].left) (tw (M.pull (fst P.A P.A).left) (M.pull (snd P.A P.A).left) 1), w.IsGen) → (∀ (σ : LB.Sec M) i, σ.f i = 0) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → P.A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB P.A.hom M D).Acyclic := by
  intro K _ _ P M hM ⟨w, hw⟩ hσ κ _ _ D hD hD'
  obtain ⟨⟨hproj, hsep⟩, -⟩ := AbProj.abelian_projective_baseChange K P
  have := P.isAb.proper
  have hO := Inh.trivLB_isLB P.A.left
  have h₀ : IsPullback (fst P.A P.A).left (snd P.A P.A).left P.A.hom P.A.hom :=
    IsPullback.of_hasPullback P.A.hom P.A.hom
  have h₁ := isPullback_mul_snd P.A
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have : QuasiCompact (fst P.A P.A).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) h₀.flip inferInstance
  have : CompactSpace (P.A ⊗ P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst P.A P.A).left
  have : Nonempty P.A.left := ⟨η[P.A].left (Classical.arbitrary (Spec (CommRingCat.of K)))⟩
  obtain ⟨k, E, hE, hE'⟩ := exists_fin_affine_cover (P.A ⊗ P.A).left
  have finM := cechLB_homology_finite_of_affine_cover K _ P.A.hom M κ D hM hsep hproj hD hD'
  have finO := cechLB_homology_finite_of_affine_cover K _ P.A.hom _ κ D hO hsep hproj hD hD'
  have k₀ := GlobalTheory.T.finrank_cechLB_homology_extProd_alt K _ _ _ _ _ _ _ M M h₀ hM hM hsep hsep κ D κ D _ E hD hD' hD hD' hE hE'
    finM finM
  have k₁ := GlobalTheory.T.finrank_cechLB_homology_extProd_alt K _ _ _ _ _ _ _ M _ h₁ hM hO hsep hsep κ D κ D _ E hD hD' hD hD' hE hE'
    finM finO
  have hf : μ[P.A].left ≫ P.A.hom = (fst P.A P.A).left ≫ P.A.hom :=
    (Over.w μ[P.A]).trans (Over.w (fst P.A P.A)).symm
  rw [hf, ← tw_pull_triv] at k₁
  have iso : cechLB ((fst P.A P.A).left ≫ P.A.hom)
      (tw (M.pull μ[P.A].left) ((Inh.trivLB P.A.left).pull (snd P.A P.A).left) 0) E ≅
      cechLB ((fst P.A P.A).left ≫ P.A.hom)
        (tw (M.pull (fst P.A P.A).left) (M.pull (snd P.A P.A).left) 1) E :=
    (cechLBTwZero _ E (LB.isLB_pull hM _) (LB.isLB_pull hO _)).symm ≪≫
      cechLBCongr _ E (LB.isLB_pull hM _) (isLB_tw (LB.isLB_pull hM _) (LB.isLB_pull hM _) 1) w hw
  have hO₀ : 0 < Module.finrank K ((cechLB P.A.hom (Inh.trivLB P.A.left) D).homology 0) := by
    obtain ⟨e⟩ := cechLB_homology_zero_equiv_sections K _ P.A.hom (Inh.trivLB P.A.left) κ D hD'
    have := nontrivial_secOnR_triv P.A.hom
    have := e.toEquiv.nontrivial
    have := finO 0
    exact Module.finrank_pos
  have hM₀ : Module.finrank K ((cechLB P.A.hom M D).homology 0) = 0 := by
    obtain ⟨e⟩ := cechLB_homology_zero_equiv_sections K _ P.A.hom M κ D hD'
    have : Subsingleton (LB.Sec M) := ⟨fun a b => by
      obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      congr 1
      funext i
      exact (hσ ⟨a, ha⟩ i).trans (hσ ⟨b, hb⟩ i).symm⟩
    have := (SecOnR.topEquiv P.A.hom M).toEquiv.subsingleton
    have := e.toEquiv.subsingleton
    exact Module.finrank_zero_of_subsingleton
  have key : ∀ n, Module.finrank K ((cechLB P.A.hom M D).homology n) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hz := k₀ n
      rw [Finset.sum_eq_zero fun x hx => ?_,
        ← (HomologicalComplex.homologyMapIso iso n).toLinearEquiv.finrank_eq, k₁ n,
        Finset.sum_eq_zero_iff] at hz
      · exact (mul_eq_zero.1 (hz (n, 0) (by simp))).resolve_right hO₀.ne'
      · have hx' : x.1 + x.2 = n := by simpa using hx
        rcases Nat.eq_zero_or_pos x.2 with h | h
        · rw [h, hM₀, mul_zero]
        · rw [ih x.1 (by omega), zero_mul]
  intro n
  have := finM n
  have : Subsingleton ((cechLB P.A.hom M D).homology n) := Module.finrank_zero_iff.1 (key n)
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_of_subsingleton _)

end GlobalTheory.PicZeroVan
