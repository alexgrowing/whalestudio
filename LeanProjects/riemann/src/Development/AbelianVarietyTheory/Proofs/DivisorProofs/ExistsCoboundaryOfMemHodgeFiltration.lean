import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCobWholeOfIsCobCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulHodgeFilEqZeroOfDeRhamCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParCocIsCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParCocSpOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtAlgCompRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundaryStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OrthPt

variable {R : Type} [CommRing R]

theorem iSup_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens} (hW : ⨆ i, W i = ⊤)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : ⨆ i, parCov W x i = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top _ hW

theorem sm_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens}
    {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E]
    (φ : D →ₐ[R] D') (x : Pt A D) (z : Pt (SpAlg R D' ⊗ B) E) (h : Sm (parCov W (spOver φ ≫ x)) z) :
    Sm (parCov W x) (z ≫ spOver φ ▷ B) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  unfold parCov at hi ⊢
  rw [comp_whiskerRight, Over.comp_left, Scheme.Hom.comp_preimage] at hi
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  exact hi

theorem sumMul_elim {B : Over (Sp R)} {D : Type} [CommRing D] [Algebra R D] {I₁ I₂ I₃ : Type} [Fintype I₁]
    [Fintype I₂] [Fintype I₃] (d₁ : I₁ → D) (d₂ : I₂ → D) (d₃ : I₃ → D)
    (β₁ : I₁ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (β₂ : I₂ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (β₃ : I₃ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
    (z : Pt (SpAlg R D ⊗ B) E) :
    sumMul (Sum.elim d₁ (Sum.elim (fun i ↦ -d₂ i) (fun i ↦ -d₃ i)))
        (fun i ↦ fv (Sum.elim β₁ (Sum.elim β₂ β₃) i)) E E' ψ z =
      sumMul d₁ (fun i ↦ fv (β₁ i)) E E' ψ z - sumMul d₂ (fun i ↦ fv (β₂ i)) E E' ψ z -
        sumMul d₃ (fun i ↦ fv (β₃ i)) E E' ψ z := by
  simp only [sumMul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem exists_isCob_of_mem_fil : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (K : Type) (W : K → (A ⊗ B).left.Opens), ⨆ i, W i = ⊤ → ∀ (J : Type) [Fintype J] (a : J → Fn1 A) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → IsCupCob W a (fun i ↦ fv (β i)) n → ∀ y ∈ Fil B, ∃ k : Fn0 A, IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, a i D D' φ x * algebraMap R D' (y ⟨_, hβ i⟩)) k := by
  intro H R _ A B _ g hB hg K W hW J _ a β hβ n ha hn y hy
  have hP : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f ∈ primDR B := fun f ↦ by
    have h : primDR B = ⊤ := ((GlobalTheory.abelianDeRham_free_baseChange_rigid H).1 R B g hB hg).1
    rw [h]; trivial
  have hfv : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), IsCoc (whole B) (fv f) := fun f ↦ (fv_isCoc_and_ev_eq R B f).1
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (m : ℕ) (d : Fin m → D) (c : Fin m → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (k : Fn0 (SpAlg R D ⊗ B)),
        IsCob (parCov W x) ((parCoc a (fun i ↦ fv (β i)) n x).add (sumMul d fun i ↦ fv (c i)).neg) k := by
    intro D _ _ x
    obtain ⟨u, hu, k₁, h₁⟩ := GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary R _ K (parCov W x) (iSup_parCov hW x) _
      (GlobalTheory.PtExt.parCoc_isCoc R A B K W J a _ n ha (fun i ↦ hfv _) hn D x)
    obtain ⟨m, d, c, k₂, h₂⟩ := GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul H R B g hB hg D u hu
    refine ⟨m, d, c, fun E _ _ z ↦ k₁ E z + k₂ E z, ?_⟩
    intro E _ _ E' _ _ ψ z hz
    have e₁ := h₁ E E' ψ z hz
    have e₂ := h₂ E E' ψ z (sm_whole z)
    simp only [Fn1.add, Fn1.neg] at e₁ e₂ ⊢
    rw [map_add]
    linear_combination e₁ + e₂
  choose m d c k hk using key
  refine ⟨fun D _ _ x ↦ ∑ j, d D x j * algebraMap R D (y ⟨_, hP (c D x j)⟩), ?_⟩
  intro D _ _ D' _ _ φ x _
  have hcob : IsCob (parCov W (spOver φ ≫ x))
      (sumMul (Sum.elim (d D' (spOver φ ≫ x)) (Sum.elim (fun i ↦ -φ (d D x i)) (fun i ↦ -a i D D' φ x)))
        (fun i ↦ fv (Sum.elim (c D' (spOver φ ≫ x)) (Sum.elim (c D x) β) i)))
      (fun E _ _ z ↦ k D x E (z ≫ spOver φ ▷ B) - k D' (spOver φ ≫ x) E z) := by
    intro E _ _ E' _ _ ψ z hz
    have e₁ := hk D' (spOver φ ≫ x) E E' ψ z hz
    have e₂ := hk D x E E' ψ (z ≫ spOver φ ▷ B) (sm_parCov φ x z hz)
    have e₃ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      (GlobalTheory.PtExt.parCoc_spOver R A B J a (fun i ↦ fv (β i)) n ha D D' φ x)
    have e₄ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      ((GlobalTheory.PtExt.SumMulFacts.main R D B _ (d D x) (fun i ↦ fv (c D x i))).2 D' φ)
    rw [sumMul_elim]
    simp only [Fn1.add, Fn1.neg, Fn1.pull] at e₁ e₂ e₃ e₄
    beta_reduce
    rw [map_sub, Category.assoc]
    linear_combination e₂ - e₁ + e₃ + e₄
  have h0 := GlobalTheory.T.sum_mul_hodgeFil_eq_zero_of_deRham_coboundary H R B g hB hg y hy D' _ _ _ (fun i ↦ hP _)
    (GlobalTheory.PtExt.isCob_whole_of_isCob_cover R _ K _ (iSup_parCov hW (spOver φ ≫ x)) _
      ((GlobalTheory.PtExt.SumMulFacts.main R D' B _ _ _).1 fun i ↦ hfv _) _ hcob)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h0
  simp only [map_sum, map_mul, AlgHom.commutes]
  linear_combination -h0

end GlobalTheory.PtExt.OrthPt
