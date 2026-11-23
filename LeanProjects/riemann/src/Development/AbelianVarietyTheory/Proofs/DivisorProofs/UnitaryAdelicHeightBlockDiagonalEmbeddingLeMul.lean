import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BlockHeight

open scoped NNReal
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation Formalism.UG

section Generic

variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem htOf_blk_le {R : Type} [CommRing R] {N₁ : Matrix (Fin p) (Fin p) R → ℝ≥0} {N₂ : Matrix (Fin q) (Fin q) R → ℝ≥0}
    {N : Matrix (Fin d) (Fin d) R → ℝ≥0} (hN : ∀ a b, N (blk e a b) ≤ max (N₁ a) (N₂ b))
    (X : GL (Fin d) R) (x : GL (Fin p) R) (y : GL (Fin q) R)
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R))
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)
  · rw [h2]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)

theorem bc_val_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R)) :
    ((bc φ X : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e ((bc φ x : GL (Fin p) R') : Matrix (Fin p) (Fin p) R') ((bc φ y : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  show (X : Matrix (Fin d) (Fin d) R).map φ = _
  rw [h1, blk_map _ _ _ (map_zero φ)]
  rfl

theorem bc_inv_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    (((bc φ X)⁻¹ : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e (((bc φ x)⁻¹ : GL (Fin p) R') : Matrix (Fin p) (Fin p) R')
        (((bc φ y)⁻¹ : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  simp only [← map_inv]
  exact bc_val_blk e φ h2

theorem opNorm_blk_le (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin q) (Fin q) ℂ) :
    opNorm (blk e a b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : Fin d → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hcdef
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm a : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_left _ _
    exact this
  have hb : ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm b : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_right _ _
    exact this
  have key : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (blk e a b) (WithLp.toLp 2 v)‖ ^ 2 =
      ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← e.sum_comp, Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, mulVec, dotProduct, ← e.sum_comp, Fintype.sum_sum_type]
  have knorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← e.sum_comp,
      Fintype.sum_sum_type]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).1 ?_
  rw [key, mul_pow, knorm, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem normFin_blk_le (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (a : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) (b : Matrix (Fin q) (Fin q) (Fv F v ⊗[F] E)) :
    normFin F v (blk e a b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 fun i j => ?_
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_apply]
  rcases e.symm i with i | i <;> rcases e.symm j with j | j
  · rw [fromBlocks_apply₁₁]; exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₂]; exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_blk_le (w : InfinitePlace F) (a : Matrix (Fin p) (Fin p) (w.Completion ⊗[F] E))
    (b : Matrix (Fin q) (Fin q) (w.Completion ⊗[F] E)) :
    normInf F w (blk e a b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [blk_map _ _ _ (map_zero (infEmb τ))]
    exact (opNorm_blk_le e _ _).trans
      (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_blk_le (X : GL (Fin d) (AF F ⊗[F] E)) (x : GL (Fin p) (AF F ⊗[F] E)) (y : GL (Fin q) (AF F ⊗[F] E))
    (h1 : (X : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e (x : Matrix (Fin p) (Fin p) (AF F ⊗[F] E)) (y : Matrix (Fin q) (Fin q) (AF F ⊗[F] E)))
    (h2 : ((X⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e ((x⁻¹ : GL (Fin p) (AF F ⊗[F] E)) : Matrix (Fin p) (Fin p) (AF F ⊗[F] E))
        ((y⁻¹ : GL (Fin q) (AF F ⊗[F] E)) : Matrix (Fin q) (Fin q) (AF F ⊗[F] E))) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => ?_)
  · exact htOf_blk_le e (normInf_blk_le F e w) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)
  · exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)
  · exact htOf_blk_le e (normFin_blk_le F e v) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)

theorem ht_blkU_le : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  intro D A B d e J hJ g g₁
  have h := heightGL_blk_le D.host.F e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)).1 (Formalism.L2.Theta.matHom A g)
    (Formalism.L2.Theta.matHom B g₁) rfl (by
      show blk e (Formalism.L2.Theta.mt A g⁻¹) (Formalism.L2.Theta.mt B g₁⁻¹) = _
      simp only [Formalism.L2.Theta.mt, map_inv])
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((heightGL D.host.F _ : ℝ≥0) : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.BlockHeight

end
