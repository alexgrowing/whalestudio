import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.HermitianFormSum

variable {S : Scheme.{0}}

theorem one_left (G : Over S) [GrpObj G] (Y : Over S) : (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem hermForm_sum {g n m : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (b : Fin m → ℂ)
    (W : Fin n → Fin g → ℂ) (W' : Fin m → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i : Fin g → ℂ) (∑ j, b j • W' j : Fin g → ℂ) = ∑ i, ∑ j, a i * star (b j) * hermForm Hm (W i) (W' j) := by
  simp only [hermForm, dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_sum,
    star_mul', Finset.mul_sum, Finset.sum_mul]
  have e1 : ∀ x x1, (∑ x_2 : Fin m, ∑ i : Fin n, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x x1 => Finset.sum_comm
  simp only [e1]
  have e2 : ∀ x, (∑ x1 : Fin g, ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e2]
  rw [Finset.sum_comm (f := fun (x : Fin g) (i : Fin n) => ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e3 : ∀ x, (∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ x_2 : Fin m, ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e3]
  rw [Finset.sum_comm (f := fun (x : Fin g) (x_2 : Fin m) => ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end PositivityTheory.Xgf.HermitianFormSum

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.HermitianFormSum in
theorem hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  intro S G _ L x n n' v v' Γ A hT hG hC
  obtain ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv, hΓ⟩ := hG
  have hη : (η[Q.A] : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    have hw : ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) ≫ G.hom = (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x)).hom := by
      rw [Category.assoc, hPB.1.w, ← Category.assoc, Over.w]
      rfl
    let a₀ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x) ⟶ G := Over.homMk ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) hw
    have hm := hPB.2 (𝟙_ (Over (Sp ℂ))) 1 1 a₀ a₀ rfl rfl
    rw [_root_.mul_one] at hm
    have h1 : a₀ * a₀ = a₀ * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext hm
    have h2 := congrArg (fun h => h.left) (mul_left_cancel h1)
    simp only [a₀, Over.homMk_left, one_left] at h2
    simpa using h2
  have hunit : ∀ T : Over (Sp ℂ), (1 : T ⟶ Q.A).left ≫ ψ = (1 : Over.mk (T.hom ≫ x) ⟶ G).left := by
    intro T
    rw [one_left, one_left, Category.assoc, hη]
    simp
  have hprod : ∀ (k : ℕ) (uu : Fin k → (epsR ℂ ⟶ Q.A)) (dd : Fin k → (epsAt x ⟶ G)),
      (∀ i, (dd i).left = (uu i).left ≫ ψ) → (List.ofFn dd).prod.left = (List.ofFn uu).prod.left ≫ ψ := by
    intro k
    induction k with
    | zero => intro uu dd _; simpa using (hunit (epsR ℂ)).symm
    | succ k ih =>
      intro uu dd h
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
      exact hPB.2 (epsR ℂ) _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hsp : ∀ (c : ℂ), spMap (epsScaleR c) ≫ (epsR ℂ).hom = (epsR ℂ).hom := by
    intro c
    simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    · simp [epsScaleR]
    · simp [epsScaleR]
  have htan : ∀ i, IsTangent (v₁ i) := by
    intro i
    apply hPB.1.hom_ext
    · rw [Category.assoc, (hv i).1, hT i, one_left, hη]
      rfl
    · rw [Category.assoc, Over.w, Over.w]
      simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have e : ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
        ext z; simp
      erw [e, CommRingCat.ofHom_id, Spec.map_id]
      rfl
  choose u' hu' hv' using hC
  let uu : ∀ k, Fin n → (epsR ℂ ⟶ Q.A) := fun k i =>
    Over.homMk (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) (by rw [Category.assoc, Over.w]; exact hsp _)
  refine ⟨Q, ψ, fun k => (List.ofFn (uu k)).prod, u, Hm, χ, fun k => ∑ i, A k i • W i, hPB, hLB, hAH,
    fun k => ⟨?_, ?_⟩, fun k l => ?_⟩
  · rw [hv' k]
    exact (hprod n (uu k) (u' k) fun i => by
      rw [hu' k i]
      show _ = (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) ≫ ψ
      rw [Category.assoc, (hv i).1]
      rfl).symm
  · exact GlobalTheory.isDiff_sum_smul_of_isLieComb Q.A Q.isAb Q.L Q.g n u v₁ W (A k) _ htan (fun i => (hv i).2)
      ⟨uu k, fun i => rfl, rfl⟩
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hΓ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring

end PositivityTheory.Xgf
