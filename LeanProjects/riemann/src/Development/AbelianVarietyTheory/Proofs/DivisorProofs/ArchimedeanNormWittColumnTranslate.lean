import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameFirstColumnsNeZero
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ArchOrth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compInf_adVec {n : ℕ} (w : InfinitePlace F) (z : Fin n → E) (i : Fin n) :
    compInf F E w (GlobalTheory.EisMidHt.adVec F z i) = inclR (F := F) w.Completion (z i) := by
  change (Algebra.TensorProduct.map (evInf F w) (AlgHom.id F E)) ((1 : AF F) ⊗ₜ[F] z i) =
    (1 : w.Completion) ⊗ₜ[F] z i
  rw [Algebra.TensorProduct.map_tmul, map_one]; rfl

theorem sigR_sigR {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, sigma_sigma hcm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigR_inclR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR R σ (inclR (F := F) R e) = inclR (F := F) R (σ e) := by
  simp [sigR, inclR]

theorem hE_swap {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND σ J) (x y : Fin n → E) : hE σ J x y = σ (hE σ J y x) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, sigma_sigma hcm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ.1 j i]; ring

theorem sum_expand {A : Type} [CommRing A] (s : A →+* A) (hs : ∀ x, s (s x) = x) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) A) (v u : Fin n → A) (c : A)
    (hT : ∑ i, s ((B *ᵥ v) i) * (B *ᵥ u) i = 0) :
    ∑ i, (B *ᵥ (v + c • u)) i * s ((B *ᵥ (v + c • u)) i) =
      ∑ i, (B *ᵥ v) i * s ((B *ᵥ v) i) + c * s c * ∑ i, (B *ᵥ u) i * s ((B *ᵥ u) i) := by
  have hT' : ∑ i, (B *ᵥ v) i * s ((B *ᵥ u) i) = 0 := by
    have := congrArg s hT
    simpa [map_sum, map_mul, hs, mul_comm] using this
  have key : ∀ i, (B *ᵥ (v + c • u)) i * s ((B *ᵥ (v + c • u)) i) =
      (B *ᵥ v) i * s ((B *ᵥ v) i) + c * (s ((B *ᵥ v) i) * (B *ᵥ u) i) +
        s c * ((B *ᵥ v) i * s ((B *ᵥ u) i)) + c * s c * ((B *ᵥ u) i * s ((B *ᵥ u) i)) := by
    intro i
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum, hT, hT']
  ring

theorem cross_eq {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (B : Matrix (Fin n) (Fin n) A) (v u : Fin n → A) :
    ∑ i, s ((B *ᵥ v) i) * (B *ᵥ u) i = ∑ j, s (v j) * ((Formalism.UG.cT s B * B) *ᵥ u) j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem archimedean_norm_add_smul_first_column : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
      GlobalTheory.EisLine.IsAdapted σ J X Y L a → ∀ y : Fin n → E, hE σ J (GlobalTheory.EisMidHt.firstColumn Y) y = 0 →
      ∀ (c : E) (w : InfinitePlace F),
        GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (y + c • GlobalTheory.EisMidHt.firstColumn X) i)) =
          GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F y i)) +
            ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖ *
              GlobalTheory.EisMidHt.normInf a w (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) i)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a hcm hJ hW hA y hy c w
  haveI := hcm.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, hr]
  have hs : ∀ x, sigR w.Completion σ (sigR w.Completion σ x) = x := sigR_sigR hcm w.Completion
  obtain ⟨c0, hc⟩ := hA.cartan w
  rw [map_inv] at hc
  have hv : (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (y + c • GlobalTheory.EisMidHt.firstColumn X) i)) =
      (fun i => inclR (F := F) w.Completion (y i)) +
        inclR (F := F) w.Completion c • (fun i => inclR (F := F) w.Completion (X i 0)) := by
    funext i; simp [compInf_adVec, GlobalTheory.EisMidHt.firstColumn, map_add, map_mul]
  have hv1 : (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F y i)) = fun i => inclR (F := F) w.Completion (y i) := by
    funext i; exact compInf_adVec w y i
  have hv2 : (fun i => compInf F E w (GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) i)) =
      fun i => inclR (F := F) w.Completion (X i 0) := by
    funext i; exact compInf_adVec w _ i
  unfold GlobalTheory.EisMidHt.normInf
  simp only [hv, hv1, hv2, hmult, pow_one]
  set B : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E) := ((Formalism.UG.bc (compInf F E w) a)⁻¹ : GL _ _).1 with hB
  have hPu : (Formalism.UG.cT (sigR w.Completion σ) B * B) *ᵥ (fun i => inclR (F := F) w.Completion (X i 0)) =
      fun k => (JR w.Completion J *ᵥ fun j => inclR (F := F) w.Completion (Y j 0)) k * c0 0 := by
    funext k
    have := congrFun (congrFun hc k) 0
    rw [Matrix.mul_diagonal] at this
    simp only [JR] at this ⊢
    erw [Matrix.mul_apply (M := J.map _)] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h0 : hE σ J y (GlobalTheory.EisMidHt.firstColumn Y) = 0 := by rw [hE_swap hcm hJ, hy, map_zero]
  have hT : ∑ i, sigR w.Completion σ ((B *ᵥ fun i => inclR (F := F) w.Completion (y i)) i) *
      (B *ᵥ fun i => inclR (F := F) w.Completion (X i 0)) i = 0 := by
    rw [cross_eq, hPu]
    have : ∑ j, sigR w.Completion σ (inclR (F := F) w.Completion (y j)) *
        ((JR w.Completion J *ᵥ fun j => inclR (F := F) w.Completion (Y j 0)) j * c0 0) =
        inclR (F := F) w.Completion (hE σ J y (GlobalTheory.EisMidHt.firstColumn Y)) * c0 0 := by
      simp only [hE, Formalism.UG.hform, JR, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
        Finset.sum_mul, Finset.mul_sum, sigR_inclR, GlobalTheory.EisMidHt.firstColumn, AlgHom.coe_toRingHom]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this, h0, map_zero, zero_mul]
  obtain ⟨τ⟩ := nonempty_embOver F (E := E) w
  haveI : Nontrivial (w.Completion ⊗[F] E) :=
    (RingEquiv.ofBijective (infEmb τ) (infEmb_bijective hcm τ)).toEquiv.nontrivial
  have hsum : ∑ i, Algebra.norm w.Completion ((B *ᵥ ((fun i => inclR (F := F) w.Completion (y i)) +
        inclR (F := F) w.Completion c • (fun i => inclR (F := F) w.Completion (X i 0)))) i) =
      ∑ i, Algebra.norm w.Completion ((B *ᵥ fun i => inclR (F := F) w.Completion (y i)) i) +
        Algebra.norm w.Completion (inclR (F := F) w.Completion c) *
          ∑ i, Algebra.norm w.Completion ((B *ᵥ fun i => inclR (F := F) w.Completion (X i 0)) i) := by
    apply (algebraMap w.Completion (w.Completion ⊗[F] E)).injective
    simp only [map_add, map_mul, map_sum, GlobalTheory.Doubling.algebraMap_norm_eq hcm]
    exact sum_expand _ hs B _ _ _ hT
  rw [hsum]
  set φ := InfinitePlace.Completion.ringEquivRealOfIsReal hr
  have hn : ∀ x : w.Completion, ‖x‖ = |φ x| := fun x => by
    rw [← Real.norm_eq_abs]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hr).norm_map_of_map_zero
      (map_zero _) x).symm
  have hp : ∀ z : Fin n → w.Completion ⊗[F] E, 0 ≤ φ (∑ i, Algebra.norm w.Completion (z i)) := fun z => by
    rw [map_sum]; exact Finset.sum_nonneg fun i _ => (GlobalTheory.PoleFactor.norm_completion_tensor_pos hcm w hr _).1
  have hq := (GlobalTheory.PoleFactor.norm_completion_tensor_pos hcm w hr (inclR (F := F) w.Completion c)).1
  rw [hn, hn, hn, hn, map_add, map_mul, abs_of_nonneg (add_nonneg (hp _) (mul_nonneg hq (hp _))),
    abs_of_nonneg (hp _), abs_of_nonneg hq, abs_of_nonneg (hp _)]

end GlobalTheory.ArchOrth
