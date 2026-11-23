import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare.SymplVal

theorem trace_field {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨a, ha⟩ := hf (e + σ e) (by rw [map_add, hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h2, map_add, h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

theorem trace_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h2 σ hσ hf, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

theorem trace_AE (D : D7) (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z :=
  trace_tensor D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he) _ z

theorem map_sum4 {A : Type} [CommRing A] (φ : A →+* ℂ) (c : A →+* A) (hc : ∀ a, φ (c a) = starRingEnd ℂ (φ a))
    {m n : ℕ} (x y : Fin m → Fin n → A) (P Q : Fin m → Fin n → Fin m → Fin n → A) :
    φ (∑ i, ∑ j, ∑ k, ∑ l, c (x i j) * P i j k l * Q i j k l * y k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (φ (x i j)) * φ (P i j k l) * φ (Q i j k l) * φ (y k l) := by
  simp only [map_sum, map_mul, hc]

theorem comp_hHom {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W) :
    θ τ (infPart D (hHom V W x y)) = hC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  unfold hHom hC
  split_ifs
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram k i)) (fun i j k l => incA D (W.gram j l))).trans ?_
    simp only [hi]
    rfl
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram i k)) (fun i j k l => incA D (W.gram l j))).trans ?_
    simp only [hi]
    rfl

theorem valTau_sympl : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W),
    valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  intro D θ hθ V W τ x y
  unfold valTau sympl symplC
  rw [trace_AE, RingHom.map_add, RingHom.map_add, comp_cA hθ, RingHom.map_mul, RingHom.map_mul, comp_incA hθ,
    comp_hHom hθ, Complex.add_re, Complex.conj_re, two_mul]

end GlobalTheory.FockCompare.SymplVal
