import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Chart.Assoc

theorem isEval_comp (p : ℕ) {O A B σ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] B) (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨c, hc⟩ := hN f hf
  exact ⟨φ c, by simp [hc, map_mul, map_pow, map_natCast]⟩

theorem constantCoeff_op {O : Type} [CommRing O] {d : ℕ} {τ : Type}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u v : Fin d → MvPowerSeries τ O) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (j : Fin d) : constantCoeff (op μ u v j) = 0 := by
  have h : ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    rintro (k | k) <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ j)

theorem dvd_pow_map (p : ℕ) {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (φ : A →ₐ[O] B) {a : A} (h : ∃ N : ℕ, (p : A) ∣ a ^ N) :
    ∃ N : ℕ, (p : B) ∣ φ a ^ N := by
  obtain ⟨N, c, hc⟩ := h
  exact ⟨N, φ c, by rw [← map_pow, hc, map_mul, map_natCast]⟩

end GlobalTheory.Chart.Assoc

namespace GlobalTheory.Chart.Assoc

theorem assoc_eval (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A]
    [IsAdicComplete (Ideal.span {(p : A ⊗[O] (A ⊗[O] A))}) (A ⊗[O] (A ⊗[O] A))] {d : ℕ}
    (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A)
    (E₃ : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] A ⊗[O] (A ⊗[O] A))
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (hx : ∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (h2 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂)
    (h3 : IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) E₃)
    (hc : ∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) :
    ∀ i, E₃ (op μ (op μ x1 x2) x3 i) = E₃ (op μ x1 (op μ x2 x3) i) := by
  let Φ₁ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Algebra.TensorProduct.includeLeft (S := O))
  let Φ₃ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) := Algebra.TensorProduct.includeRight
  let Φ₂ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    (Algebra.TensorProduct.assoc O O O A A A).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom O A) (AlgHom.id O A))
  let Φ₄ : A ⊗[O] A →ₐ[O] A ⊗[O] (A ⊗[O] A) :=
    Algebra.TensorProduct.map (AlgHom.id O A) (Bialgebra.comulAlgHom O A)
  have hnil : ∀ k, ∃ N : ℕ, (p : A ⊗[O] (A ⊗[O] A)) ∣ (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A ⊗[O] A))
      (Sum.elim (fun i => (1 : A) ⊗ₜ[O] (x i ⊗ₜ[O] (1 : A)))
        fun i => (1 : A) ⊗ₜ[O] ((1 : A) ⊗ₜ[O] x i))) k ^ N := by
    rintro (k | k | k)
    · exact dvd_pow_map p (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A ⊗[O] A)) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := A) (B := A))) (hx k)
    · exact dvd_pow_map p (Φ₃.comp (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A))) (hx k)
  have sub := ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ hnil).2 E₃ h3).1
  have c1 : ∀ j, constantCoeff (x1 (R := O) (d := d) j) = 0 := fun j => by simp [x1]
  have c2 : ∀ j, constantCoeff (x2 (R := O) (d := d) j) = 0 := fun j => by simp [x2]
  have c3 : ∀ j, constantCoeff (x3 (R := O) (d := d) j) = 0 := fun j => by simp [x3]
  have ce : ∀ {u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O},
      (∀ j, constantCoeff (u j) = 0) → (∀ j, constantCoeff (v j) = 0) →
      ∀ k, constantCoeff (Sum.elim u v k) = 0 := by
    intro u v hu hv k; rcases k with k | k <;> simp [hu, hv]
  have L1 : ∀ j, E₃ (op μ x1 x2 j) = Φ₁ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₁ h2
    have := sub _ (Sum.elim x1 x2) (Φ₁.comp E₂) (ce c1 c2) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x1, x2, h3.1, Φ₁, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  have L3 : ∀ j, E₃ (op μ x2 x3 j) = Φ₃ (Coalgebra.comul (R := O) (x j)) := by
    intro j
    have e := isEval_comp p Φ₃ h2
    have := sub _ (Sum.elim x2 x3) (Φ₃.comp E₂) (ce c2 c3) (by
      convert e using 2 with k
      rcases k with k | k <;> simp [x2, x3, h3.1, Φ₃, Algebra.TensorProduct.one_def]) (μ j)
    simp only [op, at2]
    rw [this, AlgHom.comp_apply, hc]
  intro i
  have LL : E₃ (op μ (op μ x1 x2) x3 i) = Φ₂ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₂ h2
    have := sub _ (Sum.elim (op μ x1 x2) x3) (Φ₂.comp E₂)
      (ce (constantCoeff_op μ hμ _ _ c1 c2) c3) (by
      convert e using 2 with k
      rcases k with k | k
      · simp only [Sum.elim_inl]
        rw [L1]
        have key : ∀ c : A ⊗[O] A, Φ₁ c = (Algebra.TensorProduct.assoc O O O A A A) (c ⊗ₜ[O] 1) := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => simp
          | tmul a b => simp [Φ₁, Algebra.TensorProduct.one_def]
          | add a b ha hb => rw [map_add, ha, hb, TensorProduct.add_tmul, map_add]
        rw [key]
        simp [Φ₂]
      · simp [x3, h3.1, Φ₂, Algebra.TensorProduct.one_def]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  have RR : E₃ (op μ x1 (op μ x2 x3) i) = Φ₄ (Coalgebra.comul (R := O) (x i)) := by
    have e := isEval_comp p Φ₄ h2
    have := sub _ (Sum.elim x1 (op μ x2 x3)) (Φ₄.comp E₂)
      (ce c1 (constantCoeff_op μ hμ _ _ c2 c3)) (by
      convert e using 2 with k
      rcases k with k | k
      · simp [x1, h3.1, Φ₄, Algebra.TensorProduct.one_def]
      · simp only [Sum.elim_inr]
        rw [L3]
        simp [Φ₃, Φ₄]) (μ i)
    simp only [op, at2] at this ⊢
    rw [this, AlgHom.comp_apply, hc]
  rw [LL, RR]
  have ka : ∀ w : (A ⊗[O] A) ⊗[O] A,
      (Algebra.TensorProduct.assoc O O O A A A) w = TensorProduct.assoc O A A A w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a a' => simp
      | add c c' hc hc' => rw [TensorProduct.add_tmul, map_add, hc, hc', map_add]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  have k2 : ∀ c : A ⊗[O] A, Φ₂ c = TensorProduct.assoc O A A A (LinearMap.rTensor A (Coalgebra.comul (R := O) (A := A)) c) := by
    intro c
    rw [← ka]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₂]
    | add a b ha hb => rw [map_add, ha, hb, map_add, map_add]
  have k4 : ∀ c : A ⊗[O] A, Φ₄ c = LinearMap.lTensor A (Coalgebra.comul (R := O) (A := A)) c := by
    intro c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Φ₄]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  rw [k2, k4, Coalgebra.coassoc_apply]

end GlobalTheory.Chart.Assoc
