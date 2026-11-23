import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCastStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveEvalTmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffEqZeroOfEvalEqComulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartGroupLawEvalRightUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSwapEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AssocEvalStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartEx

theorem isEval_comp {p : ℕ} {O A A' σ : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A]
    [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (φ : A →ₐ[O] A')
    (h : IsEval p x E) : IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  obtain ⟨a, ha⟩ := hN f hf
  exact ⟨φ a, by rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]⟩

theorem nil_map {p : ℕ} {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {a : A}
    (h : ∃ N : ℕ, (p : A) ∣ a ^ N) : ∃ N : ℕ, (p : A') ∣ φ a ^ N := by
  obtain ⟨N, b, hb⟩ := h
  exact ⟨N, φ b, by rw [← map_pow, hb, map_mul, map_natCast]⟩

theorem eq_zero_of_dvd {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {c : O} (h : ∀ m : ℕ, (p : O) ^ m ∣ c) : c = 0 := by
  refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) c fun m => ?_
  obtain ⟨b, hb⟩ := h m
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨b, hb⟩

theorem eq_zero_of_ker {p : ℕ} {O σ : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
    {A : ℕ → Type} [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)]
    (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hker : ∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f)
    {f : MvPowerSeries σ O} (hf : ∀ n, E n f = 0) : f = 0 := by
  ext α
  rw [map_zero]
  refine eq_zero_of_dvd (p := p) fun m => ?_
  obtain ⟨n, hn⟩ := hker m (α.degree + 1)
  exact hn f (hf n) α (Nat.lt_succ_self _)

theorem chart_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ d : ℕ, Nonempty (QLog.Chart G d) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, ev, hnil, hev, hres, haug, hsurj, hker⟩ := GlobalTheory.T.exists_coordinates_of_isConnected p C v O hv G hG
  have hc2 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hc3 : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] (G.A n ⊗[O] G.A n))})
      (G.A n ⊗[O] (G.A n ⊗[O] G.A n)) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have hcA : ∀ n, IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := fun n => GlobalTheory.T.isAdicComplete_span_natCast_of_finite_projective' p O _
  have nil2 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) j ^ N := by
    rintro n (i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
    · simpa using nil_map (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n).toRingHom (hnil n i)
  have nil3 : ∀ n, ∀ j, ∃ N : ℕ, (p : G.A n ⊗[O] (G.A n ⊗[O] G.A n)) ∣
      (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) j ^ N := by
    rintro n (i | i | i)
    · simpa using nil_map (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
    · simpa using nil_map ((Algebra.TensorProduct.includeRight : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n)).comp (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)).toRingHom (hnil n i)
  have hE2 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n ⊗[O] G.A n,
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) fun i => (1 : G.A n) ⊗ₜ[O] x n i) E := by
    intro n
    haveI := hc2 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.exists
  choose E₂ hE₂ using hE2
  have hE3 : ∀ n, ∃ E : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) O →ₐ[O] G.A n ⊗[O] (G.A n ⊗[O] G.A n),
      IsEval p (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) E := by
    intro n
    haveI := hc3 n
    exact (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil3 n)).1.exists
  choose E₃ hE₃ using hE3
  have hsurj2 : ∀ n, Function.Surjective (E₂ n) := fun n => by
    haveI := hc2 n
    exact GlobalTheory.T.surjective_isEval_tmul_of_surjective p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n)
  have hker2 : ∀ m N : ℕ, ∃ n, ∀ f, E₂ n f = 0 → ∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn⟩
  have hker3 : ∀ m N : ℕ, ∃ n, ∀ f, E₃ n f = 0 → ∀ α : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
    intro m N
    obtain ⟨n, hn⟩ := hker m N
    have hn2 := GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) (x n) (ev n) (ev n) (E₂ n) m N (hev n) (hev n) (hE₂ n) (hsurj n) (hsurj n) hn hn
    have hpt : (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) fun j => (1 : G.A n) ⊗ₜ[O] (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] x n i) j)) = (Sum.elim (fun i => x n i ⊗ₜ[O] (1 : G.A n ⊗[O] G.A n)) (Sum.elim (fun i => (1 : G.A n) ⊗ₜ[O] (x n i ⊗ₜ[O] (1 : G.A n))) fun i => (1 : G.A n) ⊗ₜ[O] ((1 : G.A n) ⊗ₜ[O] x n i))) := by
      funext j
      rcases j with j | j | j <;> rfl
    have hE3' := hE₃ n
    rw [← hpt] at hE3'
    exact ⟨n, GlobalTheory.T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O _ _ _ _ (x n) _ (ev n) (E₂ n) (E₃ n) m N (hev n) (hE₂ n) hE3' (hsurj n) (hsurj2 n) hn hn2⟩
  have hstep : ∀ i n f, E₂ (n + 1) f = Coalgebra.comul (R := O) (x (n + 1) i) →
      E₂ n f = Coalgebra.comul (R := O) (x n i) := by
    intro i n f hf
    let ρ : G.A (n + 1) ⊗[O] G.A (n + 1) →ₐ[O] G.A n ⊗[O] G.A n :=
      Algebra.TensorProduct.map (AlgHomClass.toAlgHom (G.res n)) (AlgHomClass.toAlgHom (G.res n))
    have hρ : ρ.comp (E₂ (n + 1)) = E₂ n := by
      haveI := hc2 n
      refine (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O _ _ _ (nil2 n)).1.unique ?_ (hE₂ n)
      have h1 := isEval_comp ρ (hE₂ (n + 1))
      convert h1 using 1
      funext j
      rcases j with j | j <;> simp [ρ, hres]
    rw [← hρ, AlgHom.comp_apply, hf]
    exact (CoalgHomClass.map_comp_comul_apply (G.res n) (x (n + 1) i)).trans (by rw [hres])
  have hμ : ∀ i, ∃ g, ∀ n, E₂ n g = Coalgebra.comul (R := O) (x n i) := by
    intro i
    exact GlobalTheory.T.exists_series_of_compatible' p O (Fin d ⊕ Fin d) (fun n => G.A n ⊗[O] G.A n) (fun n => (hc2 n).toIsHausdorff) _ E₂
      (fun n => Coalgebra.comul (R := O) (x n i)) hE₂ (fun n => hsurj2 n _) (hstep i) hker2
  choose μ hμ using hμ
  have hconst : ∀ i, constantCoeff (μ i) = 0 :=
    GlobalTheory.T.constantCoeff_eq_zero_of_eval_eq_comul' p O (G.A 0) (x 0) (E₂ 0) μ (haug 0) (hE₂ 0) (fun i => hμ i 0)
  refine ⟨d, ⟨⟨x, ev, E₂, μ, hnil, hev, hE₂, hres, haug, hsurj, hker, ?_, fun n i => hμ i n⟩⟩⟩
  refine ⟨hconst, ?_, fun i => ?_, ?_⟩
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) ev hker fun n => ?_)
    haveI := hcA n
    rw [map_sub, GlobalTheory.T.formalChart_groupLaw_eval_right_unit p O (G.A n) (x n) (ev n) (E₂ n) μ (hnil n) (haug n) (hev n) (hE₂ n) (fun i => hμ i n) i,
      (hev n).1 i, sub_self]
  · refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₂ hker2 fun n => ?_)
    haveI := hc2 n
    rw [map_sub, GlobalTheory.T.eval_swap_eq' p O (G.A n) (x n) (E₂ n) μ (hnil n) (hE₂ n) (fun i => hμ i n) i, sub_self]
  · funext i
    refine sub_eq_zero.1 (eq_zero_of_ker (p := p) E₃ hker3 fun n => ?_)
    haveI := hc3 n
    rw [map_sub, GlobalTheory.T.isEval_comul_assoc_of_isEval p O (G.A n) (x n) (E₂ n) (E₃ n) μ (hnil n) hconst (hE₂ n) (hE₃ n) (fun i => hμ i n) i, sub_self]

end GlobalTheory.ChartEx
