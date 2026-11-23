import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2MatrixCoeffBoundedHolomorphicFormEqExtremalVecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFunOfTransvectionConstantTermsZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsActByScalarsHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantMultilinearOfMatrixCoeffEqUnitaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorAutomorphicDerivativesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantMultilinearMapsSmoothVectorsIntertwinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDerivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundForSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameBorelActsExtremalVectorByWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalityPreservedInClosureStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.BackForm

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem coe_update (y : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    (fun ρ => ((Function.update y τ w ρ : M.sm ρ) : M.H ρ)) = Function.update (fun ρ => (y ρ : M.H ρ)) τ (w : M.H τ) := by
  funext ρ
  by_cases h : ρ = τ
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem word_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    ∃ y', l.foldr (fun p f => Rder θ V p.1 p.2 f) (T y) = T y' := by
  induction l with
  | nil => exact ⟨y, rfl⟩
  | cons p l ih =>
    obtain ⟨y', h⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    exact ⟨_, by rw [List.foldr_cons, h]; exact hT y' p.1 p.2 hp ⟨_, hsm _ _ hp (y' p.1)⟩ rfl⟩

theorem rderC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Z : Mt V.rank) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = dRepC (gramAt D V τ) (M.rep τ) Z w ∧
      RderC θ V τ Z (T (Function.update y τ w)) = T (Function.update y τ w') := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨⟨_, hsm τ _ h1 w⟩ + Complex.I • ⟨_, hsm τ _ h2 w⟩, rfl, ?_⟩
  rw [T.map_update_add, T.map_update_smul, RderC,
    hT (Function.update y τ w) τ _ h1 ⟨_, hsm τ _ h1 w⟩ (by simp),
    hT (Function.update y τ w) τ _ h2 ⟨_, hsm τ _ h2 w⟩ (by simp), Function.update_idem, Function.update_idem]

theorem wordC_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (Zs : List (Mt V.rank)) (w : M.sm τ) :
    ∃ w' : M.sm τ, (w' : M.H τ) = (Zs.map (dRepC (gramAt D V τ) (M.rep τ))).foldr (fun f acc => f acc) (w : M.H τ) ∧
      (Zs.map (RderC θ V τ)).foldr (fun f acc => f acc) (T (Function.update y τ w)) = T (Function.update y τ w') := by
  induction Zs with
  | nil => exact ⟨w, rfl, rfl⟩
  | cons Z Zs ih =>
    obtain ⟨w', h1, h2⟩ := ih
    obtain ⟨w'', h3, h4⟩ := rderC_value T hsm hT y τ Z w'
    refine ⟨w'', ?_, ?_⟩
    · rw [List.map_cons, List.foldr_cons, ← h1, h3]
    · rw [List.map_cons, List.foldr_cons, h2, h4]

theorem gelf_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (y : M.Vec) (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) (w : M.sm τ)
    (hc : gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ)) :
    gelf θ V τ k (T (Function.update y τ w)) = c • T (Function.update y τ w) := by
  choose W h1 h2 using fun idx : Fin (k + 1) → Fin V.rank =>
    wordC_value T hsm hT y τ (List.ofFn fun a : Fin (k + 1) => (Matrix.single (idx a) (idx (a + 1)) 1 : Mt V.rank)) w
  simp only [List.map_ofFn] at h1 h2
  have e : ∑ idx, W idx = c • w := by
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_smul, ← hc, gelfRep]
    exact Finset.sum_congr rfl fun idx _ => h1 idx
  rw [← T.map_update_smul, ← e, T.map_update_sum, gelf]
  exact Finset.sum_congr rfl fun idx _ => h2 idx

theorem zfin_value (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w))
    (hc : ∀ τ k, ∃ c : ℂ, ∀ w : M.sm τ, gelfRep (gramAt D V τ) (M.rep τ) k (w : M.H τ) = c • (w : M.H τ))
    (y : M.Vec) :
    ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ T y ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ V τ k f ∈ W := by
  refine ⟨Submodule.span ℂ {T y}, inferInstance, Submodule.mem_span_singleton_self _, fun τ k f hf => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
  obtain ⟨c, hc⟩ := hc τ k
  have e : a • T y = T (Function.update y τ (a • y τ)) := by rw [T.map_update_smul, Function.update_eq_self]
  have := gelf_value T hsm hT y τ k c (a • y τ) (hc _)
  rw [← e] at this
  rw [this]
  exact Submodule.smul_mem _ _ hf

def lettersAt (τ : D.what₂.Tau) (l : List (D.what₂.Tau × Mt V.rank)) : List (Mt V.rank) :=
  (l.filter fun p => p.1 = τ).map Prod.snd

theorem lettersAt_mem {τ : D.what₂.Tau} {l : List (D.what₂.Tau × Mt V.rank)} (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) :
    ∀ X ∈ lettersAt τ l, X ∈ lieAt V τ := by
  intro X hX
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hX
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hp
  have h3 : p.1 = τ := by simpa using h2
  exact h3 ▸ hl p h1

theorem word_mem (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    {τ : D.what₂.Tau} (l : List (Mt V.rank)) (hl : ∀ X ∈ l, X ∈ lieAt V τ) (w : M.sm τ) :
    l.foldr (dRep (M.rep τ)) (w : M.H τ) ∈ M.sm τ := by
  induction l with
  | nil => exact w.2
  | cons X l ih => exact hsm τ X (hl X List.mem_cons_self) ⟨_, ih fun q hq => hl q (List.mem_cons_of_mem _ hq)⟩

theorem word_map {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (l : List (D.what₂.Tau × Mt V.rank)) (hl : ∀ p ∈ l, p.2 ∈ lieAt V p.1) (y : M.Vec) :
    l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ)) =
      Φ fun τ => (lettersAt τ l).foldr (dRep (M.rep τ)) (y τ : M.H τ) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [List.foldr_cons, ih hl']
    have := hΦ (fun τ => ⟨_, word_mem hsm _ (lettersAt_mem hl') (y τ)⟩) p.1 p.2 (hl p List.mem_cons_self)
    refine this.trans ?_
    congr 1
    funext τ
    by_cases h : τ = p.1
    · subst h; simp [lettersAt]
    · have h' : ¬ p.1 = τ := fun e => h e.symm
      simp [lettersAt, Function.update_of_ne h, List.filter_cons, h']

theorem sum_bound {α β : Type} (a b : α → β → ℝ) (hb : ∀ l w, 0 ≤ b l w) (L : List α)
    (h : ∀ l ∈ L, ∃ c, ∀ w, a l w ≤ c * b l w) :
    ∃ C, 0 ≤ C ∧ ∀ w, (L.map fun l => a l w).sum ≤ C * (L.map fun l => b l w).sum := by
  induction L with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons l L ih =>
    obtain ⟨C, hC, ih⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := h l List.mem_cons_self
    refine ⟨max c C, le_max_of_le_right hC, fun w => ?_⟩
    have h0 : 0 ≤ (L.map fun l => b l w).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
      exact hb q w)
    simp only [List.map_cons, List.sum_cons, mul_add]
    exact add_le_add ((hc w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hb l w)))
      ((ih w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) h0))

theorem cont_value {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (Φ : ContinuousMultilinearMap ℂ M.H K) (T : MMap M)
    (hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ)
    (hΦ : ∀ (v : M.Vec) τ, ∀ X ∈ lieAt V τ, dL2 θ V ρ (τ, X) (Φ fun τ => (v τ : M.H τ)) =
      Φ (Function.update (fun τ => (v τ : M.H τ)) τ (dRep (M.rep τ) X (v τ))))
    (L : List (List (D.what₂.Tau × Mt V.rank))) (hL : ∀ l ∈ L, ∀ p ∈ l, p.2 ∈ lieAt V p.1) (x : GA D V) (C : ℝ)
    (hC : ∀ y : M.Vec, ‖T y x‖ ≤ C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y τ : M.H τ))‖).sum)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := by
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ((LinearMap.proj x : (GA D V → ℂ) →ₗ[ℂ] ℂ) ∘ₗ T.toLinearMap v τ)
  have hℓ' : ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x := fun w => LinearMap.congr_fun hℓ w
  refine ⟨ℓ, ?_, hℓ'⟩
  obtain ⟨C', hC', hb⟩ := sum_bound
    (fun l (w : M.sm τ) => ‖l.foldr (dL2 θ V ρ) (Φ fun σ => ((Function.update v τ w σ : M.sm σ) : M.H σ))‖)
    (fun l (w : M.sm τ) => ‖(lettersAt τ l).foldr (dRep (M.rep τ)) (w : M.H τ)‖) (fun _ _ => norm_nonneg _) L (by
      intro l hl
      refine ⟨‖Φ.toContinuousLinearMap (fun σ => (lettersAt σ l).foldr (dRep (M.rep σ)) (v σ : M.H σ)) τ‖, fun w => ?_⟩
      refine le_trans (le_of_eq ?_) (ContinuousLinearMap.le_opNorm _ _)
      rw [word_map ρ Φ hsm hΦ l (hL l hl), ContinuousMultilinearMap.toContinuousLinearMap_apply]
      congr 2
      funext σ
      by_cases h : σ = τ
      · subst h; simp
      · simp [Function.update_of_ne h])
  refine ⟨L.map (lettersAt τ), |C| * C', ?_, fun w hw => ?_⟩
  · intro l hl
    obtain ⟨l', h', rfl⟩ := List.mem_map.1 hl
    exact lettersAt_mem (hL l' h')
  · have hw' : w ∈ M.sm τ := Submodule.subset_span hw
    have h1 := hℓ' ⟨w, hw'⟩
    have h2 := hb ⟨w, hw'⟩
    have h3 := hC (Function.update v τ ⟨w, hw'⟩)
    rw [List.map_map, mul_assoc]
    simp only at h1
    rw [h1]
    refine h3.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (List.sum_nonneg ?_)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    intro x hx
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _

theorem continuous_rTr (k : GA D V) {f : GA D V → ℂ} (hf : Continuous f) : Continuous (rTr V k f) := by
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact hf.comp (continuous_mul_const k)

section L2

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))}

theorem repr_add (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {F F' ψ ψ'} (h : Repr V μ 𝓕 F ψ) (h' : Repr V μ 𝓕 F' ψ') :
    Repr V μ 𝓕 (F + F') (ψ + ψ') := by
  simpa using (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F' ψ ψ' 1 h h'

theorem repr_smul (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) (a : ℂ) {F ψ} (h : Repr V μ 𝓕 F ψ) :
    Repr V μ 𝓕 (a • F) (a • ψ) := by
  have := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.2.2.2.1 F F ψ ψ (a - 1) h h
  rwa [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this

theorem eig_closure {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (ρ : GA D V →* (K →L[ℂ] K))
    (A : Set K) (k : GA D V) (c : ℂ) (hA : ∀ z ∈ A, ρ k z = c • z) {F : K}
    (hF : F ∈ closure (Submodule.span ℂ A : Set K)) : ρ k F = c • F := by
  have h1 : (Submodule.span ℂ A : Set K) ⊆ {z | ρ k z = c • z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hA x hx
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add, hx, hy, smul_add]
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [map_smul, hx, smul_comm]
  exact closure_minimal h1 (isClosed_eq (ρ k).continuous (continuous_const_smul c)) hF

theorem exists_map_abs {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ρ : GA D V →* (K →L[ℂ] K)) {v : M.Vec} (hθ : IsInfFam θ) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1)
    (hiso : ∀ g F, ‖ρ g F‖ = ‖F‖) (F₀ : K)
    (hco : ∀ u ∈ GinfC V, ⟪F₀, ρ u F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (archM V (θ τ) u) (v τ : M.H τ)⟫_ℂ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H K, (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set K)) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, ρ k F₀ = c • F₀ → ∀ y, ρ k (Φ y) = c • Φ y := by
  obtain ⟨L, hL1, hL2, -, -, -, hL3, -, hL4, hL5⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have h1 : (1 : D.what₂.Tau → Mt V.rank) ∈ UG (gramAt D V) := fun τ => by simp [Formalism.QuantumDeterminants.UH]
  have hone : L 1 = 1 := by
    have := hL2 1 h1 1 h1
    rw [mul_one] at this
    exact mul_eq_left.1 this.symm
  have a1 : ρ (L 1) = 1 := by rw [hone, map_one]
  have a2 : ∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), ρ (L (u * u')) = ρ (L u) * ρ (L u') :=
    fun u hu u' hu' => by rw [hL2 u hu u' hu', map_mul]
  have a3 : ∀ u ∈ UG (gramAt D V), ⟪F₀, ρ (L u) F₀⟫_ℂ =
      ((‖F₀‖ ^ 2 : ℝ) : ℂ) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ := fun u hu => by
    rw [hco (L u) (hL1 u hu).1]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [(hL1 u hu).2 τ]
  obtain ⟨Φ, e1, e2, e3⟩ := GlobalTheory.T.exists_equivariant_multilinear_of_matrixCoeff_eq_unitaryProduct V.rank D.what₂.Tau (gramAt D V) M.H M.rep K
    (fun u => ρ (L u)) (fun τ => (v τ : M.H τ)) F₀
    (fun τ => ⟨(hL5 τ).2, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1, (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.2.1, hv τ⟩)
    a1 a2 (fun u _ y => hiso _ y) a3
  refine ⟨Φ, e1, fun τ g hg y => ?_, fun y => ?_, fun k hk c h0 y => ?_⟩
  · rw [hL3 τ g hg]; exact e2 τ g hg y
  · refine closure_mono (Submodule.span_mono ?_) (e3 y)
    rintro z ⟨u, -, hz⟩
    exact ⟨_, hz⟩
  · refine eig_closure ρ _ k c ?_ (e3 y)
    rintro z ⟨u, hu, hz⟩
    have : ρ k (ρ (L u) F₀) = ρ (L u) (ρ k F₀) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, hL4 k hk _ (hL1 u hu).1, map_mul, ContinuousLinearMap.mul_apply]
    rw [hz, this, h0, map_smul]

theorem eig_class (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {φ : GA D V → ℂ}
    {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) (k : GA D V) (c : ℂ) (hc : ∀ g, φ (g * k) = c * φ g) :
    ρ k F₀ = c • F₀ := by
  have hr := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h := hr.2.2.2.1 F₀ φ k hF
  have e : rTr V k φ = c • φ := funext hc
  rw [e] at h
  have h3 := hr.2.2.1 _ _ _ h (repr_smul hp hρ c hF)
  exact h3

theorem exists_map {w : D.what₂.Tau → Fin V.rank → ℤ} {v : M.Vec} (hθ : IsInfFam θ) (hs : HolShape M) (hw : WtIs M w)
    (hv : IsExtVec M v) (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ) {J : Set (GA D V)} {χ φ : GA D V → ℂ}
    (hφ : HolForm θ M w J χ φ) {F₀ : Lp ℂ 2 (nuQ V μ 𝓕)} (hF : Repr V μ 𝓕 F₀ φ) :
    ∃ Φ : ContinuousMultilinearMap ℂ M.H (Lp ℂ 2 (nuQ V μ 𝓕)), (Φ fun τ => (v τ : M.H τ)) = F₀ ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y,
        Φ (Function.update y τ (M.rep τ g (y τ))) = ρ (atTau θ V τ g) (Φ y)) ∧
      (∀ y, Φ y ∈ closure (Submodule.span ℂ {z | ∃ u : GA D V, z = ρ u F₀} : Set (Lp ℂ 2 (nuQ V μ 𝓕)))) ∧
      ∀ k ∈ GfC V, ∀ c : ℂ, (∀ g, φ (g * k) = c * φ g) → ∀ y, ρ k (Φ y) = c • Φ y := by
  have h1 := GlobalTheory.T.inner_rho_eq_normSq_mul_prod_of_holForm D θ V S M w v hθ hs hw hv μ 𝓕 ρ hp hρ J χ φ F₀ hφ hF
  have h2 := exists_map_abs (K := Lp ℂ 2 (nuQ V μ 𝓕)) (M := M) (v := v) ρ hθ (fun τ => (hv τ).1) hρ.iso F₀
  have h3 := h2 h1
  refine h3.imp fun Φ h => ⟨h.1, h.2.1, h.2.2.1, fun k hk c hc => ?_⟩
  have h4 := eig_class hp hρ hF k c hc
  exact h.2.2.2 k hk c h4

end L2

set_option maxHeartbeats 1000000 in

theorem exists_multMap : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → (∃ μ 𝓕, FinPair V μ 𝓕) → ∀ (J : Set (GA D V)) (χ φ : GA D V → ℂ), J ⊆ (GfC V : Set (GA D V)) → HolForm θ M w J χ φ → ZCusp V φ → ∃ T : MMap M, IsMultMap θ M J χ T ∧ T v = φ := by
  rintro D θ V S M w v hθ hs hw hv ⟨μ, 𝓕, hp⟩ J χ φ hJ hφ hZ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.regular_representation_of_finite_pair D V μ 𝓕 hp
  obtain ⟨r1, r2, -, r4, -, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  obtain ⟨F₀, hF⟩ := r1 φ hφ.aut.cont hφ.aut.left hφ.bdd
  obtain ⟨Φ, e1, e2, e3, e4⟩ := exists_map hθ hs hw hv hp hρ hφ hF
  obtain ⟨U, hU, hUφ⟩ := hφ.aut.level
  have hfix : ∀ y, ∀ k ∈ U, k ∈ GfC V → ρ k (Φ y) = Φ y := fun y k hk hk' => by
    simpa using e4 k hk' 1 (fun g => by rw [hUφ k hk hk', one_mul]) y
  have hsmM := GlobalTheory.T.equivariantMultilinear_maps_smoothVectors_intertwines D θ V hθ S M _ ρ Φ e2
  choose ψ p1 p2 p3 p4 using fun y : M.Vec =>
    GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU (Φ fun τ => (y τ : M.H τ)) (hsmM y).1 (hfix _)
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).1
  have hH : ∀ τ, (gramAt D V τ).IsHermitian := GlobalTheory.SmoothAutCheck.gramAt_herm V
  have hdet : ∀ τ, (gramAt D V τ).det ≠ 0 := fun τ => (GlobalTheory.SmoothAutCheck.gramAt_unit V τ).ne_zero
  have hsv := fun τ => GlobalTheory.T.smoothVectors_subspace_stable_sobolevForm_deriv V.rank (gramAt D V τ) (M.H τ) (M.rep τ) (hH τ) (hdet τ) (GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ).2.1
  have hsm : ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, dRep (M.rep τ) X (w : M.H τ) ∈ M.sm τ := fun τ X hX w =>
    Submodule.subset_span (((hsv τ).2 w ((hsv τ).1 w w.2)).2.1 X hX).1
  have uniq : ∀ (y : M.Vec) f, Continuous f → Repr V μ 𝓕 (Φ fun τ => (y τ : M.H τ)) f → ψ y = f :=
    fun y f hf h => r2 _ _ _ (p2 y).cont hf (p1 y) h
  let T : MMap M := MultilinearMap.mk' ψ
    (fun y τ a b => by
      refine uniq _ _ ((p2 _).cont.add (p2 _).cont) ?_
      have := repr_add hp hρ (p1 (Function.update y τ a)) (p1 (Function.update y τ b))
      rw [coe_update, coe_update, ← Φ.map_update_add] at this
      rw [coe_update]
      exact this)
    (fun y τ c a => by
      refine uniq _ _ ((p2 _).cont.const_smul c) ?_
      have := repr_smul hp hρ c (p1 (Function.update y τ a))
      rw [coe_update, ← Φ.map_update_smul] at this
      rw [coe_update]
      exact this)
  have hTψ : ∀ y, T y = ψ y := fun _ => rfl
  have hT : ∀ (y : M.Vec) τ, ∀ X ∈ lieAt V τ, ∀ w : M.sm τ, (w : M.H τ) = dRep (M.rep τ) X (y τ) →
      Rder θ V τ X (T y) = T (Function.update y τ w) := by
    intro y τ X hX w hw
    obtain ⟨q1, q2⟩ := p4 y [(τ, X)] (by simpa using hX)
    simp only [List.foldr_cons, List.foldr_nil] at q1 q2
    refine (uniq _ _ q1 ?_).symm
    rw [coe_update, hw, ← (hsmM y).2 τ X hX]
    exact q2
  obtain ⟨N, L, hL, hgr⟩ := GlobalTheory.T.sobolev_bound_for_smooth_vectors D θ V hθ μ 𝓕 ρ hp hρ U hU
  refine ⟨T, ⟨fun y => ⟨p2 y, p3 y, ?_, N, fun l hl x => ?_⟩, fun y => ?_, fun y k hk g => ?_, fun τ g hg y z hz => ?_,
    fun τ y x => ?_⟩, uniq v φ hφ.aut.cont (e1 ▸ hF)⟩
  · refine zfin_value T hsm hT (fun τ k => ?_) y
    obtain ⟨-, m1, m2, m3⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
    obtain ⟨k1, k2⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hs hw hv τ
    obtain ⟨c, hc⟩ := GlobalTheory.T.gelfand_invariants_act_by_scalars_highest_weight V.rank (gramAt D V τ) _ _ (w τ) (M.H τ) (M.rep τ) (m3 hs).1 m1 m2 (v τ)
      (by rw [← norm_ne_zero_iff, (hv τ).1]; exact one_ne_zero) k1 k2 k
    exact ⟨c, fun z => hc z ((hsv τ).1 z z.2)⟩
  · obtain ⟨y', hy'⟩ := word_value T hsm hT l hl y
    obtain ⟨C, hC⟩ := hgr x
    refine ⟨C * (L.map fun l => ‖l.foldr (dL2 θ V ρ) (Φ fun τ => (y' τ : M.H τ))‖).sum, fun g hg => ?_⟩
    rw [hy', mul_right_comm]
    exact hC _ _ (hsmM y').1 (hfix _) (p2 y').cont (p1 y') g hg
  · exact GlobalTheory.T.isCuspFun_of_transvection_constantTerms_zero D θ V hθ _ (p2 y)
      (GlobalTheory.T.cuspidality_preserved_in_closure D θ V hθ μ 𝓕 ρ hp hρ φ (ψ y) F₀ _ hφ.aut hZ hF (p2 y) (p1 y) (e3 _))
  · have h1 := r4 _ _ k (p1 y)
    rw [e4 k (hJ hk) (χ k) (hφ.lev k hk)] at h1
    have h2 := r2 _ _ _ (continuous_rTr k (p2 y).cont) ((p2 y).cont.const_smul (χ k)) h1
      (repr_smul hp hρ (χ k) (p1 y))
    exact congrFun h2 g
  · refine uniq _ _ (continuous_rTr (atTau θ V τ g) (p2 y).cont) ?_
    rw [coe_update, hz, e2 τ g hg]
    exact r4 _ _ _ (p1 y)
  · obtain ⟨C, hC⟩ := hgr x
    refine cont_value ρ Φ T hsm (fun y => (hsmM y).2) L hL x (C * normInf θ V 1 ^ N) (fun y => ?_) τ y
    have := hC _ _ (hsmM y).1 (hfix _) (p2 y).cont (p1 y) 1 (one_mem _)
    rwa [mul_one] at this

end GlobalTheory.BackForm
