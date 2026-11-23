import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbSInjective

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

def lawX {ι P : Type} (BX : P → (P → ℂ) → (P → ℂ) → ℂ) (γ x : ι → P → ℂ) : ι → P → ℂ :=
  fun v p => γ v p + x v p + BX p (γ v) (x v)

theorem pi_measure_eq_prod_absNorm_mul_sqrt_discr (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by
  have hsf : SigmaFinite (ENNReal.ofReal c • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (c.toNNReal • (volume : Measure ℂ)))
  let sw : (ι → P → ℂ) → (P → ι → ℂ) := fun x p v => x v p
  let usw : (P → ι → ℂ) → (ι → P → ℂ) := fun y v p => y p v
  have h1 : ∀ x, usw (sw x) = x := fun x => rfl
  have h2 : ∀ y, sw (usw y) = y := fun y => rfl
  have hsw : MeasurePreserving sw _ _ := swap_mp (ι := ι) (P := P) (ENNReal.ofReal c • (volume : Measure ℂ))
  have husw : Measurable usw :=
    measurable_pi_lambda _ fun v => measurable_pi_lambda _ fun p =>
      (measurable_pi_apply v).comp (measurable_pi_apply p)
  let B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ) := fun p y y' v => BX p (fun q => y q v) (fun q => y' q v)
  let τT : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ) := fun p y => τ p (usw y)
  have hlaw : ∀ γ x, mlaw B (sw γ) (sw x) = sw (lawX BX γ x) := fun γ x => rfl
  have hmemT : ∀ γ : ι → P → ℂ, (∀ p, sw γ p - τT p (sw γ) ∈ (Λ p).map (embS φ (s p))) ↔
      (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) := fun γ => Iff.rfl
  have hpre : Kset = sw ⁻¹' (usw ⁻¹' Kset) := by ext x; simp [h1]
  have hKT : MeasurableSet (usw ⁻¹' Kset) := husw hK
  rw [hpre, hsw.measure_preimage hKT.nullMeasurableSet]
  refine covol_oneT K ι φ σ hφ P h B ?_ ?_ ?_ c hc I Λ hΛ k hk hk0 s hs τT ?_ ?_ (usw ⁻¹' Kset) hKT ?_
  · intro p
    refine measurable_pi_lambda _ fun v => ?_
    have hf : Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => ((fun q => z.1 q v), (fun q => z.2 q v))) :=
      (measurable_pi_lambda _ fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_fst)).prodMk
        (measurable_pi_lambda _ fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_snd))
    exact (hBm p).comp hf
  · intro p x x' y y' hxy
    funext v
    exact hBd p _ _ _ _ fun q hq => ⟨congrFun (hxy q hq).1 v, congrFun (hxy q hq).2 v⟩
  · intro p x
    funext v
    exact hB0 p _
  · intro p x x' hxx
    exact hτ p _ _ fun q hq v => congrFun (hxx q hq) v
  · intro γT hγT
    obtain ⟨γ', hγ', hinv'⟩ := hinv (usw γT) ((hmemT (usw γT)).1 (by rw [h2]; exact hγT))
    refine ⟨sw γ', (hmemT γ').2 hγ', fun g => ⟨?_, ?_⟩⟩
    · have := (hinv' (usw g)).1
      calc mlaw B (sw γ') (mlaw B γT g) = mlaw B (sw γ') (mlaw B (sw (usw γT)) (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX γ' (lawX BX (usw γT) (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
    · have := (hinv' (usw g)).2
      calc mlaw B γT (mlaw B (sw γ') g) = mlaw B (sw (usw γT)) (mlaw B (sw γ') (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX (usw γT) (lawX BX γ' (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
  · intro g
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (usw g)
    refine ⟨sw γ, ⟨(hmemT γ).2 hγΓ, ?_⟩, ?_⟩
    · show usw (mlaw B (sw γ) g) ∈ Kset
      rw [show g = sw (usw g) from (h2 g).symm, hlaw, h1]; exact hγK
    · rintro γT ⟨hΓT, hKT'⟩
      have e := hγu (usw γT) ⟨(hmemT (usw γT)).1 (by rw [h2]; exact hΓT), by
        have : usw (mlaw B γT g) ∈ Kset := hKT'
        rw [show γT = sw (usw γT) from (h2 γT).symm, show g = sw (usw g) from (h2 g).symm, hlaw, h1] at this
        exact this⟩
      rw [← e, h2]

theorem covol_one_eq_one (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (hconst : ∏ p, (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) = 1)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset = 1 := by
  rw [pi_measure_eq_prod_absNorm_mul_sqrt_discr K ι φ σ hφ P h BX hBm hBd hB0 c hc I Λ hΛ k hk hk0 s hs τ hτ hinv Kset hK hKd,
    ← ENNReal.ofReal_prod_of_nonneg, hconst, ENNReal.ofReal_one]
  intro p _
  have hN := FractionalIdeal.absNorm_nonneg (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  have hN' : (0 : ℝ) ≤ (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) := by
    exact_mod_cast hN
  positivity

end Formalism.L2.SG.NGCut.SplitEmbedding
