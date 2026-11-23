import Mathlib
open ValuativeRel MeasureTheory Matrix Filter Topology

namespace GlobalTheory.CompanionTheory.GLSmall

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def small (ϖ : k) (n l : ℕ) : Set (GL (Fin n) k) :=
  {g | (∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)
        ≤ valuation k ϖ ^ l) ∧
    ∀ i j, valuation k (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j
        - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ϖ ^ l}

theorem small_antitone {ϖ : k} (h : valuation k ϖ < 1) (n : ℕ) : Antitone (small ϖ n) :=
  fun _ _ hab _ hg => ⟨fun i j => (hg.1 i j).trans (pow_le_pow_right_of_le_one' h.le hab),
    fun i j => (hg.2 i j).trans (pow_le_pow_right_of_le_one' h.le hab)⟩

theorem tendsto_zero_of_le_pow {ϖ : k} (h : valuation k ϖ < 1) {α : Type} {s : ℕ → Set α} (f : α → k)
    (hf : ∀ l, ∀ a ∈ s l, valuation k (f a) ≤ valuation k ϖ ^ l) :
    Tendsto f (⨅ l, 𝓟 (s l)) (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨l, hl⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  refine mem_iInf_of_mem l (mem_principal.2 fun a ha => ?_)
  exact lt_of_le_of_lt (hf l a ha) hl

theorem tendsto_one_of_le_pow {ϖ : k} (h : valuation k ϖ < 1) {n : ℕ} {α : Type} {s : ℕ → Set α}
    (f : α → Matrix (Fin n) (Fin n) k)
    (hf : ∀ l, ∀ a ∈ s l, ∀ i j,
      valuation k (f a i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ϖ ^ l) :
    Tendsto f (⨅ l, 𝓟 (s l)) (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h0 := (tendsto_zero_of_le_pow h
    (fun a => f a i j - (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun l a ha => hf l a ha i j)).add_const ((1 : Matrix (Fin n) (Fin n) k) i j)
  simpa using h0

theorem exists_congruence_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), IsOpen U →
    (1 : GL (Fin n) k) ∈ U → ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ g : GL (Fin n) k,
    (∀ i j, ∃ μ ∈ 𝒪[k], (g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j = ϖ ^ l * μ) →
    (∀ i j, ∃ μ ∈ 𝒪[k], ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j = ϖ ^ l * μ) →
    g ∈ U := by
  intro k _ _ _ _ n U hU h1 ϖ hϖ
  have ha : Tendsto (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k))
      (⨅ l, 𝓟 (small ϖ n l)) (𝓝 1) :=
    tendsto_one_of_le_pow hϖ _ fun l _ ha => ha.1
  have hb : Tendsto (fun g : GL (Fin n) k => ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
      (⨅ l, 𝓟 (small ϖ n l)) (𝓝 1) :=
    tendsto_one_of_le_pow hϖ _ fun l _ ha => ha.2
  have ht : Tendsto (id : GL (Fin n) k → GL (Fin n) k) (⨅ l, 𝓟 (small ϖ n l)) (𝓝 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have hc := ha.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hb)
    rw [map_one]
    exact hc
  have hU' : U ∈ ⨅ l, 𝓟 (small ϖ n l) := ht (hU.mem_nhds h1)
  have hd : Directed (· ≥ ·) fun l => 𝓟 (small ϖ n l) :=
    (monotone_principal.comp_antitone (small_antitone hϖ n)).directed_ge
  obtain ⟨l, hl⟩ := (mem_iInf_of_directed hd U).1 hU'
  refine ⟨l, fun g hg hg' => mem_principal.1 hl ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · obtain ⟨μ, hμ, e⟩ := hg i j
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 hμ)
  · obtain ⟨μ, hμ, e⟩ := hg' i j
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 hμ)

end GlobalTheory.CompanionTheory.GLSmall
