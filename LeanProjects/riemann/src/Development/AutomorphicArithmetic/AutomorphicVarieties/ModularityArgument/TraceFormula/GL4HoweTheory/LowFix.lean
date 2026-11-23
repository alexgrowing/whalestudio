import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

open Topology Filter in
private theorem lowFix_emb (E : Type) [Field E] [TopologicalSpace E] [IsTopologicalDivisionRing E] (n : ℕ) :
    IsEmbedding (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E) := by
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix (Fin n) (Fin n) E => A⁻¹) ?_ ?_
  · intro A hA
    refine (continuousAt_matrix_inv A ?_).continuousWithinAt
    have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  · intro u
    exact (Matrix.coe_units_inv u).symm

open Topology Filter in
private theorem lowFix_ball (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (γ : ValueGroupWithZero E) (hγ : γ < 1) (W : Set E) (hW : W ∈ nhds (0 : E)) :
    ∃ m : ℕ, ∀ x : E, valuation E x ≤ γ ^ m → x ∈ W := by
  obtain ⟨δ, hδ⟩ := (IsValuativeTopology.mem_nhds_zero_iff W).1 hW
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hγ δ
  exact ⟨m, fun x hx => hδ (lt_of_le_of_lt hx hm)⟩

open Topology Filter in
theorem UpperTheory.V.Z.Tf.L4.lowFix :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (d : ℤ) (U : Set (GL (Fin n) E)), U ∈ nhds (1 : GL (Fin n) E) →
      ∃ a₀ : ℤ, ∀ a ≥ a₀, ∀ b ∈ howeSet n ϖ a (2 * a - d), (∀ i j : Fin n, i < j → (b : Matrix (Fin n) (Fin n) E) i j = 0) → b ∈ U := by
  intro E _ _ _ _ n ϖ hϖ d U hU
  have hlt : valuation E (ϖ : E) < 1 := hϖ ▸ uniformizer_lt_one
  have hpos : 0 < valuation E (ϖ : E) := zero_lt_iff.2 (by simp)
  rw [(lowFix_emb E n).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  have hc : Continuous (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) :=
    Continuous.add (f := fun A : Fin n → Fin n → E => (Matrix.of A : Matrix (Fin n) (Fin n) E)) continuous_id continuous_const
  have h0 : (fun A : Fin n → Fin n → E => (Matrix.of A + 1 : Matrix (Fin n) (Fin n) E)) ⁻¹' T ∈ nhds (0 : Fin n → Fin n → E) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hT
  have key : ∃ m : ℕ, ∀ A : Fin n → Fin n → E, (∀ i j, valuation E (A i j) ≤ valuation E (ϖ : E) ^ m) →
      Matrix.of A + 1 ∈ T := by
    rw [nhds_pi, Filter.mem_pi'] at h0
    obtain ⟨I, t, ht, htI⟩ := h0
    have h1 : ∀ i, ∃ s : Fin n → Set E, (∀ j, s j ∈ nhds (0 : E)) ∧ Set.pi Set.univ s ⊆ t i := by
      intro i
      have := ht i
      rw [nhds_pi, Filter.mem_pi'] at this
      obtain ⟨J, s, hs, hsJ⟩ := this
      exact ⟨s, hs, fun x hx => hsJ fun j _ => hx j (Set.mem_univ _)⟩
    choose s hs hst using h1
    have hW : (⋂ i, ⋂ j, s i j) ∈ nhds (0 : E) :=
      Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => hs i j
    obtain ⟨m, hm⟩ := lowFix_ball E _ hlt _ hW
    refine ⟨m, fun A hA => htI fun i _ => hst i fun j _ => ?_⟩
    have := hm _ (hA i j)
    simp only [Set.mem_iInter] at this
    exact this i j
  obtain ⟨m, hm⟩ := key
  refine ⟨max (m : ℤ) |d|, fun a ha b hb hlow => hTU ?_⟩
  have ham : (m : ℤ) ≤ a := le_trans (le_max_left _ _) ha
  have had : |d| ≤ a := le_trans (le_max_right _ _) ha
  have hc0 : 0 ≤ 2 * a - d := by
    have := le_abs_self d
    have := abs_nonneg d
    omega
  have := hm (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) (by
    intro i j
    rcases lt_or_ge i j with hij | hij
    · simp [hlow i j hij, Matrix.one_apply_ne hij.ne]
    · refine le_trans (hb i j) ?_
      rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← zpow_natCast]
      refine zpow_le_zpow_right_of_le_one₀ hpos hlt.le ?_
      have hji : ((j : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast hij
      have := mul_nonneg hc0 (sub_nonneg.2 hji)
      omega)
  have e : (Matrix.of (fun i j => (b : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) + 1 : Matrix (Fin n) (Fin n) E) = (b : Matrix (Fin n) (Fin n) E) := by
    ext i j
    simp
  rw [e] at this
  exact this
