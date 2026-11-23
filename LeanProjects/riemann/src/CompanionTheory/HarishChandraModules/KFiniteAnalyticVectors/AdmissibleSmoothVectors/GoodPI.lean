import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly

open MeasureTheory Matrix

noncomputable section

namespace CompanionTheory.D.gk.admitted

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_common_eigenvector (h : ι → ℕ) (hinj : Function.Injective h) (W : Submodule ℂ (ι → ℂ))
    (hW : W ≠ ⊥) : ∃ w₀ ∈ W, w₀ ≠ 0 ∧ ∀ A : Matrix ι ι ℂ, A.BlockTriangular h → (∀ w ∈ W, A *ᵥ w ∈ W) →
      ∃ c : ℂ, A *ᵥ w₀ = c • w₀ := by
  classical
  have hex : ∃ n : ℕ, ∃ w ∈ W, w ≠ 0 ∧ ∀ i, n ≤ h i → w i = 0 := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    refine ⟨Finset.univ.sup h + 1, w, hw, hw0, fun i hi => ?_⟩
    have : h i ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ i)
    omega
  obtain ⟨w₀, hw₀, hne, hz⟩ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    apply hne
    funext i
    exact hz i (by omega)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin : ∀ w ∈ W, (∀ i, m ≤ h i → w i = 0) → w = 0 := by
    intro w hw hw'
    by_contra hw0
    exact Nat.find_min hex (show m < Nat.find hex by omega) ⟨w, hw, hw0, hw'⟩
  have hj : ∃ j, h j = m := by
    by_contra hno
    apply hne
    refine hmin w₀ hw₀ fun i hi => hz i ?_
    have : h i ≠ m := fun e => hno ⟨i, e⟩
    omega
  obtain ⟨j, hj⟩ := hj
  refine ⟨w₀, hw₀, hne, fun A hA hAW => ⟨A j j, ?_⟩⟩
  rw [← sub_eq_zero]
  refine hmin _ (W.sub_mem (hAW _ hw₀) (W.smul_mem _ hw₀)) fun i hi => ?_
  have key : (A *ᵥ w₀) i = A i j * w₀ j := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)
    have hkj : h k ≠ m := fun e => hk (hinj (e.trans hj.symm))
    rcases lt_or_ge (h k) (h i) with h1 | h1
    · rw [hA h1, zero_mul]
    · rw [hz k (by omega), mul_zero]
  rw [Pi.sub_apply, key, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [hij, sub_self]
  · have him : h i ≠ m := fun e => hij (hinj (e.trans hj.symm))
    rw [hA (show h j < h i by omega), hz i (by omega)]
    simp

def perp (T : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {y | ∀ x ∈ T, star y ⬝ᵥ x = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [star_add, add_dotProduct, ha x hx, hb x hx, add_zero]
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro c a ha x hx
    rw [star_smul, smul_dotProduct, ha x hx, smul_zero]

theorem perp_ne_bot (T : Submodule ℂ (ι → ℂ)) (hT : T ≠ ⊤) : perp T ≠ ⊥ := by
  obtain ⟨f, hf, hle⟩ := T.exists_le_ker_of_lt_top hT.lt_top
  have hfx : ∀ x, f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  intro hb
  have hy : (star fun i => f (Pi.single i 1) : ι → ℂ) ∈ perp T := by
    intro x hx
    rw [star_star, ← hfx]
    exact hle hx
  rw [hb, Submodule.mem_bot, star_eq_zero] at hy
  apply hf
  refine LinearMap.ext fun x => ?_
  rw [hfx, hy]
  simp

omit [DecidableEq ι] in
open ComplexOrder in
theorem eq_zero_of_mem_perp {T : Submodule ℂ (ι → ℂ)} {y : ι → ℂ} (h1 : y ∈ T) (h2 : y ∈ perp T) : y = 0 :=
  dotProduct_star_self_eq_zero.1 (h2 y h1)

theorem eq_top_of_minimal {G : Type} (A : G → Matrix ι ι ℂ) (hadj : ∀ g, ∃ g', A g' = (A g)ᴴ)
    (N : Submodule ℂ (ι → ℂ))
    (hN : ∀ W : Submodule ℂ (ι → ℂ), W ≠ ⊥ → (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) →
      (∀ U : Submodule ℂ (ι → ℂ), U ≠ ⊥ → (∀ g, ∀ w ∈ U, A g *ᵥ w ∈ U) → U ≤ W → U = W) → W ≤ N) :
    N = ⊤ := by
  set T : Submodule ℂ (ι → ℂ) := sSup {W | (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) ∧ W ≤ N} with hT
  have hTN : T ≤ N := sSup_le fun W hW => hW.2
  have hTs : ∀ g, ∀ w ∈ T, A g *ᵥ w ∈ T := by
    intro g
    have : T ≤ T.comap (Matrix.toLin' (A g)) := by
      refine sSup_le fun W hW w hw => ?_
      have hWT : W ≤ T := le_sSup hW
      simpa using hWT (hW.1 g w hw)
    intro w hw
    simpa using this hw
  have hPs : ∀ g, ∀ w ∈ perp T, A g *ᵥ w ∈ perp T := by
    intro g w hw x hx
    obtain ⟨g', hg'⟩ := hadj g
    rw [star_mulVec, ← dotProduct_mulVec, ← hg']
    exact hw _ (hTs g' x hx)
  by_contra hne
  have hTne : T ≠ ⊤ := fun e => hne (top_le_iff.1 (e ▸ hTN))
  obtain ⟨W, ⟨hW0, hWs, hWP⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ (ι → ℂ))).has_min
    {W | W ≠ ⊥ ∧ (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) ∧ W ≤ perp T} ⟨perp T, perp_ne_bot T hTne, hPs, le_rfl⟩
  have hWN : W ≤ N := hN W hW0 hWs fun U hU0 hUs hUW => by
    by_contra hUne
    exact hmin U ⟨hU0, hUs, hUW.trans hWP⟩ (lt_of_le_of_ne hUW hUne)
  have hWT : W ≤ T := le_sSup ⟨hWs, hWN⟩
  apply hW0
  rw [eq_bot_iff]
  intro y hy
  exact eq_zero_of_mem_perp (hWT hy) (hWP hy)

omit [DecidableEq ι] in
theorem integral_mem_of_forall_mem {X : Type} [MeasurableSpace X] (μ : Measure X) (W : Submodule ℂ (ι → ℂ))
    (f : X → ι → ℂ) (hf : Integrable f μ) (hW : ∀ x, f x ∈ W) : ∫ x, f x ∂μ ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have := (LinearMap.toContinuousLinearMap φ).integral_comp_comm hf
  simp only [LinearMap.coe_toContinuousLinearMap'] at this
  rw [← this]
  simp [fun x => hφ _ (hW x)]

end Lin

theorem goodPI_of (hS : SmallPI) : GoodPI := by
  intro G _ _ _ _ _ K _ _ _ μ _ _ st S hKS e d M he hfin hM ι _ _ ρ hρ E hE g
  obtain ⟨φ, hφc, hφ⟩ := hfin
  obtain ⟨h, hinj, htri⟩ := hρ.tri
  rw [← LinearMap.ker_eq_top]
  refine eq_top_of_minimal (fun x => ρ x) (fun x => ⟨st x, hρ.adj x⟩) _ fun W hW0 hWs hmin => ?_
  obtain ⟨w₀, hw₀, hne, heig⟩ := exists_common_eigenvector h hinj W hW0
  have hcont : Continuous fun x : K => ρ x *ᵥ w₀ :=
    (hρ.cont.comp continuous_subtype_val).matrix_mulVec continuous_const
  have hint : ∀ i, Integrable (fun x : K => φ i x • (ρ x *ᵥ w₀)) μ := fun i =>
    ((hφc i).smul hcont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set θ : Fin d → ι → ℂ := fun i => ∫ x : K, φ i x • (ρ x *ᵥ w₀) ∂μ with hθ
  set U : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k *ᵥ w₀) with hU
  have hUW : U = W := by
    refine hmin U ?_ ?_ ?_
    · intro hb
      have : w₀ ∈ U := Submodule.subset_span ⟨1, by simp⟩
      rw [hb, Submodule.mem_bot] at this
      exact hne this
    · intro x
      have : U ≤ U.comap (Matrix.toLin' (ρ x)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        obtain ⟨k', hk', s, hs, hks⟩ := hKS (x * k)
        obtain ⟨c, hc⟩ := heig (ρ s) (htri s hs) (hWs s)
        have e1 : ρ x *ᵥ (ρ k *ᵥ w₀) = c • (ρ k' *ᵥ w₀) := by
          rw [mulVec_mulVec, ← map_mul, hks, map_mul, ← mulVec_mulVec, hc, mulVec_smul]
        show Matrix.toLin' (ρ x) (ρ k *ᵥ w₀) ∈ U
        rw [Matrix.toLin'_apply, e1]
        exact U.smul_mem _ (Submodule.subset_span ⟨⟨k', hk'⟩, rfl⟩)
      intro w hw
      simpa using this hw
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      exact hWs k w₀ hw₀
  set Y : Submodule ℂ (ι → ℂ) := Submodule.span ℂ (Set.range θ) with hY
  have hYW : Y ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact integral_mem_of_forall_mem μ W _ (hint i) fun x => W.smul_mem _ (hWs x w₀ hw₀)
  have hEY : W ≤ Y.comap E := by
    rw [← hUW]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨c, hc⟩ := hφ k
    have e1 : E (ρ k *ᵥ w₀) = ∑ i, c i • θ i := by
      rw [hE, ← integral_mul_right_eq_self _ k⁻¹]
      have : ∀ x : K, e (x * k⁻¹) • (ρ ((x * k⁻¹ : K) : G) *ᵥ (ρ k *ᵥ w₀)) =
          ∑ i, c i • (φ i x • (ρ x *ᵥ w₀)) := by
        intro x
        rw [mulVec_mulVec, ← map_mul, hc, Finset.sum_smul]
        simp [smul_smul]
      simp only [this]
      rw [integral_finsetSum (f := fun i (x : K) => c i • (φ i x • (ρ x *ᵥ w₀))) _
        fun i _ => (hint i).smul (c i)]
      simp only [integral_smul, hθ]
    show E (ρ k *ᵥ w₀) ∈ Y
    rw [e1]
    exact Y.sum_mem fun i _ => Y.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrk : Module.finrank ℂ Y ≤ d := by
    have := finrank_range_le_card (R := ℂ) θ
    rwa [Fintype.card_fin] at this
  intro w hw
  exact hS (ι → ℂ) W Y hYW E (fun w hw => hEY hw) M
    (lt_of_le_of_lt (Nat.pow_le_pow_left hrk 2) hM) _ (fun i w hw => by simpa using hWs (g i) w hw) w hw

end CompanionTheory.D.gk.admitted
