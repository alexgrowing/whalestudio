import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushA
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

theorem snc_eval_zero {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set X}
    (h : IsSNC A L s m W) {k : Fin r} {x : X} (hx : x ∈ W k) (hm : m k ≠ 0) : s x x = 0 := by
  obtain ⟨ψ, -, hxs, -, σ, -, hW, u, -, -, hs⟩ := h x
  have hx' : x ∈ W k ∩ ψ.source := ⟨hx, hxs⟩
  rw [hW k] at hx'
  obtain ⟨-, i, hσ, hψ⟩ := hx'
  rw [hs x hxs]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [hσ, hψ, hm]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (h0 : eval z (map (Int.castRingHom ℂ) s) = 0) :
    ∃ W' ∈ divSupp P s, IsHorizontal W' ∧ z ∈ mcPts W' := by
  classical
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun f => rfl
  haveI hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    rw [sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨fun f hf => ?_, ?_⟩
    · rw [RingHom.mem_ker, hφ]
      exact hz.2 f hf
    · show s ∈ RingHom.ker φ
      rw [RingHom.mem_ker, hφ]
      exact h0
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hmem : ∀ f ∈ W', eval z (map (Int.castRingHom ℂ) f) = 0 := fun f hf => by
    have := hW'le hf
    rwa [RingHom.mem_ker, hφ] at this
  refine ⟨W', ⟨hW', ?_⟩, ?_, ⟨hz.1, hmem⟩⟩
  · intro k
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun hX => hi (by simpa using hmem _ hX)⟩
  · show Ideal.comap _ W' = ⊥
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap] at hn
    rw [Ideal.mem_bot]
    have := hmem _ hn
    simpa using this

theorem proj_ne_zero_of_snc {P J : Ideal (MRing ι)} {e n : ℕ} (R : AnLogRes P J e) {A : HermLine ι}
    {s : MRing ι} {r : ℕ} {m : Fin r → ℕ} {W : Fin r → Set R.X}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)}
    (hsnc : IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W)
    (hΨ : ∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) {k : Fin r} (hm : m k ≠ 0)
    {x : R.X} (hx : x ∈ W k) : Ψ (segre (R.lift x x)) ≠ 0 := by
  have h0 := snc_eval_zero hsnc hx hm
  have hz : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  obtain ⟨W', hW', hh, hzW⟩ := exists_divSupp_of_eval hz h0
  exact hΨ W' hW' hh _ hzW

theorem divPushFibre_of (h1 : DivPushResSideStatement) (h2 : DivPushPointStatement) :
    DivPushFibreStatement := by
  unfold DivPushResSideStatement at h1
  unfold DivPushPointStatement at h2
  unfold DivPushFibreStatement
  intro K _ ι _ P J n R L B B₁ s r m W BW Ψ hAr hLs hBs hB1s hB1a hsec hsnc hHolo hΨ
  have hclosed : ∀ k, IsClosed (W k) := by
    intro k
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨ψ, -, hxs, -, σ, -, hW, -⟩ := hsnc x
    refine ⟨ψ.source ∩ {y | ∀ i, σ k = some i → ψ y i ≠ 0}, ?_, ?_, ?_⟩
    · rintro y ⟨hys, hy⟩ hyW
      have hyy : y ∈ W k ∩ ψ.source := ⟨hyW, hys⟩
      rw [hW k] at hyy
      obtain ⟨-, i, hi, h0⟩ := hyy
      exact hy i hi h0
    · cases hσ : σ k with
      | none =>
        have e : ψ.source ∩ {y | ∀ i, (none : Option (Fin (n + 1))) = some i → ψ y i ≠ 0} =
            ψ.source := by
          ext y
          simp
        rw [e]
        exact ψ.open_source
      | some i0 =>
        have e : ψ.source ∩ {y | ∀ i, some i0 = some i → ψ y i ≠ 0} =
            ψ.source ∩ (fun y => ψ y i0) ⁻¹' {0}ᶜ := by
          ext y
          simp
        rw [e]
        exact ((continuous_apply i0).comp_continuousOn ψ.continuousOn).isOpen_inter_preimage
          ψ.open_source isOpen_compl_singleton
    · refine ⟨hxs, fun i hi h0 => hx ?_⟩
      have hxx : x ∈ {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0} := ⟨hxs, i, hi, h0⟩
      rw [← hW k] at hxx
      exact hxx.1
  have hres : ∀ k, m k ≠ 0 → _ := fun k hmk =>
    h1 K ι P J n R L B₁ Ψ (W k) (BW k) hAr hLs hB1s hB1a (hclosed k) (hHolo k)
      (fun x hx => proj_ne_zero_of_snc R hsnc hΨ hmk hx)
  have hint : ∀ k ∈ Finset.univ, Integrable (fun y => (m k : ℝ) * divFib R L B₁ Ψ (BW k) y) := by
    intro k _
    by_cases hmk : m k = 0
    · simp [hmk]
    · exact ((hres k hmk).1).const_mul _
  have step : ∀ k ∈ Finset.univ, (m k : ℝ) * mInt (BW k)
      (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
      ((fun x => Real.log (B₁.h (R.lift x x))) ∘ Subtype.val) =
        ∫ y, (m k : ℝ) * divFib R L B₁ Ψ (BW k) y := by
    intro k _
    by_cases hmk : m k = 0
    · simp [hmk]
    · rw [integral_const_mul, (hres k hmk).2]
  rw [Finset.sum_congr rfl step,
    ← integral_finset_sum Finset.univ (f := fun k y => (m k : ℝ) * divFib R L B₁ Ψ (BW k) y) hint]
  apply integral_congr_ae
  filter_upwards [h2 K ι P J n R L B B₁ s r m W BW Ψ hAr hLs hBs hB1s hB1a hsec hsnc hHolo hΨ]
    with y hy
  simpa using hy

end ReciprocityTheory.ChartRestriction.G.Geo
