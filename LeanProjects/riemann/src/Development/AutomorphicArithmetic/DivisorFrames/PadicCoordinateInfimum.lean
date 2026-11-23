import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.PadicSpanCoordinateLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

private theorem norm_le_one_of_int {F : Type} [NormedField F] [IsUltrametricDist F] (y : F)
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := F)).integer y := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h1
  have h3 : ‖y‖₊ ≤ 1 := h2
  exact_mod_cast h3

private theorem bddBelow_support_primePowerComponent_coeff (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] (g : ℕ)
    (j : K →+* ℂ_[p]) (L : Submodule (𝓞 K) (Fin g → K)) (q : Fin g) (hL : L.FG) :
    ∃ B : ℝ, ∀ v ∈ L, ‖j (v q)‖ ≤ B := by
  obtain ⟨T, rfl⟩ := hL
  refine ⟨∑ t ∈ T, ‖j (t q)‖, fun v hv => ?_⟩
  have h0 : (0 : ℝ) ≤ ∑ t ∈ T, ‖j (t q)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  induction hv using Submodule.span_induction with
  | mem x hx => exact Finset.single_le_sum (f := fun t => ‖j (t q)‖) (fun _ _ => norm_nonneg _) hx
  | zero => simpa using h0
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    have e : (a • x) q = (a : K) * x q := rfl
    have ha : ‖j (a : K)‖ ≤ 1 :=
      norm_le_one_of_int _ (map_isIntegral_int j (RingOfIntegers.isIntegral_coe a))
    rw [e, map_mul, norm_mul]
    calc ‖j (a : K)‖ * ‖j (x q)‖ ≤ 1 * ‖j (x q)‖ := by gcongr
      _ ≤ _ := by rwa [one_mul]

theorem UpperTheory.padic_coordinate_infimum :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] (g : ℕ) (j : K →+* ℂ_[p]) (L : Submodule (𝓞 K) (Fin g → K)) (S : Set (Fin g)) (q : Fin g), L.FG → (∃ v ∈ L, (∀ k, k ∉ S → v k = 0) ∧ v q ≠ 0) → sInf {r : ℝ | ∃ c : Fin g → ℂ_[p], c q ≠ 0 ∧ (∀ k, k ∉ S → c k = 0) ∧ (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ L) ∧ c = ∑ m, a m • fun i => j (v m i)) ∧ r = ‖c q‖⁻¹} = (sSup ((fun b => ‖j b‖) '' {b : K | ∃ v ∈ L, (∀ k, k ∉ S → v k = 0) ∧ b = v q}))⁻¹ := by
  intro p _ K _ _ g j L S q hL hex
  obtain ⟨B, hB⟩ := bddBelow_support_primePowerComponent_coeff p K g j L q hL
  set A : Set ℝ := (fun b => ‖j b‖) '' {b : K | ∃ v ∈ L, (∀ k, k ∉ S → v k = 0) ∧ b = v q} with hA
  set R : Set ℝ := {r : ℝ | ∃ c : Fin g → ℂ_[p], c q ≠ 0 ∧ (∀ k, k ∉ S → c k = 0) ∧ (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ L) ∧ c = ∑ m, a m • fun i => j (v m i)) ∧ r = ‖c q‖⁻¹} with hR
  have hbdd : BddAbove A := by
    refine ⟨B, ?_⟩
    rintro _ ⟨_, ⟨v, hv, _, rfl⟩, rfl⟩
    exact hB v hv
  have hle : ∀ v ∈ L, (∀ k, k ∉ S → v k = 0) → ‖j (v q)‖ ≤ sSup A := fun v hv hS =>
    le_csSup hbdd ⟨v q, ⟨v, hv, hS, rfl⟩, rfl⟩
  have hmem : ∀ v ∈ L, (∀ k, k ∉ S → v k = 0) → v q ≠ 0 → ‖j (v q)‖⁻¹ ∈ R := by
    intro v hv hS hq
    refine ⟨fun i => j (v i), (map_ne_zero j).mpr hq, fun k hk => by simp [hS k hk],
      ⟨1, fun _ => 1, fun _ => v, fun _ => by simp, fun _ => hv, by simp⟩, rfl⟩
  obtain ⟨v0, hv0, hS0, hq0⟩ := hex
  have hpos0 : 0 < ‖j (v0 q)‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hq0)
  have hs : 0 < sSup A := hpos0.trans_le (hle v0 hv0 hS0)
  have hlow : ∀ r ∈ R, (sSup A)⁻¹ ≤ r := by
    rintro _ ⟨c, hcq, hcS, hc, rfl⟩
    obtain ⟨n, a, v, ha, hv, rfl⟩ := UpperTheory.padic_span_coordinate_lattice p K g j L S c hL hcS hc
    refine inv_anti₀ (norm_pos_iff.mpr hcq) ?_
    rw [Finset.sum_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hs.le fun m _ => ?_
    have e : (a m • fun i => j (v m i)) q = a m * j (v m q) := rfl
    rw [e, norm_mul]
    calc ‖a m‖ * ‖j (v m q)‖ ≤ 1 * ‖j (v m q)‖ := by gcongr; exact ha m
      _ ≤ _ := by rw [one_mul]; exact hle _ (hv m).1 (hv m).2
  have hne : R.Nonempty := ⟨_, hmem v0 hv0 hS0 hq0⟩
  have h1 : (sSup A)⁻¹ ≤ sInf R := le_csInf hne hlow
  have hi : 0 < sInf R := (inv_pos.mpr hs).trans_le h1
  refine le_antisymm ?_ h1
  rw [le_inv_comm₀ hi hs]
  refine csSup_le ⟨_, v0 q, ⟨v0, hv0, hS0, rfl⟩, rfl⟩ ?_
  rintro _ ⟨_, ⟨v, hv, hS, rfl⟩, rfl⟩
  by_cases hq : v q = 0
  · simp only [hq, map_zero, norm_zero]
    exact (inv_pos.mpr hi).le
  · have hp : 0 < ‖j (v q)‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr hq)
    exact (le_inv_comm₀ hp hi).mpr (csInf_le ⟨_, hlow⟩ (hmem v hv hS hq))
