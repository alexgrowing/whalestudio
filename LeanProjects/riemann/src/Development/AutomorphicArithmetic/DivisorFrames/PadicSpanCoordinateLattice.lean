import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

private theorem ringOfIntegers_baer_vectors (K : Type) [Field K] [NumberField K] (g : ℕ) :
    Module.Baer (𝓞 K) (Fin g → K) := by
  intro I f
  by_cases hI : I = ⊥
  · refine ⟨0, fun x hx => ?_⟩
    have hx0 : x = 0 := by simpa [hI] using hx
    subst hx0
    have : (⟨0, hx⟩ : I) = 0 := rfl
    rw [this]; simp
  · obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hy1 : (y : K) ≠ 0 := by exact_mod_cast hy0
    refine ⟨LinearMap.toSpanSingleton (𝓞 K) _ ((y : K)⁻¹ • f ⟨y, hy⟩), fun x hx => ?_⟩
    have h1 : x • f ⟨y, hy⟩ = y • f ⟨x, hx⟩ := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext1
      simp [mul_comm]
    rw [LinearMap.toSpanSingleton_apply, smul_comm, h1]
    have : y • f ⟨x, hx⟩ = (y : K) • f ⟨x, hx⟩ := rfl
    rw [this, smul_smul, inv_mul_cancel₀ hy1, one_smul]

private theorem exists_section (K : Type) [Field K] [NumberField K] (g : ℕ)
    (L : Submodule (𝓞 K) (Fin g → K)) (hL : L.FG) (π : (Fin g → K) →ₗ[𝓞 K] (Fin g → K)) :
    ∃ T : (Fin g → K) →ₗ[K] (Fin g → K), ∀ v ∈ L, T (π v) ∈ L ∧ π (T (π v)) = π v := by
  have hP : (L.map π).FG := hL.map π
  haveI : Module.Finite (𝓞 K) (L.map π) := Module.Finite.iff_fg.mpr hP
  haveI : Module.Flat (𝓞 K) (L.map π) := inferInstance
  haveI : Module.FinitePresentation (𝓞 K) (L.map π) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 K) (L.map π) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (π.submoduleMap L) LinearMap.id
    (π.submoduleMap_surjective L)
  obtain ⟨T, hT⟩ := (ringOfIntegers_baer_vectors K g).extension_property (L.map π).subtype
    (L.map π).injective_subtype (L.subtype ∘ₗ s)
  refine ⟨T.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K, fun v hv => ?_⟩
  have h1 : T (π v) = (s ⟨π v, Submodule.mem_map_of_mem hv⟩ : Fin g → K) :=
    LinearMap.congr_fun hT ⟨π v, Submodule.mem_map_of_mem hv⟩
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨π v, Submodule.mem_map_of_mem hv⟩)
  change T (π v) ∈ L ∧ π (T (π v)) = π v
  rw [h1]
  exact ⟨(s _).2, h2⟩

theorem UpperTheory.padic_span_coordinate_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] (g : ℕ) (j : K →+* ℂ_[p]) (L : Submodule (𝓞 K) (Fin g → K)) (S : Set (Fin g)) (c : Fin g → ℂ_[p]), L.FG → (∀ k, k ∉ S → c k = 0) → (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ L) ∧ c = ∑ m, a m • fun i => j (v m i)) → (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ L ∧ ∀ k, k ∉ S → v m k = 0) ∧ c = ∑ m, a m • fun i => j (v m i)) := by
  classical
  intro p _ K _ _ g j L S c hL hc h
  obtain ⟨n, a, v, ha, hv, hcv⟩ := h
  let π : (Fin g → K) →ₗ[𝓞 K] (Fin g → K) :=
    LinearMap.pi fun k => if k ∈ S then 0 else LinearMap.proj k
  have hπ : ∀ w k, π w k = if k ∈ S then 0 else w k := by
    intro w k
    by_cases hk : k ∈ S <;> simp [π, hk]
  obtain ⟨T, hT⟩ := exists_section K g L hL π
  refine ⟨n, a, fun m => v m - T (π (v m)), ha, fun m => ⟨L.sub_mem (hv m) (hT _ (hv m)).1, fun k hk => ?_⟩, ?_⟩
  · have := congrFun (hT _ (hv m)).2 k
    rw [hπ, hπ (v m), if_neg hk, if_neg hk] at this
    simp [this]
  · have h0 : ∀ k, ∑ m, a m * j (π (v m) k) = 0 := by
      intro k
      by_cases hk : k ∈ S
      · simp [hπ, hk]
      · have := congrFun hcv k
        rw [hc k hk] at this
        simpa [hπ, hk, Finset.sum_apply] using this.symm
    have hTw : ∀ w i, T w i = ∑ k, w k * T (Pi.single k 1) i := by
      intro w i
      have := LinearMap.pi_apply_eq_sum_univ T w
      rw [this, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e : (fun j => if k = j then (1 : K) else 0) = Pi.single k 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [e]; rfl
    funext i
    have h1 : ∑ m, a m * j (T (π (v m)) i) = 0 := by
      simp only [hTw (π _), map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp only [← mul_assoc]
      rw [← Finset.sum_mul, h0, zero_mul]
    rw [hcv]
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, map_sub, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, h1, sub_zero]
