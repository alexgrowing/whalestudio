import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaSpan

theorem ofIntVec_single {g : ℕ} (j : Fin g) :
    ofIntVec (Pi.single j (1 : ℤ)) = (Pi.single j 1 : Fin g → ℂ) := by
  funext i
  by_cases h : i = j
  · subst h; simp [ofIntVec]
  · simp [ofIntVec, Pi.single_eq_of_ne h]

theorem laws_of_level {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) (f : (Fin g → ℂ) → ℂ)
    (h : ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z) :
    (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z := by
  refine ⟨fun i z => ?_, fun j z => ?_⟩
  · have := h 0 (Pi.single i 1) z
    rw [ofIntVec_zero, ofIntVec_single] at this
    simpa [eC] using this
  · have := h (Pi.single j 1) 0 z
    rw [ofIntVec_zero, ofIntVec_single, add_zero] at this
    rw [this]
    congr 1
    simp only [eC, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [single_one_dotProduct, mulVec_single_one, Matrix.col_apply, transpose_apply]
    ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in

theorem _root_.GlobalTheory.ThetaSpan.mem_span_theta_of_level :
  (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, (Differentiable ℂ f ∧ ∀ (n n' : Fin g → ℤ) z, f (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * f z) → f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)))) := by
  intro _ H g τ hτ N hN f hf
  have hN0 : 0 < N := hN
  obtain ⟨hmem, hli⟩ := H g τ hτ N hN
  have hV : _root_.GlobalTheory.thetaLevel N τ = _root_.GlobalTheory.thetaLevelChar 0 0 N τ := by
    ext φ
    simp [_root_.GlobalTheory.mem_thetaLevel, _root_.GlobalTheory.mem_thetaLevelChar, _root_.ReciprocityTheory.PTheta.eC_zero]
  have hsymm : τ.IsSymm := (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm
  haveI : FiniteDimensional ℂ (_root_.GlobalTheory.thetaLevel N τ) := by
    rw [hV]
    exact _root_.GlobalTheory.finiteDimensional_thetaLevelChar hsymm hN0
  have hrank : Module.finrank ℂ (_root_.GlobalTheory.thetaLevel N τ) = N ^ g := by
    rw [hV, _root_.GlobalTheory.finrank_thetaLevelChar hτ hN0, Fintype.card_fin]
  let v : (Fin g → Fin N) → _root_.GlobalTheory.thetaLevel N τ := fun c => ⟨_, _root_.GlobalTheory.mem_thetaLevel.2 (hmem c)⟩
  have hvli : LinearIndependent ℂ v := LinearIndependent.of_comp (_root_.GlobalTheory.thetaLevel N τ).subtype hli
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank' (by simp [hrank])
  have hfv : (⟨f, _root_.GlobalTheory.mem_thetaLevel.2 hf⟩ : _root_.GlobalTheory.thetaLevel N τ) ∈ Submodule.span ℂ (Set.range v) := by
    rw [hspan]
    exact Submodule.mem_top
  have := Submodule.mem_map_of_mem (f := (_root_.GlobalTheory.thetaLevel N τ).subtype) hfv
  rw [Submodule.map_span, ← Set.range_comp] at this
  exact this

end GlobalTheory.ThetaSpan
