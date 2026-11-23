import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeComparisonRootMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricCombEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.ArInt GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ProjVar

namespace GlobalTheory.CoverModelTop

theorem top_eq : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ {F : Type} [Field F] [NumberField F] {C : GlobalTheory.TrueGeo.CxSt F} (Y : GlobalTheory.ProjVar.Var F) {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (A : ι → GlobalTheory.TrueGeo.Adl C Y), (∀ i, (A i).n = 1) → ∀ (M : GlobalTheory.TrueGeo.Model Y) (L : ι → GlobalTheory.HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) → ∀ (V : GlobalTheory.Mean4O.Cover Y) (L' : κ → GlobalTheory.HermLB V.p) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), (∀ z, V.Induces (A (e z)) (L' z) 1) → IsArFun L' Y.dim Φ → ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ (Y.dim + 1)) / (((m : ℕ) : ℝ) ^ (Y.dim + 1) * (Module.finrank ℚ F : ℝ)) = Φ (lin (fun z => (n (e z) : ℝ)) ^ (Y.dim + 1)) / V.ν := by
  intro hA _ F _ _ C Y ι κ _ _ e A _ M L m Ψ hL hΨ V L' Φ hL' hΦ n
  let N : ι → GlobalTheory.HermLB V.p := fun i => L' (e.symm i)
  have hΦ' : IsArFun N Y.dim (Φ ∘ₗ (rename e.symm : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial κ ℝ).toLinearMap) :=
    GlobalTheory.CovTest.SwapZ.isArFun_equiv V.ar e.symm (fun i => GlobalTheory.HermLB.Isometric.refl _) hΦ
  have hN : ∀ i, Norms V (N i) (fun x => genAt (A i).D x) (fun σ y => lnAdl (A i) σ y) fun v e' y => (A i).lg v e' y := by
    intro i
    have h := hL' (e.symm i)
    rw [e.apply_symm_apply] at h
    exact (norms_of_induces h).congr (fun x => pow_one _) (fun σ y => by simp) fun v e' y => by simp
  have e₂ := GlobalTheory.RadicalRootComparison.smul_eq_smul_of_norms hA V M A L m hL hΨ N hN rfl hΦ'
  have e₃ := LinearMap.congr_fun e₂ (lin (fun i => (n i : ℝ)) ^ (Y.dim + 1))
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow,
    GlobalTheory.CovTest.SwapZ.rename_lin_int, Equiv.symm_symm] at e₃
  have hn : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := Nat.cast_pos.2 Module.finrank_pos
  have hm : (0 : ℝ) < ((m : ℕ) : ℝ) ^ (Y.dim + 1) := pow_pos (Nat.cast_pos.2 m.2) _
  have hV : (0 : ℝ) < (V.deg : ℝ) := Nat.cast_pos.2 V.deg_pos
  rw [Cover.ν, div_eq_div_iff (mul_pos hm hn).ne' (mul_pos hn hV).ne']
  linear_combination -(Module.finrank ℚ F : ℝ) * e₃

end GlobalTheory.CoverModelTop
