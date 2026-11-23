import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDeterminantNonnegCurveDegree
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModel

theorem sec_linear : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) → ∀ i : L.B.ι, (s x).f i = ∑ k, ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) (β k) * (s (u k)).f i := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev m β u x hx i
  have hw : ∃ w' : W, ev w' ≠ 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨N, n, b, g, A, c, gw, -, -, hb, -⟩ := hM.fs
    exact hev (b.ext fun j => by rw [hb j, map_sum]; simp [map_smul, hne])
  obtain ⟨w', hw'⟩ := hw
  apply GlobalTheory.Cartier.fn_ext
  intro hU
  have ha : ψ (ev w') ≠ 0 := (map_ne_zero ψ).mpr hw'
  have hr : ∀ y : W, ψ (ev w') * GlobalTheory.Cartier.fnOf _ hU ((s y).f i) =
      ψ (ev y) * GlobalTheory.Cartier.fnOf _ hU ((s w').f i) := fun y => (hM.ratio y w' i hU).symm
  have hc : ∀ b : 𝓞 K, GlobalTheory.Cartier.fnOf _ hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (L.B.U i) b) =
      ψ (algebraMap K Ω (b : K)) := by
    intro b
    rw [hM.base]
    exact RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p _ hU) b
  have hex : ψ (ev x) = ∑ k, ψ (algebraMap K Ω (β k : K)) * ψ (ev (u k)) := by
    rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← IsScalarTower.algebraMap_smul K (β k) (u k : V), map_smul, Algebra.smul_def, map_mul]
  rw [map_sum]
  simp only [map_mul, hc]
  apply mul_left_cancel₀ ha
  rw [hr x, hex, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm (ψ (ev w')), hr (u k), mul_assoc]

end GlobalTheory.ImageModel
