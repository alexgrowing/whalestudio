import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem exists_half_canMult : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  intro g Λ bs χ hχ hsq
  classical
  have hpm : ∀ l, χ l = 1 ∨ χ l = -1 := fun l =>
    mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq l)
  have hexp : ∀ k : ℤ, Complex.exp (↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (-1) ^ k := by
    intro k
    rw [Complex.ofReal_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hhalf : Complex.exp (2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  have hhalf' : Complex.exp (-(2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [Complex.exp_neg, hhalf]
    norm_num
  have hsame : ∀ j k : Fin g ⊕ Fin g, bs.repr (bs j) k = if j = k then 1 else 0 := by
    intro j k
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hsingle : ∀ i : Fin g, (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k)) = Pi.single i 1 ∧
      (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) = Pi.single i 1 := by
    intro i
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      by_cases hk : k = i
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
  have hdot : ∀ (a : Fin g → ℝ) (i : Fin g),
      (a ⬝ᵥ fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℝ)) = a i := by
    intro a i
    simp [dotProduct, Pi.single_apply]
  have hdot0 : ∀ a : Fin g → ℝ, (a ⬝ᵥ fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
    intro a
    simp [dotProduct]
  have hC_inl : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ((a i : ℝ) : ℂ)) := by
    intro a c i
    obtain ⟨h1, h2, -, -⟩ := hsingle i
    rw [h1, h2]
    simp only [GlobalTheory.CanTh.canMult, dotProduct_zero, hdot, hdot0]
    congr 1
    push_cast
    ring
  have hC_inr : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ((c i : ℝ) : ℂ))) := by
    intro a c i
    obtain ⟨-, -, h3, h4⟩ := hsingle i
    rw [h3, h4]
    simp only [GlobalTheory.CanTh.canMult, zero_dotProduct, hdot, hdot0]
    congr 1
    push_cast
    ring
  obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, a = fun i => if χ (bs (Sum.inl i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin g → ℝ, c = fun i => if χ (bs (Sum.inr i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  refine ⟨a, c, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    split_ifs <;> norm_num
  · simp only [hc]
    split_ifs <;> norm_num
  have hχ0 : ∀ l, χ l ≠ 0 := by
    intro l h
    have h' := hsq l
    rw [h] at h'
    norm_num at h'
  have hψ0 : ∀ l : Λ, GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)) ≠ 0 := by
    intro l
    simp only [GlobalTheory.CanTh.canMult]
    exact Complex.exp_ne_zero _
  have hψ : ∀ l l' : Λ,
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (l + l') (Sum.inl i))
                   (fun i => bs.repr (l + l') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
                     (fun i => bs.repr l (Sum.inr i)) *
          GlobalTheory.CanTh.canMult a c (fun i => bs.repr l' (Sum.inl i))
            (fun i => bs.repr l' (Sum.inr i)) *
          Complex.exp (Real.pi * Complex.I *
            (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
              bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)) := by
    intro l l'
    have hm : (fun i => bs.repr (l + l') (Sum.inl i)) =
        (fun i => bs.repr l (Sum.inl i)) + (fun i => bs.repr l' (Sum.inl i)) := by
      funext i
      simp [map_add]
    have hn : (fun i => bs.repr (l + l') (Sum.inr i)) =
        (fun i => bs.repr l (Sum.inr i)) + (fun i => bs.repr l' (Sum.inr i)) := by
      funext i
      simp [map_add]
    rw [hm, hn, GlobalTheory.HolTheta.canMult_add, hexp, Finset.sum_sub_distrib]
    rfl
  have hbasis : ∀ j : Fin g ⊕ Fin g, χ (bs j) =
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (bs j) (Sum.inl i))
        (fun i => bs.repr (bs j) (Sum.inr i)) := by
    rintro (i | i)
    · rw [hC_inl]
      rcases hpm (bs (Sum.inl i)) with h | h
      · simp [ha, h]
      · have h' : χ (bs (Sum.inl i)) ≠ 1 := by rw [h]; norm_num
        simp only [ha, h', if_false]
        rw [h, hhalf]
    · rw [hC_inr]
      rcases hpm (bs (Sum.inr i)) with h | h
      · simp [hc, h]
      · have h' : χ (bs (Sum.inr i)) ≠ 1 := by rw [h]; norm_num
        simp only [hc, h', if_false]
        rw [h, hhalf']
  exact GlobalTheory.HolTheta.eq_of_cocycle bs
    (fun l l' => Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
        bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)))
    (ψ := fun l => GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)))
    (fun _ _ => Complex.exp_ne_zero _) hχ0 hψ0 hχ hψ hbasis

end GlobalTheory.CompanionTheory.Ar.Nform
