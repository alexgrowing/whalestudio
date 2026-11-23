import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EmDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponents

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem mm_jn (hn : r + t = n) (M : Mx D c a) (x : Mx D a r) (v : Mx D a t) :
    mm M (jn hn x v) = jn hn (mm M x) (mm M v) := by
  unfold jn mm
  rw [← Matrix.mul_fromCols]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t) :
    mm (jn hn w v) (bl hn p q s u) = jn hn (mm w p + mm v s) (mm w q + mm v u) := by
  unfold jn PositivityTheory.Rg.Rsw.L.mm
  rw [show bl hn p q s u =
      (Matrix.fromBlocks p q s u).submatrix
        (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm from rfl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem block_mul₂ (hn : r + t = n) (p p' : Mx D r r) (q q' : Mx D r t) (s s' : Mx D t r) (u u' : Mx D t t) :
    (bl hn p q s u * bl hn p' q' s' u' : Matrix (Fin n) (Fin n) (AE D)) =
      bl hn (mm p p' + mm q s') (mm p q' + mm q u') (mm s p' + mm u s') (mm s q' + mm u u') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : r + t = n) :
    bl hn (1 : Mx D r r) (0 : Mx D r t) (0 : Mx D t r) (1 : Mx D t t) = (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem smul_blockMatrix_sub_one (hn : r + t = n) (e : AE D) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t)
    (h₁ : e • (p - 1) = p - 1) (h₂ : e • q = q) (h₃ : e • s = s) (h₄ : e • (u - 1) = u - 1) :
    e • (bl hn p q s u - 1) = bl hn p q s u - 1 := by
  have h : bl hn p q s u - 1 = bl hn (p - 1) q s (u - 1) := by
    rw [← blockRowSubstitution_one hn]
    unfold bl
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
      rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp
  rw [h]
  unfold bl
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp only [Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j
  · exact congrFun (congrFun h₃ i) j
  · exact congrFun (congrFun h₄ i) j

def shU (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn

def colU (hn : r + t = n) (g : GL (Fin t) (AE D)) : GL (Fin n) (AE D) where
  val := bl hn 1 0 0 g.1
  inv := bl hn 1 0 0 (g⁻¹).1
  val_inv := by
    rw [block_mul₂]
    have : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    have : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn

theorem smul_inv_sub (e : AE D) (g : GL (Fin t) (AE D)) (h : e • (g.1 - 1) = g.1 - 1) :
    e • ((g⁻¹).1 - 1) = (g⁻¹).1 - 1 := by
  have h1 : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (g⁻¹).1 - 1 = - ((g⁻¹).1 * (g.1 - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [h2, smul_neg, ← Matrix.mul_smul, h]

theorem trans_int {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X) (c : N ≃ₜ N) (κ₁ κ₂ : ℝ≥0)
    (h₁ : σ.map Θ = κ₁ • σ) (h₂ : lam.map c = κ₂ • lam) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k (c x) (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((κ₁ * κ₂ : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have hin : ∀ x, ∫ z, f (Θ z) * k x z ∂σ = (κ₁ : ℂ) * ∫ z, f z * k (c x) z ∂σ := by
    intro x
    have e₁ : ∫ z, f (Θ z) * k x z ∂σ = ∫ z, (fun w => f w * k (c x) w) (Θ z) ∂σ :=
      integral_congr_ae ((hk x).mono fun z hz => by simp only [hz])
    have e₃ := Θ.measurableEmbedding.integral_map (μ := σ) (fun w => f w * k (c x) w)
    rw [e₁, ← e₃, h₁, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp only [hin]
  rw [integral_const_mul]
  have e₂ : ∫ x, ∫ z, f z * k (c x) z ∂σ ∂lam = ∫ x, (fun u => ∫ z, f z * k u z ∂σ) (c x) ∂lam := rfl
  have e₄ := c.measurableEmbedding.integral_map (μ := lam) (fun u => ∫ z, f z * k u z ∂σ)
  rw [e₂, ← e₄, h₂, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

theorem map_val_rel {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X) (i : X → Y) (Θ : X → X) (T : Y → Y)
    (κ : ℝ≥0) (hi : Measurable i) (hΘ : Measurable Θ) (hT : Measurable T) (hc : ∀ z, i (Θ z) = T (i z)) (h : ν.map Θ = κ • ν) :
    (ν.map i).map T = κ • ν.map i := by
  rw [Measure.map_map hT hi]
  have : T ∘ i = i ∘ Θ := funext fun z => (hc z).symm
  rw [this, ← Measure.map_map hi hΘ, h, Measure.map_smul]

end GlobalTheory.CompanionTheory.OrbExist

end
