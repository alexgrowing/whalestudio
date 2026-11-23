import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MixCondT

variable {D : D7}

theorem incAdj_surj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (η : Mx D ρ S.rank) :
    ∃ y, d.incAdj S y = d.incY S η := by
  refine ⟨adj (incA D (-D.host.xi0) • (η ⬝ giA S)), ?_⟩
  rw [HypDec.incAdj_apply, adj_adj, Matrix.smul_mul, Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, smul_smul,
    ← map_mul, neg_mul_neg, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul]

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T u (c • f) = c • heisO ψ S T u f := by
  funext z
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem mixT_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (c • f) y = c • d.mixT S ψ μ 𝓕 f y := by
  funext w₀
  simp only [GlobalTheory.MixModel.Check.mixT_eq, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext a
  ring

theorem isHalf_of_wittHyperbolic_inclusion {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {S : HSp D} {e : AE D} {w : WO S T₀}
    (h : IsHalf e (d.inc0 S w)) : IsHalf e w := by
  have hw : w = d.p0 ⬝ d.inc0 S w := by rw [HypDec.wittDecomp_inclAnisotropicHom_apply, ← Matrix.mul_assoc, d.p0_j0, Matrix.one_mul]
  intro i j
  rw [hw]
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem mul_eq_zero_real_fin {m k n : ℕ} {r : Mx D m k} {ξ : Mx D k n} (hr : r.map (finPart D) = 0)
    (hξ : MxAt (fun _ => True) ξ) : r ⬝ ξ = 0 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  have h1 : finPart D (r i l) = 0 := by
    have := congrFun (congrFun hr i) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  have h2 : infPart D (ξ l j) = 0 := RingHom.mem_ker.1 (Ideal.mem_inf.1 (hξ l j)).1
  rw [mul_comm]
  exact GlobalTheory.RatHalfDense.mul_eq_zero_of_parts h2 h1

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vT : VolM D σ V₀.rank) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ), p.Is dV dW x ψ → ∀ (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ), VacG ψ V₀ W₀ p.Γ₀ g → IsThetaFunO ψ V₀ W g' → (∀ y', dW.mixT V₀ ψ vT.μ vT.𝓕 g' y' = β₂ y' • g) → (∀ η ∈ p.B₂, ∀ b, dW.incAdj V₀ b = dW.incY V₀ η → ∀ z, β₂ (z + b) = β₂ z) → (∀ z, β₂ z ≠ 0 → ∃ r : Mx D V₀.rank σ, r.map (finPart D) = 0 ∧ ∃ η ∈ p.B₂, dW.incAdj V₀ (z - (y + r)) = dW.incY V₀ η) → (∀ ξ ∈ p.B₁, heisO ψ V₀ W (dW.incX V₀ ξ) g' = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • g') ∧ (∀ η ∈ p.B₂, heisO ψ V₀ W (dW.incY V₀ η) g' = g') ∧ IsLatVac (heisO ψ V₀ W) (p.Γ₀.map (dW.inc0 V₀)) g' := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vT p x y hp β₂ g g' hgv hg' hmix hinv hsupp
  have L := GlobalTheory.HeisTarget.main D ψ hψ V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol g' hg'
  have inj : ∀ f f' : WO V₀ W → ℂ, IsThetaFunO ψ V₀ W f → IsThetaFunO ψ V₀ W f' →
      (∀ y', dW.mixT V₀ ψ vT.μ vT.𝓕 f y' = dW.mixT V₀ ψ vT.μ vT.𝓕 f' y') → f = f' :=
    fun f f' hf hf' h => (GlobalTheory.T.thetaFunction_determined_by_mixedCoordinates D ψ hψ V₀ W f f' hf hf').2 W₀ σ dW vT h
  have th : ∀ u, IsThetaFunO ψ V₀ W (heisO ψ V₀ W u g') := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ hξ
    have hξf : MxAt (fun _ => True) ξ := hp.b₁.fin ξ hξ
    have key : ∀ z, symplO V₀ W (dW.incAdj V₀ z) (dW.incX V₀ ξ) =
        -Algebra.trace (AF D.host.F) (AE D) (z ⬝ ξ).trace := fun z => by
      rw [GlobalTheory.OrientedHeis.symplO_skew, HypDec.symplO_incX_incAdj]
    refine inj _ _ (th _) (GlobalTheory.OrientedHeis.theta_smul _ hg') fun y' => ?_
    rw [L.1 ξ y', mixT_smul, hmix y']
    by_cases hb : β₂ y' = 0
    · simp only [hb, zero_smul, smul_zero]
    obtain ⟨r, hr, η, hη, he⟩ := hsupp y' hb
    have hη1 : ψ (symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ ξ)) = 1 := by
      rw [GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv,
        (hp.dualB' η (hp.b₂.fin η hη)).1 hη ξ hξ, inv_one]
    have hsplit : y' = y + r + (y' - (y + r)) := by abel
    have e1 : symplO V₀ W (dW.incAdj V₀ y') (dW.incX V₀ ξ) =
        symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ) + symplO V₀ W (dW.incY V₀ η) (dW.incX V₀ ξ) := by
      rw [← he, key, key, key]
      conv_lhs => rw [hsplit]
      rw [Matrix.add_mul, Matrix.add_mul, mul_eq_zero_real_fin hr hξf, add_zero, Matrix.trace_add, map_add, neg_add]
    rw [e1, AddChar.map_add_eq_mul, hη1, mul_one]
  · intro η hη
    obtain ⟨b, hb⟩ := incAdj_surj dW V₀ η
    rw [← hb]
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [GlobalTheory.MixModel.Check.mixT_heis_incAdj, hmix, hmix, hinv η hη b hb y']
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    rw [← map_nsmul]
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [L.2.1, hmix, heisO_smul, hgv.2.1 w hw]
  · intro e he u hu hh
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    refine inj _ _ (th _) hg' fun y' => ?_
    rw [L.2.1, hmix, heisO_smul, hgv.2.2 e he w hw (isHalf_of_wittHyperbolic_inclusion dW hh)]

end GlobalTheory.MixCondT

end
