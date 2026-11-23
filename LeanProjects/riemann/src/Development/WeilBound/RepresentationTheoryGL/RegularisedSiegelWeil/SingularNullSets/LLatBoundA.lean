import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.MemIntROfFinPart
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.NormDetLeFactorialMulProd

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem fullRank_col (D : D7) (a n n₀ : ℕ) (hn₀ : 0 < n₀) (f : SchwartzMap (D.what₂.Tau → Fin a → Fin n → ℂ) ℂ) :
    ∃ C : ℝ, ∀ B : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ, (∀ τ, ‖(B τ).det‖ = 1) →
      ∑' ξ : {ξ : Matrix (Fin a) (Fin n) D.host.E // ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
        ‖f (fun τ => B τ * ξ.1.map (tauE D τ))‖ₑ ≤ ENNReal.ofReal C := by
  haveI := GlobalTheory.CompanionTheory.Ipf.Bdd.nonempty_tau D
  obtain ⟨e, he⟩ : ∃ e : (D.what₂.Tau → Fin n → Fin a → ℂ) ≃ₗ[ℝ] (D.what₂.Tau → Fin a → Fin n → ℂ),
      ∀ x τ i j, e x τ i j = x τ j i :=
    ⟨{ toFun := fun x τ i j => x τ j i
       invFun := fun y τ j i => y τ i j
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl }, fun _ _ _ _ => rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Twist.FullRank.tsum_schwartz_fullRank_le D.host.E (GlobalTheory.CompanionTheory.Ipf.Bdd.intR D)
    D.what₂.Tau (tauE D) (fun z hz h0 => GlobalTheory.CompanionTheory.Ipf.Bdd.one_le_prod_tauE z hz h0) a n n₀ hn₀
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e.toContinuousLinearEquiv f)
  refine ⟨C, fun B hB => ?_⟩
  have hBt : ∀ τ, ‖(B τ)ᵀ.det‖ = 1 := fun τ => by
    rw [Matrix.det_transpose]
    exact hB τ
  obtain ⟨T, hT⟩ : ∃ T : {γ : Matrix (Fin n) (Fin a) D.host.E //
        γ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * γ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} ≃
      {ξ : Matrix (Fin a) (Fin n) D.host.E //
        ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
      ∀ γ, (T γ).1 = γ.1ᵀ :=
    ⟨{ toFun := fun γ => ⟨γ.1ᵀ, by rw [Matrix.rank_transpose]; exact γ.2.1, fun i j => γ.2.2 j i⟩
       invFun := fun ξ => ⟨ξ.1ᵀ, by rw [Matrix.rank_transpose]; exact ξ.2.1, fun i j => ξ.2.2 j i⟩
       left_inv := fun γ => Subtype.ext (Matrix.transpose_transpose _)
       right_inv := fun ξ => Subtype.ext (Matrix.transpose_transpose _) }, fun _ => rfl⟩
  rw [← T.tsum_eq]
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hC (fun τ => (B τ)ᵀ) hBt)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  congr 2
  funext τ i j
  rw [LinearEquiv.coe_toContinuousLinearEquiv']
  refine Eq.trans ?_ (he _ τ i j).symm
  rw [hT]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
