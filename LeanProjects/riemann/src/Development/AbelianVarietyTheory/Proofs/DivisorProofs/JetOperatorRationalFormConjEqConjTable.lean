import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacEqJets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.JetDescent

theorem coe_lift_of_mem (M : IntermediateField ℚ ℂ) (x : ℂ) (hx : x ∈ M) : Formalism.MainNotions.TaylorLogMetric.liftM M x = ⟨x, hx⟩ := by
  unfold Formalism.MainNotions.TaylorLogMetric.liftM
  exact dif_pos hx

theorem mapVV_rational_form_conj : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  intro D a b lam lam' n J σ ρ' f hV hJ hσ hf u
  have halg : ∀ x : D.what₂.LL, D.what₂.embLL x ∈ Qbar := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom
  let e : D.what₂.LL →+* Qbar := D.what₂.embLL.codRestrict Qbar halg
  let i : Qbar →+* ℂ := algebraMap Qbar ℂ
  let r : Qbar →+* ℂ := ρ'
  let Jq : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → Qbar := fun m => ⟨J m, hJ m⟩
  have hie : i.comp e = D.what₂.embLL := RingHom.ext fun _ => rfl
  have hre : r.comp e = σ := RingHom.ext fun x => by
    rw [← hσ x]
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (halg x)]
    rfl
  have hJi : (fun m => i (Jq m)) = J := funext fun _ => rfl
  have hJr : (fun m => r (Jq m)) = fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m) := funext fun m => by
    unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [coe_lift_of_mem _ _ (hJ m)]
    rfl
  have h1 : Formalism.L2.Ker.jetMap J n (MvPolynomial.map D.what₂.embLL u.1) = MvPolynomial.map D.what₂.embLL (f u).1 := by
    have h := congrArg Subtype.val (hf u)
    rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV] at h
    exact h
  have h2 : Formalism.L2.Ker.jetMap Jq n (MvPolynomial.map e u.1) = MvPolynomial.map e (f u).1 := by
    apply MvPolynomial.map_injective i i.injective
    rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hie, hJi]
    exact h1
  have h3 := congrArg (MvPolynomial.map r) h2
  rw [Formalism.L2.Ker.map_jetMap, MvPolynomial.map_map, MvPolynomial.map_map, hre, hJr] at h3
  apply Subtype.ext
  rw [Formalism.L2.Ker.jetOp_coe lam lam' n hV]
  exact h3.symm

end GlobalTheory.JetDescent
