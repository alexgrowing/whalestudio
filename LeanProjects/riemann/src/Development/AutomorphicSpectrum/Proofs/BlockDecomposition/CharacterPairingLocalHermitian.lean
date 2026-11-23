import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.SplitPair

section gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_trace [FiniteDimensional F E] (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    evInf F w (Algebra.trace (AF F) (AF F ⊗[F] E) z) =
      Algebra.trace w.Completion (w.Completion ⊗[F] E) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    have e : compInf F E w (a ⊗ₜ[F] x) = evInf F w a ⊗ₜ[F] x := rfl
    rw [e, GlobalTheory.OppLinChar.trace_tmul', GlobalTheory.OppLinChar.trace_tmul', map_mul, AlgHom.commutes]

theorem eq_single (v : HeightOneSpectrum (𝓞 F)) (y : AF F)
    (hi : ∀ w, evInf F w y = 0) (hf : ∀ v' ≠ v, evFin F v' y = 0) :
    y = pairA F 0 (singleV F v (evFin F v y)) := by
  classical
  refine Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => ?_)
  by_cases h : u = v
  · subst h
    change _ = singleV F u _ u
    exact (RestrictedProduct.single_eq_same _ u _).symm
  · change _ = singleV F v _ u
    exact (hf u h).trans (RestrictedProduct.single_eq_of_ne _ _ h).symm

theorem cA_eq_sigR (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => rfl

theorem psi_half_trace {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F))
    (τ : E →ₐ[F] Fv F v) (ψ : AddChar (AF F) ℂ) {n : ℕ}
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) E)
    (hx : ∀ i j, sigR (AF F) σ (x j i) = x i j) (hb : ∀ i j, σ (b j i) = b i j)
    (hinf : ∀ w i j, compInf F E w (x i j) = 0) (hfin : ∀ v' ≠ v, ∀ i j, compFin F E v' (x i j) = 0) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ i, ∑ j, x i j * inclR (AF F) (b j i))) =
      psiV F ψ v (∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i)) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hcm.2.2.1
  set z : AF F ⊗[F] E := ∑ i, ∑ j, x i j * inclR (AF F) (b j i) with hz
  set a : Fv F v := ∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i) with ha
  have hzi : ∀ w, compInf F E w z = 0 := fun w => by
    simp only [hz, map_sum, map_mul, hinf, zero_mul, Finset.sum_const_zero]
  have hzf : ∀ v' ≠ v, compFin F E v' z = 0 := fun v' h => by
    simp only [hz, map_sum, map_mul, hfin v' h, zero_mul, Finset.sum_const_zero]
  have hpi : ∀ t : E →ₐ[F] Fv F v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z =
      ∑ i, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (x i j) * t (b j i) := fun t => by
    simp only [hz, map_sum, map_mul, GlobalTheory.OppLinChar.piW_inclR]
  have h1 : splitProj τ (compFin F E v z) = a := hpi τ
  have h2 : splitProj (τ.comp σ) (compFin F E v z) = a := by
    refine (hpi (τ.comp σ)).trans ?_
    rw [ha, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (x i j) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (x j i) := by
      rw [← hx i j, ← cA_eq_sigR]
      exact GlobalTheory.OppLinChar.piW_cA hcm τ (x j i)
    rw [e, AlgHom.comp_apply, hb i j]
    rfl
  set y : AF F := algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z with hy
  have hv : evFin F v y = a := by
    rw [hy, map_mul, AlgHom.commutes, GlobalTheory.OppLinChar.evFin_trace, GlobalTheory.OppLinChar.trace_split hcm τ, h1, h2,
      ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  have hs := eq_single v y
    (fun w => by rw [hy, map_mul, evInf_trace, hzi, map_zero, mul_zero])
    (fun v' h => by rw [hy, map_mul, GlobalTheory.OppLinChar.evFin_trace, hzf v' h, map_zero, mul_zero])
  rw [hv] at hs
  rw [hs]
  rfl

end gen

theorem pch_rat_split : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n),
    (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) →
    ∀ β : HermE D n, pch ψ x.1 (rat β.1) =
      psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  intro D n v τ ψ x hinf hfin β
  have hx : ∀ i j, sigR (AF D.host.F) D.sp.cm.sig (x.1 j i) = x.1 i j := fun i j =>
    congrFun (congrFun x.2 i) j
  have hb : ∀ i j, D.sp.cm.sig (β.1 j i) = β.1 i j := fun i j => congrFun (congrFun β.2 i) j
  exact psi_half_trace (isCMExt_host D) v τ ψ x.1 β.1 hx hb hinf hfin

end GlobalTheory.CompanionTheory.Jp.SplitPair
end
