import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.SumBoxSph

variable {D : D7}

theorem rat_mul_gen {k l m : ℕ} (q : Matrix (Fin k) (Fin l) D.host.E) (p : AF D.host.F) (a : D.host.E)
    (t : Fin l → D.host.E) (z : Fin m → D.host.E) :
    rat q ⬝ (Matrix.of fun i j => (p ⊗ₜ[D.host.F] (a * t i * z j) : AE D) : Mx D l m) =
      (Matrix.of fun i j => (p ⊗ₜ[D.host.F] (a * (q *ᵥ t) i * z j) : AE D) : Mx D k m) := by
  ext i j
  have h : ∀ e y : D.host.E, incA D e * (p ⊗ₜ[D.host.F] y : AE D) = p ⊗ₜ[D.host.F] (e * y) := fun e y => by
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (p ⊗ₜ[D.host.F] y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  show ∑ r, incA D (q i r) * (p ⊗ₜ[D.host.F] (a * t r * z j) : AE D) = p ⊗ₜ[D.host.F] (a * (∑ r, q i r * t r) * z j)
  rw [Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h]
  congr 1
  ring

theorem resT_mem_latO {A B W H : HSp D} (o : OrthDec B W H) {LA : Lat A} {LW : Lat W} {LH : Lat H}
    {P : FinPl D → Prop} {u : WO A B} (hu : u ∈ latO A B LA (sumLatO o LW LH) P) :
    o.resT A u ∈ (latO A W LA LW P).prod (latO A H LA LH P) := by
  have key : latO A B LA (sumLatO o LW LH) P ≤
      ((latO A W LA LW P).prod (latO A H LA LH P)).comap (o.resT A).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨x, hx, x', hx', rfl⟩ := (mem_sumLatO o LW LH t).1 ht
    have e₁ : o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
        Matrix.zero_mulVec, add_zero]
    have e₂ : o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
        Matrix.zero_mulVec, zero_add]
    refine ⟨AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, x, hx, ?_⟩,
      AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, x', hx', ?_⟩⟩
    · have := rat_mul_gen o.qA (pairA D.host.F 0 α) a (o.iA *ᵥ x + o.iB *ᵥ x') fun j => ∑ k, star (s k) * A.gram k j
      rw [e₁] at this
      exact this
    · have := rat_mul_gen o.qB (pairA D.host.F 0 α) a (o.iA *ᵥ x + o.iB *ᵥ x') fun j => ∑ k, star (s k) * A.gram k j
      rw [e₂] at this
      exact this
  exact key hu

theorem isHalf_mul {k l m : ℕ} {e : AE D} (p : Mx D k l) {u : Mx D l m} (hu : IsHalf e u) : IsHalf e (p ⬝ u) := by
  intro i j
  show e * ∑ r, p i r * u r j = ∑ r, p i r * u r j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [mul_left_comm, hu r j]

theorem isSphOff_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B W H : HSp D) (o : OrthDec B W H) (LA : Lat A) (LW : Lat W) (LH : Lat H) (Sf : Finset (FinPl D)) (Φ : WO A W → ℂ) (Φ' : WO A H → ℂ), IsSphOff ψ A W LA LW Sf Φ → IsSphOff ψ A H LA LH Sf Φ' → IsSphOff ψ A B LA (sumLatO o LW LH) Sf (o.boxT A Φ Φ') := by
  intro D ψ A B W H o LA LW LH Sf Φ Φ' h₁ h₂
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · obtain ⟨hL, hR⟩ := resT_mem_latO o hu
    rw [o.heisO_boxT, map_nsmul, Prod.smul_fst, Prod.smul_snd, h₁.1 _ hL, h₂.1 _ hR]
  · obtain ⟨hL, hR⟩ := resT_mem_latO o hu
    rw [o.heisO_boxT, h₁.2 e he _ hL (isHalf_mul o.pA hh), h₂.2 e he _ hR (isHalf_mul o.pB hh)]

end GlobalTheory.Core.Rk.SumBoxSph

end
