import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuousStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Aniso

theorem thetaKO_one_translate {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (f : WO S T → ℂ) : thetaKO om 1 h (om (g, 1) f) = thetaKO om g h f := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem thetaKernel_rationalSource_invariant {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S) (c : GA D S) (h : GA D T) :
    thetaKO om (γ * c) h f = thetaKO om c h f := by
  unfold thetaKO
  have e : om (γ * c, h) = om (γ, (1 : GA D T)) * om (c, h) := by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (GQ T).one_mem _ (hω.om_pres (c, h) f hf)

theorem thetaInt_translate {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (mT : Measure (GA D T)) (g : GA D S) (f : WO S T → ℂ) :
    thetaInt om mT (om (g, 1) f) 1 = thetaInt om mT f g := by
  simp only [thetaInt, thetaPair, thetaKO_one_translate]

theorem dblInt_thetaInt_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → ∀ g, ThetaPairConv omh mW φ' 1 g) → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (thetaInt omh mW φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro D ψ θ A cA a hDef W χ omh hω m mW hm hmW u hu hinv hK hconv φ hφ hKf
  obtain ⟨φ', hφ', hΛ⟩ := GlobalTheory.T.theta_kernel_exists_for_continuous D ψ θ A cA a hDef W χ omh hω φ hφ hKf m hm u hu hinv

  have hker : ∀ h, thetaKO omh 1 h φ' = 0 := by
    intro h
    have e := hΛ (fun f => thetaKO omh 1 h f)
      (fun f f' _ _ => by simp only [thetaKO, map_add, Pi.add_apply])
      (fun c f _ => by simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul])
      (fun γ hγ g => by
        simp only [thetaKO_one_translate]
        exact thetaKernel_rationalSource_invariant hω hφ hγ g h)
    simp only [thetaKO_one_translate] at e
    rw [← e]
    exact hK φ hφ h
  have hΛ' := hΛ (fun f => thetaInt omh mW f 1)
    (fun f f' hf hf' => by
      simp only [thetaInt, thetaPair]
      have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h (f + f') * (1 : GA D W → ℂ) h)
          = fun q => GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h f * (1 : GA D W → ℂ) h) q
            + GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h f' * (1 : GA D W → ℂ) h) q := by
        funext q
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_add, Pi.add_apply, add_mul]
      rw [e, average_eq, average_eq, average_eq, integral_add (hconv f hf 1) (hconv f' hf' 1), smul_add])
    (fun c f _ => by
      simp only [thetaInt, thetaPair]
      have e : GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h (c • f) * (1 : GA D W → ℂ) h)
          = fun q => c * GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h f * (1 : GA D W → ℂ) h) q := by
        funext q
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [e, average_eq, average_eq, integral_const_mul, mul_smul_comm])
    (fun γ hγ g => by
      rw [thetaInt_translate, thetaInt_translate]
      simp only [thetaInt, thetaPair]
      have e : (fun h => thetaKO omh (γ * g) h φ * (1 : GA D W → ℂ) h)
          = fun h => thetaKO omh g h φ * (1 : GA D W → ℂ) h := by
        funext h
        rw [thetaKernel_rationalSource_invariant hω hφ hγ g h]
      rw [e])
  have ef : thetaInt omh mW φ = fun g => thetaInt omh mW (omh (g, 1) φ) 1 := by
    funext g
    rw [thetaInt_translate]
  rw [ef, hΛ']
  simp only [thetaInt, thetaPair]
  have e0 : GlobalTheory.AutomorphicL2Unitary.descend (GQ W) (fun h => thetaKO omh 1 h φ' * (1 : GA D W → ℂ) h) = fun _ => 0 := by
    funext q
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, hker, zero_mul]
  rw [e0]
  simp

end GlobalTheory.Core.Rk.Aniso

end
