import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.CartanFockDeg

theorem om_annih_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (sS : RealMat S) (sT : RealMat T)
    (hW : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (k : GA D S)
    (hk : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (k, 1) (annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) =
      annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) (om (k, 1) f) := by
  have hψ := hW.std
  have hm1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt T (1 : GA D T)) = 1 := by
    rw [hm1]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have hinv : compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
    have a := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k
    have b : compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * compAt θ τ (Formalism.L2.Theta.mt S k) = 1 := by
      have := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ k⁻¹
      rwa [inv_inv] at this
    calc compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ
        = compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * sS τ * (compAt θ τ (Formalism.L2.Theta.mt S k) * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) := by
          rw [a, Matrix.mul_one]
      _ = compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) * (compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ) * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
          rw [hk τ]; simp only [Matrix.mul_assoc]
      _ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
          rw [← Matrix.mul_assoc, b, Matrix.one_mul]
  have hJ : cplxO (sS τ) (sT τ) (z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹)) =
      cplxO (sS τ) (sT τ) z * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := by
    unfold cplxO
    rw [Matrix.smul_mul]
    simp only [Matrix.mul_assoc, hinv]
  have e : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (Formalism.L2.Theta.mt T (1 : GA D T)) * w * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) =
      w * compAt θ τ (Formalism.L2.Theta.mt S k⁻¹) := fun w => by rw [h1, Matrix.one_mul]
  unfold annih
  rw [map_add, map_smul, GlobalTheory.OrientedHeis.om_dRho hW hθ k 1 τ z hf, GlobalTheory.OrientedHeis.om_dRho hW hθ k 1 τ _ hf, e, e, hJ]

theorem om_keeps_fockDeg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (sS : RealMat S) (sT : RealMat T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ k : GA D S, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt S k) * sS τ = sS τ * compAt θ τ (Formalism.L2.Theta.mt S k)) → ∀ (N : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0) → ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) = 0 := by
  intro D ψ θ S T χS χT om sS sT hW hθ k hk N f hf hl l hlen
  have hψ := hW.std
  have hth : ∀ (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}, IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
    intro l g hg
    induction l with
    | nil => exact hg
    | cons p l ih => exact GlobalTheory.FockIndep.annih_theta hψ hθ p.1 _ p.2 ih
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ),
      om (k, 1) (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f) =
        (l.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k⁻¹))).foldr
          (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (om (k, 1) f) := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih =>
      rw [List.foldr_cons, List.map_cons, List.foldr_cons, om_annih_move sS sT hW hθ k hk p.1 p.2 (hth l hf), ih]
  let l' := l.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k))
  have hl' : l = l'.map fun p => (p.1, p.2 * compAt θ p.1 (Formalism.L2.Theta.mt S k⁻¹)) := by
    simp only [l', List.map_map]
    conv_lhs => rw [← List.map_id l]
    refine List.map_congr_left fun p _ => ?_
    simp only [Function.comp_apply, id_eq, Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  rw [hl', ← key, hl l' (by simp [l', hlen]), map_zero]

end GlobalTheory.CartanFockDeg
