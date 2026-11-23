import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionIsotropicStabilizerArchimedeStatement
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
namespace GlobalTheory.Core.Rk.IwAd

theorem exists_stab_proj_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r)
    (x : ∀ v : FinPl D, Gv T v) (hx : ∀ v, emb D.sp.cm.sig T.gram v (x v) ∈ stab d)
    (S : Finset (FinPl D)) : ∃ p ∈ stab d,
      (∀ v ∈ S, proj D.sp.cm.sig T.gram v p = x v) ∧ (∀ v ∉ S, proj D.sp.cm.sig T.gram v p = 1) ∧
        ∀ w, projArch D.sp.cm.sig T.gram w p = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun v _ => map_one _, fun w => map_one _⟩
  | insert u S hu ih =>
    obtain ⟨p, hp, h1, h2, h3⟩ := ih
    refine ⟨emb D.sp.cm.sig T.gram u (x u) * p, mul_mem (hx u) hp, fun v hv => ?_, fun v hv => ?_, fun w => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [proj_emb_self, h2 _ hu, mul_one]
      · rw [proj_emb_ne _ _ (ne_of_mem_of_not_mem hv hu), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, proj_emb_ne _ _ hv.1, h2 v hv.2, mul_one]
    · rw [map_mul, projArch_emb, h3, mul_one]

theorem hasIw_Kmax : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → IsMaj T b → HasIw d (Kmax T b) := by
  intro D T T₀ r d b h2 hb h
  choose x k hx hk hxk using fun v => GlobalTheory.T.iwasawa_isotropic_stabiliser_finite_place D T T₀ r d h2 v (proj D.sp.cm.sig T.gram v h)
  have hS := Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig T.gram (frameLat T) h)
  obtain ⟨p, hp, e1, e2, e3⟩ := exists_stab_proj_eq d x hx hS.toFinset
  set h' := p⁻¹ * h with hh'
  have hfin : ∀ v, proj D.sp.cm.sig T.gram v h' ∈ stabLoc D.sp.cm.sig T.gram (frameLat T) v := fun v => by
    by_cases hv : v ∈ hS.toFinset
    · rw [hh', map_mul, map_inv, e1 v hv, hxk v, inv_mul_cancel_left]
      exact hk v
    · rw [hh', map_mul, map_inv, e2 v hv, inv_one, one_mul]
      exact not_not.1 fun h => hv (hS.mem_toFinset.2 h)
  set y := ofInf D.sp.cm.sig T.gram (projInf D.sp.cm.sig T.gram h') with hy
  have hyC : y ∈ GinfC T := mem_infPts.2 (projFin_ofInf _ _ _)
  obtain ⟨q, hq, k₁, hk₁, -, hyq⟩ := GlobalTheory.T.iwasawa_decomposition_isotropicStabilizer_archimedean D T T₀ r d b hb y hyC
  have hz : y⁻¹ * h' ∈ Kmax T b := by
    refine mem_levelAll.2 ⟨fun v => ?_, fun w => ?_⟩
    · rw [map_mul, map_inv, hy, proj_ofInf, inv_one, one_mul]
      exact hfin v
    · have : projArch D.sp.cm.sig T.gram w (y⁻¹ * h') = 1 := by
        rw [map_mul, map_inv, hy, projArch_ofInf, projInfArch_projInf, inv_mul_cancel]
      rw [this]
      exact one_mem _
  refine ⟨⟨p * q, mul_mem hp hq⟩, k₁ * (y⁻¹ * h'), mul_mem hk₁ hz, ?_⟩
  rw [Subgroup.coe_mk, hyq, hh']
  group

end GlobalTheory.Core.Rk.IwAd
