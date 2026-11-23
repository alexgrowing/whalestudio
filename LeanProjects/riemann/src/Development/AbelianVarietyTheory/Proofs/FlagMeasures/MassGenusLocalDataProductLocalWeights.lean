import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProductStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometriesEmbedProdLocalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalLatticeOverLocalInnerDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometryExtPreservesCompletionsAeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalIsometriesFixingFramesConjStabilizStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeStabilisersCommensurableAlmostEverywStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbitsStatement

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HL

namespace GlobalTheory.Unfold

theorem mass_genus_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR d0 hd0 hΛ
  obtain ⟨φ, hφi, hφE⟩ := GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨Λ₀, hLO⟩ := GlobalTheory.T.exists_globalLattice_over_localInnerData D Z FP d0 hd0 hΛ
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    have hm : D.R.m = 2 * D.R.rS + 2 := by
      have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
    rw [finrank_Vp]; unfold Ranks.r; omega
  have hact : ∀ p : PlF D, ∃ act : MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : ↥(FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d :=
    fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (hrk p) (hR p)
  choose act hMv hSt using hact
  letI : ∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)) := act
  have hMv' : ∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d' := hMv
  have hSt' : ∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d := hSt
  obtain ⟨hc0, hfin, hdd⟩ := GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere D X Y u u' F F' w hw hG Z FP hB hR hMv' hSt' Λ₀ d0 hLO
  have hlat : Submodule.IsLattice D.host.E Λ₀ := hLO.1
  obtain ⟨V1, hV1, hmain⟩ := GlobalTheory.T.mass_genus_restricted_product (fun p => ↥(FP p).UW0) (fun p => LocNG.Datum (FP p))
    (fun p => (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ↥(FlagPairStabilizer F F') φ hφi
    (GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat)
    (GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat)
    (GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat) d0 hc0 hfin
  refine ⟨V1, hV1, fun d hd hfd => ?_⟩
  have h3 := hdd d hd
  rw [GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits D X Y u u' F F' w hw hG Z FP hB hR φ hφE hφi hMv' d]
  have hm2 := hmain d (fun p => ⟨(h3 p).1, (h3 p).2.1⟩) hfd
  have e : (∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) = ∏ᶠ p, invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) := finprod_congr fun p => ((h3 p).2.2).symm
  refine hm2.trans ?_
  rw [e]

end GlobalTheory.Unfold
