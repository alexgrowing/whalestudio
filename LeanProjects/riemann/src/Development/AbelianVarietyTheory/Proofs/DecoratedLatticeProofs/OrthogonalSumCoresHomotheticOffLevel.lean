import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleOfSupportedRankOneUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeTraceAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M M' : Lat S) (LA : Lat A) (LL : Lat L) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D) (a₀ : GA D A), IsLineVec L ζ → IsSelfDualC L LL → OrthAt o M LA LL v → TraceAt o a₀ LA M' v → SplitsAt o M' v → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' v := by
  intro D S A L o ζ M M' LA LL μ T v a₀ hζ hLL hM hTr hSp hμ hline hn hT
  obtain ⟨Λ', hΛ', hmem⟩ := GlobalTheory.T.exists_selfDual_lineLatticeTrace_at_place D S A L o ζ M' μ T v hζ hμ hline hn hT
  obtain ⟨γ, hγ, hmove⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D L v _ Λ' (GlobalTheory.FinPl.TamePlaces.tame D v)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D L LL v hLL) hΛ'
  obtain ⟨c, hc, hc', hγc⟩ := GlobalTheory.T.exists_normOneIdele_of_supported_rankOneUnitary D L v γ hζ.1 hγ
  obtain ⟨a, ha, hma⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A v (cA D c) hc'
  refine ⟨a, c, ha, hc, ?_⟩
  intro y hy
  have hAy : ∀ i, (o.pA *ᵥ y) i ∈ idAt D (· = v) := GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy
  have hBy : ∀ i, (o.pB *ᵥ y) i ∈ idAt D (· = v) := GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy
  have hcBy : ∀ i, (c • (o.pB *ᵥ y)) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hBy i)
  have hcc : c * cA D c = 1 := hc.1
  have key : c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y) =
      o.jA *ᵥ (Formalism.L2.Theta.mt A a₀ *ᵥ (o.pA *ᵥ y)) + o.jB *ᵥ (c • (o.pB *ᵥ y)) := by
    rw [o.mt_emb, GlobalTheory.FinPlLoc.mt_mul, hma, GlobalTheory.FinPlLoc.mt_one]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_smul, smul_add, smul_smul, hcc, one_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hz : ∀ i, (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) i ∈ idAt D (· = v) := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  have hpA : o.pA *ᵥ (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) = Formalism.L2.Theta.mt A a₀ *ᵥ (o.pA *ᵥ y) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_mulVec _ o.pA o.jA, Matrix.mulVec_mulVec _ o.pA o.jB, o.pA_jA, o.pA_jB,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  have hpB : o.pB *ᵥ (c • (Formalism.L2.Theta.mt S (o.emb (a₀ * a, 1)) *ᵥ y)) = c • (o.pB *ᵥ y) := by
    rw [key, Matrix.mulVec_add, Matrix.mulVec_mulVec _ o.pB o.jA, Matrix.mulVec_mulVec _ o.pB o.jB, o.pB_jA, o.pB_jB,
      Matrix.one_mulVec, Matrix.zero_mulVec, zero_add]
  rw [hM y, hSp _ hz, hpA, hpB, ← hTr _ hAy, ← hmem _ hcBy, hmove _ hBy, hγc, Matrix.smul_mulVec,
    Matrix.one_mulVec]
