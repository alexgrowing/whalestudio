import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SiegelWeilFock
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramAtP
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero

noncomputable section
namespace GlobalTheory.Core.Rk.IP.FockModel
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem of_all (D : D7) (h : SiegelWeilAll D) : SiegelWeilFock D :=
  fun ψ A B ha hab hw χB omh hom a hmaj θ sS sB hθ hS hB hc ν 𝓕 hν mH hm φ hφ =>
    h ψ A B ha hab hw χB omh hom a hmaj ν 𝓕 hν mH hm φ hφ.1
      (isKFinVec_of_isFockVec D ψ θ _ B 1 χB omh sS sB hom hθ hS hB _ (isCompact_Khat A a) hc φ hφ)

theorem resEta_one_dbl (A : HSp D) {χ : (AE D)ˣ →* Circle} {k : ℕ} (hr : ResEta D χ k) : ResEta D 1 (dblSp A).rank :=
  ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (A.rank + A.rank)
    rw [← two_mul, pow_mul, h4, one_pow]⟩

def Hyp (A B : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B) (a : GL (Fin A.rank) (AE D))
    (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (mH : Measure (GA D B)) (φ : WO (dblSp A) B → ℂ),
    IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ IsMaj A a ∧ IsInfFam θ ∧
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) ∧ (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) ∧
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) ∧
    IsCovolOne (ratL B A) ν 𝓕 ∧ mH.IsHaarMeasure ∧ IsFockVec ψ θ (dblSp A) B sS sB φ ∧ swSec A B omh ν 𝓕 φ 1 = 1

theorem hyp (A B : HSp D) (hA : HSpace.SigOK A) (hB : HSpace.SigOK B) (ha : 1 ≤ A.rank) (hab : A.rank < B.rank) :
    Hyp A B := by
  obtain ⟨ψ, θ, χA, χB, sA, sB, cA, a, om, ν, 𝓕, Φ, hP, hΦ, h1, -⟩ := Model.exists_pair_unram A B hA hB ha
    (t := B.rank - A.rank) (by omega) (by omega) _ _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A)
    (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat B)
  obtain ⟨-, -, -, hθ, -, -, hsA, hsB, -⟩ := hP.setting
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨omh, homh⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hP.weil.std (dblSp A) B 1 χB ⟨η, hη⟩
    ⟨continuous_const, fun _ => rfl⟩ hP.weil.hecT (resEta_one_dbl A hP.weil.resT) hP.weil.resT
  obtain ⟨c1, c2⟩ := Cartan.cartan_dbl D θ A sA a hθ hsA hP.maj_eq
  refine ⟨ψ, χB, omh, a, θ, _, sB, ν, 𝓕, Measure.haar, delta A B Φ Φ, homh, hP.maj, hθ, c1, hsB, c2, hP.covol,
    inferInstance, GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ A B sA sB hP.weil.std hθ Φ Φ hΦ hΦ, ?_⟩
  have e1 : omh (1, 1) = 1 := map_one omh
  have e2 : om (1, 1) = 1 := map_one om
  simp only [wcoef, e2, Module.End.one_apply] at h1
  simp only [swSec, e1, Module.End.one_apply, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta, h1]

theorem hyp_definite (D : D7) {n m : ℕ} (hn : 1 ≤ n) (hm : n < m) :
    ∃ A B : HSp D, A.rank = n ∧ B.rank = m ∧ wittIndex B = 0 ∧ Hyp A B :=
  ⟨Inh.P D n, Inh.P D m, rfl, rfl, wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.ThetaMean.Model.isAniso_posSpace _),
    hyp _ _ (Examples₂.posSpace_sigOK _ _) (Examples₂.posSpace_sigOK _ _) hn hm⟩

theorem hyp_indefinite (D : D7) : ∃ A B : HSp D, 1 ≤ A.rank ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
    A.rank + wittIndex B < B.rank ∧ (∀ τ, B.sig τ = (8, 1)) ∧ HSpace.SigOK B ∧ Hyp A B := by
  have h := Examples₂.lorentzSpace_signature_ok (E := D.host.E) Examples₂.star_isIntegral
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral) ≤ 1 :=
    (WittSignature.wittIdx_le_signature _ _ h D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  refine ⟨Inh.P D 5, Examples₂.lorentzSpace Examples₂.star_isIntegral, (by decide : 1 ≤ 5), (by decide : 5 < 8 + 1),
    (by decide : 8 + 1 ≤ 2 * 5), ?_, fun _ => rfl, h,
    hyp _ _ (Examples₂.posSpace_sigOK _ _) h (by decide : 1 ≤ 5) (by decide : 5 < 8 + 1)⟩
  rw [← GlobalTheory.RallisIP.wittIdx_eq_wittIndex]
  exact (Nat.add_le_add_left h1 5).trans_lt (by decide : 5 + 1 < 8 + 1)

theorem conclusion_zero (A B : HSp D) (hab : A.rank < B.rank) (omh : WRep (dblSp A) B) (a : GL (Fin A.rank) (AE D))
    (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (mH : Measure (GA D B)) :
    Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 0) (sZero A B)) (sZero A B) (ThetaMean.thetaMean omh mH 0) := by
  have := GlobalTheory.ThetaMean.Model.conclusion_zero A B omh a ν 𝓕 mH
  rwa [if_pos hab, one_smul] at this

end GlobalTheory.Core.Rk.IP.FockModel

end
