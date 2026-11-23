import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlace
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace UpperTheory.Lit.Sw47

open GlobalTheory.BottomRallis

def FockAnisoLe (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → A.rank < B.rank → B.rank ≤ 2 * A.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (GlobalTheory.ThetaMean.thetaMean omh mH φ)

def FockAnisoGt (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), 1 ≤ A.rank → 2 * A.rank < B.rank → wittIndex B = 0 →
  ∀ (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a →
  ∀ (θ : InfFam D) (sS : RealMat (dblSp A)) (sB : RealMat B), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D B τ) (sB τ)) →
    (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * sS τ =
      sS τ * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k)) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ mH : Measure (GA D B), mH.IsHaarMeasure →
  ∀ φ : WO (dblSp A) B → ℂ, IsFockVec ψ θ (dblSp A) B sS sB φ →
    (∀ g, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ B) fun h => thetaKO omh g h φ) (autMeasure B mH)) ∧
    GlobalTheory.Eis.EisValueAt A (flat A a (swSec A B omh ν 𝓕 φ) (sZero A B)) (sZero A B) (GlobalTheory.ThetaMean.thetaMean omh mH φ)

theorem fockAniso_of_ranges (D : D7) (h1 : FockAnisoLe D) (h2 : FockAnisoGt D) : SiegelWeilFockAniso D := by
  intro ψ A B hA hAB hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  rcases le_or_gt B.rank (2 * A.rank) with h | h
  · exact h1 ψ A B hA hAB h hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  · exact h2 ψ A B hA h hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF

theorem fockAniso_le (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent) : ∀ D, FockAnisoLe D := by
  intro D ψ A B _hA hab hle hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hw : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 := by rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hB
  exact hSW D ψ A B hab hle (by omega) χB omh homh a hmaj hI θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF

theorem re_sZero_gt {D : D7} (A B : HSp D) (h : 2 * A.rank < B.rank) : (A.rank : ℝ) / 2 < (sZero A B).re := by
  have e : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
    simp [sZero]
  rw [e]
  have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast h
  linarith

theorem fockAniso_gt : GlobalTheory.Published.WeilSiegelFormulaUnitary → ∀ D, FockAnisoGt D := by
  intro hWeil D ψ A B ha hab hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hφ := hF.1
  have hK := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hBc (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hwitt : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact Or.inl hB
  obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt
  obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
  refine ⟨hint, ?_⟩
  have hsum : ∀ g, GlobalTheory.Eis.eis A (GlobalTheory.SiegelFormula.swSection A B ν 𝓕 omh φ) g =
      ⨍ q, descend (GQ B) (fun h => thetaKO omh g h φ) q ∂autMeasure B mH := fun g =>
    ((hser hab ν 𝓕 hcov).2 g).2
  have hmem := GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries GlobalTheory.weilRepresentationUnitaryPair D ψ A B χB omh homh ν 𝓕 hcov φ hφ a hK
  have hv := GlobalTheory.Eis.SphConv.eisValueAt_flat hI hmem (GlobalTheory.Eis.sphConv D A a hI) (isHeckeCharacter_inv_of_isHeckeCharacter homh.hecT)
    (re_sZero_gt A B hab)
  have he : GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) = GlobalTheory.ThetaMean.thetaMean omh mH φ := by
    funext g
    rw [← swSection_eq_swSec]
    exact hsum g
  rw [he] at hv
  exact hv

def FA : Prop := ∀ D : D7, GlobalTheory.BottomRallis.SiegelWeilFockAniso D

theorem fa_of (hC : GlobalTheory.Published.SiegelWeilUnitaryConvergent) (hW : GlobalTheory.Published.WeilSiegelFormulaUnitary) : FA :=
  fun D => fockAniso_of_ranges D (fockAniso_le hC D) (fockAniso_gt hW D)

end UpperTheory.Lit.Sw47
