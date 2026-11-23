import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.IrreducibilityOfTheoremThree
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

noncomputable section

namespace GlobalTheory.NRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

structure Hypotheses₂ : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geo : GlobalTheory.Published.GeometricLemma
  unl : GlobalTheory.Published.UnlinkedProductIrreducible
  mp : GlobalTheory.Published.DepthZeroJacquetInjective
  howe : GlobalTheory.Published.HoweDualityGL
  js : GlobalTheory.Published.JacquetShalika
  fin : GlobalTheory.Published.AutomorphicFormsFiniteGL
  temp : GlobalTheory.Published.CohomologicalCsdTempered
  gal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  car : GlobalTheory.Published.LocalGlobalAboveL
  clo : GlobalTheory.Published.RegularAlgebraicPurity
  art : GlobalTheory.Published.GlobalArtinReciprocity
  chA : GlobalTheory.Published.HeckeLAdicCharacterAbove
  chP : GlobalTheory.Published.HeckeLAdicParameterAbove
  berger : GlobalTheory.Published.DeRhamPotSemistable
  cheb : GlobalTheory.Published.ChebotarevDegreeOne

structure RowsA (D : D7) : Prop where
  tieLab : SumRepresentations.tieLab D
  hecke : HeckeSplitOne D
  tie0 : SumRepresentations.tie0 D
  a2 : SumRepresentations.adm2 D
  an1 : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut
  an2 : T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut
  a5 : SumRepresentations.adm5 D
  temp : SumRepresentations.adm7 D
  g4p : SumRepresentations.CuspidalGaloisUnramified D
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)

structure RowsB (D : D7) : Prop where
  rowSize : RowSize D
  a3 : SumRepresentations.adm3 D
  a4 : SumRepresentations.ArchimedeanSignatureMatching D
  thetaOne : ThetaOne D

structure RowsC (D : D7) : Prop where
  c4b : JointOccurrenceCondition D
  rho : GlobalDatumResidualRepCondition D
  dz : GlobalDatumDepthZeroCondition D
  parUp : ∀ i, ParUpRec D.nd D.naut i
  downMem : ∀ i, DownMemRec D.nd D.naut i
  goodPart : ∀ i, GoodPartRec D.nd D.naut i

def LamUsed (D : D7) : Prop :=
  ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → ∀ j : Fin D.R.m, LamPos D μ (j.1 + 1)

def PartsGive (D : D7) : Prop :=
  SumRepresentations.AdmAt D → SumRepresentations.tieLab D → RowSize D → HeckeSplitOne D → (∀ i : D.nd.Loc, LamPos D (D.nd.mu i) (D.nd.j i)) →
    ThetaOne D → SumRepresentations.CuspidalGaloisUnramified D → SumRepresentations.Conclusion1 D

def GoodIdempotentFixesLocalisationForms (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par), ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
    D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F

def GoodIdempotentReadsAsGoodTypeProjector {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) : Prop :=
  ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) y,
    X.R.extV j (X.tupT μ) y = X.fn hμ j f →
      (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f = f ↔ GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y)

structure Tied (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Type 1 where
  P : GlobalTheory.NPin.Pin hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X

structure Named {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t

structure Inputs (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Type 1 extends toRowSideFamily : Tied hL D where
  named : Named toRowSideFamily

structure Rows (D : D7) : Prop where
  a : RowsA D
  b : RowsB D
  c : RowsC D
  typeNZ : ∀ i, TypeNZRec D.nd D.naut i
  rank : ∀ L : SizeData₂ D, TwistedPlaces.adm3 L

theorem an_iff {D : D7} : (T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut ↔ IsobaricCuspidalStrongMultiplicityOne D.nd D.naut) ∧ (T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut ↔ IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut) :=
  ⟨Iff.rfl, Iff.rfl⟩

theorem analyticRigidity_of_admissible {D : D7} (h : SumRepresentations.adm5 D) : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut ∧ T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut := ⟨h.1, h.2.1⟩

theorem LamUsed.at {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem LamUsed.loc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  h.at (Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩)
    (D.nd.j_range i).1 (D.nd.j_range i).2

theorem goodIdempotentFixes_of_onlySeriesOfLabelActs {D : D7} (h : GlobalTheory.TypeLeaf.SerLoc D) : GoodIdempotentFixesLocalisationForms D := fun i σ' F hF hg =>
  (PlaceLabelTeichmuller.idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => h i σ' k v f F hF hf).1 hg

theorem goodIdempotent_of_goodProjector {D : D7} (h : ArithmeticCylinders.Conclusion4 D) : GoodIdempotentFixesLocalisationForms D :=
  fun i σ' F hF hg => (h.2.2.2.2.1 _ _ (D.nd.j_range i).1 (D.nd.j_range i).2 σ' F hF).1 hg

theorem partsGive_of {D : D7} (h1 : SumRepresentations.AdmAt D → SumRepresentations.ReducedFamilyProposition D)
    (h2 : SumRepresentations.AdmAt D → RowSize D → HeckeSplitOne D → (∀ i : D.nd.Loc, LamPos D (D.nd.mu i) (D.nd.j i)) → ThetaOne D →
      SumRepresentations.ReducedParameterProposition D) : PartsGive D := fun a t s hk l th g =>
  ⟨(SumRepresentations.proposition_families_iff D a.1.2.2.2.2.2.2 a.1.2.1).2 (h1 a), g, (SumRepresentations.proposition_parameters_iff_reduced D t).2 (h2 a s hk l th)⟩

namespace Inputs

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (I : Inputs hL D)
include I

theorem hypO : SumRepresentations.hypO D := I.named.hypO

theorem c1 : GlobalDatumCompatibility D := I.named.c1

theorem bc : SphericalInertData.Conclusion1 D := I.named.bc

theorem lam : LamUsed D := I.named.lam

theorem isot : SumRepresentations.adm8 D := I.named.isot

theorem ser : GlobalTheory.TypeLeaf.SerLoc D := I.named.ser

theorem typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ I.X.R j t := I.named.typeNZ

theorem e0loc : GoodIdempotentFixesLocalisationForms D := goodIdempotentFixes_of_onlySeriesOfLabelActs I.ser

set_option linter.unusedSectionVars false in

theorem mtPar : MtParTie D.nd D.naut D.ntypes := D.mtpar_tie

theorem adm1 : SumRepresentations.adm1 D := base_change_automorphic_of D I.bc I.c1

theorem admAt (a : RowsA D) (b : RowsB D) : SumRepresentations.AdmAt D :=
  ⟨⟨a.tie0, I.hypO, I.adm1, a.a2, b.a3, b.a4, a.a5⟩, a.temp⟩

theorem Conclusion1 (h : PartsGive D) (a : RowsA D) (b : RowsB D) : SumRepresentations.Conclusion1 D :=
  h (I.admAt a b) a.tieLab b.rowSize a.hecke I.lam.loc b.thetaOne a.g4p

end Inputs

theorem nonempty_inputs_iff {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} :
    Nonempty (Inputs hL D) ↔ ∃ T : Tied hL D, Named T :=
  ⟨fun ⟨I⟩ => ⟨I.toRowSideFamily, I.named⟩, fun ⟨T, h⟩ => ⟨⟨T, h⟩⟩⟩

example (D : D7) (h : ∀ μ j f, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = f) (h1 : ∀ μ j σ, D.what₂.lamP μ j σ = 1) :
    LamUsed D := fun μ _ j σ =>
  ⟨fun f _ => by rw [h, h1, Complex.ofReal_one, one_smul], fun _ => by rw [h1]; exact one_pos⟩

example (D : D7) (j : Fin D.R.m) (σ : D.what₂.FT) (hσ : D.what₂.isot (j.1 + 1) σ ≠ ⊥)
    (h0 : D.what₂.thetaP D.what₂.mu0 (j.1 + 1) = 0) : ¬ LamUsed D := by
  intro h
  obtain ⟨f, hf, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h1 := (h _ (Or.inl rfl) j σ).1 f hf
  have hl : ((D.what₂.lamP D.what₂.mu0 (j.1 + 1) σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ((h _ (Or.inl rfl) j σ).2 hσ).ne'
  rw [h0, LinearMap.zero_apply] at h1
  exact hne ((smul_eq_zero.1 h1.symm).resolve_left hl)

example {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) {μ} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m)
    (f : D.what₂.Mt μ (j.1 + 1)) : ∃ y, T.X.R.extV j (T.X.tupT μ) y = T.X.fn hμ j f := (T.X.IL.jMt μ hμ j f).2.1

example (D : D7) (i : D.nd.Loc) (σ' : D.ntypes.Par) (F) (hF : F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ') (h0 : F ≠ 0)
    (hg : D.ntypes.goodPar σ') (hk : D.what₂.eMt (D.nd.mu i) (D.nd.j i) F = 0) : ¬ GoodIdempotentFixesLocalisationForms D := fun h =>
  h0 ((h i σ' F hF hg).symm.trans (by rw [← D.nStage_trivialCharacter_compat.2]; exact hk))

end GlobalTheory.NRows

end
