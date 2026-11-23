import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDataSizedFamily
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealDataWeightVectorFamilyCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDataSizedFamilyStatement

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
theorem GlobalTheory.PrimIn.holds_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  intro hP hHL eps heps
  obtain ⟨x₀, hx⟩ := _root_.GlobalTheory.T.real_data_weight_vector_family_core_alt hP hHL eps heps
  refine ⟨x₀, ?_⟩
  intro X px I hX Tw Wt z L hLe hx0 hS hPar hB hG hM hRT hI
  have h := hx z.core z.R z.F z.geo.κ z.geo.v₀ z.geo.O L hLe hx0 hS hPar hB hG hM hRT
  obtain ⟨hcore, -, -, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hB.char hB.ex
  have hschur := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 z.R.toRealDat
  obtain ⟨fw, hbar⟩ := hG.fw
  have hconj := GlobalTheory.T.algebraicForm_norm_eq_at_conjugateEmbedding z.core z.R.toRealDat z.F.lv2 z.geo.κ z.geo.v₀ hcore hschur fw hbar hG.unif
  have hlev : z.R.toRealDat.LLevelW z.F.lv2 :=
    GlobalTheory.LevelForms.levelW_of_irr _ _ hB.ok.ok2.irr hG.unif hB.char.base.models.HW
  exact ⟨h.1, ⟨hB.ex, hconj, hlev, hI⟩, hB.ok, h.2.1⟩
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_data_sized_family_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  first | exact @_root_.GlobalTheory.PrimIn.holds_of_ties_alt | exact _root_.GlobalTheory.PrimIn.holds_of_ties_alt | (intros; apply _root_.GlobalTheory.PrimIn.holds_of_ties_alt <;> assumption)
end
