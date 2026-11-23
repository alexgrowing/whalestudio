import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ B, C.IsB B) ∧ ∀ B, C.IsB B → IsONFr C.X (C.xB B) ∧ C.xB B ∈ C.X.dom ∧ (∀ τ, IsCartanInv (gramAt D T τ) (C.sB B τ) ∧ IsONBasis (gramAt D T τ) (C.sB B τ) (B τ) C.X.p0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) = I • zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)) ∧ (∀ (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank), zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj ((unitMap 1 (B τ) i j) a k)) : WR C.X S.rank) = letterDir C.X C.hr C.idx (C.m.e τ, (rowIdx C.hr).symm i, j)) ∧ ∀ g : GA D T, C.IsB (C.mvB g B) ∧ (∀ g', C.mvB (g' * g) B = C.mvB g' (C.mvB g B)) ∧ (g ∈ GfC T → C.mvB g B = B) ∧ (∀ τ, C.sB (C.mvB g B) τ * compAt C.θ τ (mt T g) = compAt C.θ τ (mt T g) * C.sB B τ) ∧ C.xB (C.mvB g B) = C.X.lmulC (fun σ => (compAt C.θ (C.m.e.symm σ) (mt T g)).map conj) (C.xB B) ∧ ∀ ga, IsRatOf T ga g → C.xB (C.mvB g B) = lact ga (C.xB B) := by
  first | exact @GlobalTheory.Ker.onBasis_frame_period | exact GlobalTheory.Ker.onBasis_frame_period | (intros; apply GlobalTheory.Ker.onBasis_frame_period <;> assumption)
