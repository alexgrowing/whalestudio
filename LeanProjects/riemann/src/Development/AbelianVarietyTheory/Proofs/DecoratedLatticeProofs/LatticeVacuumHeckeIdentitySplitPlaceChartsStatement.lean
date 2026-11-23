import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumHeckeIdentitySplitPlaceCharts
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ eS eT, IsSplitChart D.sp.cm.sig S.gram (frameLat S) h eS → IsSplitChart D.sp.cm.sig T.gram (frameLat T) h eT → ∀ f, VacFin ψ S T v f → (∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f) ∧ ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ T.rank, heckeVec (((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom) (KGL w T.rank) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f = ∑ j ∈ Finset.range (S.rank + 1), (if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) * (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k * (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0) • heckeVec (((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom) (KGL w S.rank) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
  first | exact @GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart | exact GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart | (intros; apply GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart <;> assumption)
