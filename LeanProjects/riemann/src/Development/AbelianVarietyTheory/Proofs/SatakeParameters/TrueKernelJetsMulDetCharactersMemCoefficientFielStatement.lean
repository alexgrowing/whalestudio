import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueKernelJetsMulDetCharactersMemCoefficientFiel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsEntC
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueKernelJets_mul_detCharacters_mem_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ColIn.JetsIn I → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i < B.R.m → ∀ (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ), (∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) → ∃ k : B.LL, B.embLL k = (I.rho u a i c.1 ((I.stp u a i).rep c) * I.rho' u a i c'.1 ((I.stp u a (i + 1)).rep c')) * jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) e := by
  first | exact @GlobalTheory.Mem.Col2.TC.rho_jet_mem | exact GlobalTheory.Mem.Col2.TC.rho_jet_mem | (intros; apply GlobalTheory.Mem.Col2.TC.rho_jet_mem <;> assumption)
