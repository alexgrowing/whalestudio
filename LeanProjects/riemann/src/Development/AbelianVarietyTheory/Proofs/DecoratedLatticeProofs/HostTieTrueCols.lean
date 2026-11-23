import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HostFieldsPrimesTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem host_tie_trueCols : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)), GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (numDatumOfParameters (I.rec7 l Z) L) (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) (B.primes X) := by
  intro B X I h l Z L
  have hX : B.fields.Ok := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.1
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩ := host_fields_primes_ties I h hX l Z
  refine ⟨rfl, rfl, rfl, h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, fun _ => rfl, HEq.rfl⟩
  · rw [h9]
    rfl
  · intro i; rw [h10]; rfl
end GlobalTheory.CoreHt
