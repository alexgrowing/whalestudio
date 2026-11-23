import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwDat.Is

theorem stp_top_idx_eq {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)
    (b b' : (I.stp u a B.R.m).β) : b = b' := by
  show (b : Idx I.sel (I.tup a) (I.idx a) B.R.m) = b'
  obtain ⟨x, hx⟩ := b
  obtain ⟨y, hy⟩ := b'
  have h1 : x = none := by simpa using hx
  have h2 : y = none := by simpa using hy
  subst h1; subst h2; rfl

theorem chOf_top_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (c₀ : (I.stp u a B.R.m).Cl) (β : Ch₀ B.R.m), A.chOf B.R.m c₀ = β := by
  intro B X I _ _ l Z u a Ch₀ A hA c₀ β
  obtain ⟨c, rfl⟩ := hA.chOf_onto B.R.m le_rfl β
  exact ((hA.reads B.R.m le_rfl).key c₀ c).2
    ⟨stp_top_idx_eq I u a _ _, GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _⟩

end GlobalTheory.AdForm.TwDat.Is
