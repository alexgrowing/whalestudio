import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem chainPar_inj_at (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : chainPar c B k w = chainPar c B' k w) : B w = B' w := by
  induction k with
  | zero => simpa [chainPar] using h
  | succ k ih =>
    apply ih
    rw [chainPar_succ, chainPar_succ] at h
    simp only [stepPar] at h
    have h2 := add_right_cancel h
    exact Multiset.map_injective (mul_right_injective _) h2

theorem chainPar_inj : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)),
    chainPar c B k w = chainPar c B' k w → B w = B' w :=
  chainPar_inj_at

end GlobalTheory.ChainOnto
