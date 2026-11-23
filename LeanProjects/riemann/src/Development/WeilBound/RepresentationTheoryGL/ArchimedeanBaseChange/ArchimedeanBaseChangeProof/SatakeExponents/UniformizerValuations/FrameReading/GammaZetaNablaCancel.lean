import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit

noncomputable section

open NumberField

namespace PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

open PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.SpectralAccumulation

def GelfInj : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℂ), (∀ m, GlobalTheory.Dec.gelfVal x m = GlobalTheory.Dec.gelfVal y m) →
    Finset.univ.val.map x = Finset.univ.val.map y

def RegDom : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n),
    RealSym (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w)) ∧ ∀ τ, GapM (mOf (fun v => PositivityTheory.RgBcC.infOf (l v).w) τ)

def Reg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → Formalism.BasicNotions.DomWeight n)
    (χ : InfinitePlace E → PositivityTheory.RgBcC.Inf n),
    (∀ v s m, GlobalTheory.Dec.gelfVal (χ v s) m = GlobalTheory.Dec.gelfVal (PositivityTheory.RgBcC.infOf (l v).w s) m) →
      RealSym (mOf χ) ∧ ∀ τ, GapM (mOf χ τ)

end PositivityTheory.Rg.BcB.F.gamma_zeta_nabla_cancel

end
