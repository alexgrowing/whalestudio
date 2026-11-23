import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameBoundSpaces.RunProps

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure RunFrame {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S)
    (T : Finset (Pl E)) : Type 1 where
  d : LocData E n
  same : RF_same F₀ d
  m : ℕ
  m_pos : 1 ≤ m
  ok : d.Ok
  mok : MLM.MOk d
  T_ne : d.T.Nonempty
  T_in : RF_T_in F₀ d
  T_le : ∀ w ∈ T, IsUnramU π w → ¬ IsSplitAt w → w ∈ d.T
  levOff : U.LevelOff F₀.Sec d.B d.KU
  fam : U.UFam F₀.Sec F₀.lam d.KU
  R : U.UMod fam d.B (d.gU m)
  i₀ : fam.ι
  comp : ∀ w ∈ F₀.Sec, IsCompU π w (fam.σ i₀ w)
  v : EuclideanSpace ℂ (Fin R.d)
  v_ne : v ≠ 0
  uv : R.u v = v
  vblk : ∀ z, diagOp R.blk z v = z i₀ • v
  choiceT : RF_choiceT F₀ d
  choiceS : RF_choiceS F₀ d
  choiceM : RF_choiceM F₀ d m

end PositivityTheory.Rg.BcB.F

end
