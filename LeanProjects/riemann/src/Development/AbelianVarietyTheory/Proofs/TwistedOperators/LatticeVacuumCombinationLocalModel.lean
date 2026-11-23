import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFunStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CombinationProducesDatumAllLocalModelsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

theorem GlobalTheory.FlatPlace.eventually_combination_of_lattice : Big fun ch => LatP ch → CombP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  intro hLat t w hw p hp j hj d c hde hc
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  obtain ⟨f₀, hf₀⟩ := exists_isVac ch.W hL hr
  have hf0 : f₀ ≠ 0 := by
    intro h0
    obtain ⟨⟨q, hq⟩, hn⟩ := hf₀.2.norm
    have := hn q hq
    rw [h0] at this
    simp [nrm2] at this
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hth := hc.2.2 f₀ hf₀.2.theta hf₀.2.lat
  have sdS := (node_isV ch.G hL (X := .top j) hj.le).sd
  have sdT := (node_isV ch.G hL (X := .top (j + 1)) hj).sd
  have hsb := d.sb
  have hth' : FinDatum.IsTheta ch.W d _ _ f₀ _ := hth
  unfold FinDatum.IsTheta at hth'
  rw [hde] at hsb hth'
  obtain ⟨Tm, hTm, hO, Φ, hΦ, hTΦ⟩ := GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun D (Kw w) p ch.W.ψ hψ _ _ _ _ sdS sdT _ _
    (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) ((hLat t w hw p hp j hj).2) f₀ d.fn _
    hf₀.2.theta hsb hth'
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w) (Y := Fin (topRank (locGrid ch.G t w) (j + 1))) (Y' := Fin (topRank (locGrid ch.G t w) j))
  have hhalf := hc.2.1
  rw [hde] at hhalf
  refine ⟨Φ, hΦ, GlobalTheory.T.combination_produces_datum_all_localModels D (Kw w) p ch.W.ψ hψ _ _ _ _ _ _ c hhalf Tm hTm O Φ hO1 ?_ ?_⟩
  · rw [hO O hO1]; exact hf0
  · rw [hTΦ, hO O hO1]
