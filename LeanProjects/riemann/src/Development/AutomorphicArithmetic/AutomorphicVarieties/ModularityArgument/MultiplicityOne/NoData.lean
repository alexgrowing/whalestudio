import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalWeak
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.G UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Mult

theorem onlyPre (hW : GalWeak 4) {E : Type} [Field E] [NumberField E] [IsCMField E] (hunr : GlobalTheory.BCT.Unr E) {n : ℕ} (hn : 1 ≤ n)
    (hn4 : n ≤ 4) (π : CuspSub E n) (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (D : Pre E n) (r : D.Reg)
    (t : D.ThetaStable) (s : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) :
    One D π := by
  obtain ⟨D₀, hone, hr⟩ := onePre E n hn π hreg (csdDisc E n hn π hd)
  have hs := oneSat E n hn π D₀ hone
  have ht : D₀.ThetaStable := (csdSat E n hn π hd).mono fun w ⟨B, a, b⟩ => ⟨B, (hs w B).1 a, fun u hu => (hs u _).1 (b u hu)⟩
  obtain ⟨e, he⟩ := Rig.locRigid_holds E n D D₀ r hr (galStep_le hW E hunr n hn4 D D₀ r hr t ht
    (s.mono fun w hw hx => (hw hx).imp fun B hB => ⟨hB.1, (hs w B).1 hB.2⟩))
  exact onlyOne cuspOrTwo notTwo oneSat E n hn π D D₀ e r hone he

end UpperTheory.V.Z.Mult
