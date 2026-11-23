import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SupercuspidalLanglands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GammaMultiplicativeGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecialStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.ExtDual

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {r : IrrGL (w.adicCompletion E) → WD h}

theorem nu_eq (H : CuspLaws a ha e r) {x : IrrGL (w.adicCompletion E)} (hx : x.IsCusp) (s : ℝ) :
    r (x.nu s) = (r x).lpTw s := by
  rw [IrrGL.nu, H.twist x hx, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem summand_dual (H : CuspLaws a ha e r) {Δ Δ' : Segment (w.adicCompletion E)} (hd : SegDual Δ Δ') :
    ((r Δ'.first).lpTw (((Δ'.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ'.len) =
      (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).lpDual := by
  obtain ⟨hl, hD⟩ := hd
  have hc : (Δ.first.nu ((Δ.len : ℂ) - 1)).IsCusp := Δ.isCusp_first.nu _
  have e1 := H.dual _ _ hc Δ'.isCusp_first hD
  have e2 : Δ.first.nu ((Δ.len : ℂ) - 1) = Δ.first.nu (((Δ.len : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [e2, nu_eq H Δ.isCusp_first] at e1
  obtain ⟨hS, hT, hP⟩ := GlobalTheory.T.weilDeligneParam_dual_listSum_absTwist_special E Ω A w h
  rw [e1, hl, hP, hT, hT, WD.lpTw_add]
  congr 2
  ring

theorem map_summand_dual (H : CuspLaws a ha e r) {l l' : List (Segment (w.adicCompletion E))}
    (hF : List.Forall₂ SegDual l l') :
    l'.map (fun Δ => ((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)) =
      l.map (fun Δ => (((r Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).lpDual) := by
  induction hF with
  | nil => rfl
  | cons hd _ ih => rw [List.map_cons, List.map_cons, ih, summand_dual H hd]

end GlobalTheory.LocLanglands.ExtDual
