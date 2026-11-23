import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ClBasic

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem rc_tw_of_segments {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {r rc : IrrGL (w.adicCompletion E) → WD h} (hL : IsLExt r rc)
    (l : List (Segment (w.adicCompletion E))) (x : IrrGL (w.adicCompletion E))
    (hx : IsL (l : Multiset (Segment (w.adicCompletion E))) x.rep)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (hr : ∀ Δ ∈ l, r (Δ.first.tw χ hχ) = (r Δ.first).lpTwist (χ.comp a) (ha.smooth hχ)) :
    rc (x.tw χ hχ) = (rc x).lpTwist (χ.comp a) (ha.smooth hχ) := by
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨-, hs, ht, -⟩ := GlobalTheory.T.weil_deligne_sum_twist_compat E Ω A w h
  have h2 := GlobalTheory.T.isLanglandsClassification_twist_multisegment _ (l : Multiset (Segment (w.adicCompletion E))) x χ hχ hx
  rw [hL l x hx, hL (l.map fun Δ : Segment _ => Δ.tw χ hχ) (x.tw χ hχ) h2, segSum, segSum, hs, List.map_map, List.map_map]
  refine congrArg sumList (List.map_congr_left fun Δ hΔ => ?_)
  show ((r (Δ.first.tw χ hχ)).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) = WD.lpTwist _ _ _
  rw [(ht _ _ _ _).2, hr Δ hΔ, WD.lpTw, WD.lpTw, GlobalTheory.LocLanglands.ExtTwist.lpTwist_lpTwist_comm]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.extTw :
    UpperTheory.Zero.LLC.ExtTw := by
  intro E Ω _ _ _ _ _ A w h a ha r rc H hL
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  refine ⟨fun x s => ?_, fun x χ hχ hg => ?_⟩
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have key := rc_tw_of_segments ha hL l x h𝔪 (absPow _ (s : ℂ)) (isSmoothChar_absPow _) (fun Δ _ => by
      have h1 := H.nu _ Δ.isCusp_first s
      rw [WD.lpTw] at h1
      refine h1.trans ?_
      congr 1
      exact (ha.absPow_comp s).symm)
    refine key.trans ?_
    rw [WD.lpTw]
    congr 1
    exact ha.absPow_comp s
  · obtain ⟨𝔪, h𝔪⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
    obtain ⟨l, rfl⟩ := Quotient.exists_rep 𝔪
    have hg' := ((UpperTheory.Zero.LLC.goodSeg _).1 l x h𝔪).1 hg
    rw [lpChar_lpOfChar]
    exact rc_tw_of_segments ha hL l x h𝔪 χ hχ fun Δ hΔ => H.twist _ Δ.isCusp_first (hg' Δ hΔ) χ hχ

end
