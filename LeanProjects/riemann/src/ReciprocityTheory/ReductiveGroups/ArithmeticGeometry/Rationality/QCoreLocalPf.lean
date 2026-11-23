import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QuotShiftPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FreeQuotPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalLengthAverage

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain Module

theorem qcoreLocal : QCoreLocalStatement := by
  intro hLD hQL K K₁ V _ _ _ _ _ _ _ _ _ _ M hM hspan W θ hθ c hc be s hbe hs hint
  refine ⟨LocalQuotientRank.detCT_ne_zero (M := M) (hM := hM) (hspan := hspan) (W := W)
    (θ := θ) (hθ := hθ) (c := c) (hc := hc), ?_⟩
  intro la
  obtain ⟨ℓ, hℓ, hle⟩ := LocalLengthAverage.average (la := la)
    (L := lenLa la (QuotMW M W ⧸ Submodule.span (𝓞 K)
      (Set.range fun j => (Submodule.Quotient.mk (θ j) : QuotMW M W))))
    (D := detCT c θ) (t := fun w => ∑ i, s i w)
    (ρ := Module.finrank (𝓞 K) (QuotMW M W)) (B := be la) (by
      intro w hw

      obtain ⟨n, hn, hnle⟩ := LocalLengthAverage.lenW_bound (hL := hQL) (M := M) (hM := hM)
        (hspan := hspan) (W := W) (θ := θ) (hθ := hθ) (c := c) (hc := hc) (w := w)
        (s := fun i => s i w) (β := (w.asIdeal.ramificationIdx (𝓞 K) : ℝ) * be la)
        (hint := fun i m hm hne => hint la w hw i m hm hne)
      refine ⟨n, ?_, ?_⟩
      · rw [← hLD K K₁ V M hM hspan W θ la w hw]
        exact hn
      · simpa only using hnle)
  refine ⟨ℓ, hℓ, ?_⟩
  simpa only [nnFun] using hle

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
