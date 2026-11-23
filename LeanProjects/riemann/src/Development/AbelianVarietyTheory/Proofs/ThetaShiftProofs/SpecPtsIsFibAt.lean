import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicCurve
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LePreimageOfUnit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SpecialisedPointsHolomorphicQuasiPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSectionsExtendGermRingsAndSpanFibresStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecFibre

theorem specPts_isFibAt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ lin cst, IsFactor A lin cst → ∃ T' ≥ Ψ.T, IsHolTo {w : ℂ | T' < w.im} Ψ.yw ∧ ∀ w : ℂ, T' < w.im → IsFibAt A o.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w) := by
  intro hL hL2 E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hR lin cst hF
  obtain ⟨T₁, hT₁, h₁⟩ := GlobalTheory.T.specialisedPoints_holomorphic_quasiPeriodic hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR lin cst hF
  obtain ⟨T₂, hT₂, h₂⟩ := GlobalTheory.T.thetaSections_extend_germRings_and_span_fibres hL hL2 E H D l B bb S s o A y Φ Γ Ψ hA hR 1
  obtain ⟨T₀, hT₀⟩ := A.exists_isConvLine
  have hc := (GlobalTheory.HalfPoint.holomorphic_curve S Ψ.T Ψ.yT Ψ.yw Ψ.yw_eq).1
  have hle : Ψ.T ≤ max (max T₁ T₂) T₀ := le_trans hT₁ (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨max (max T₁ T₂) T₀, hle, ?_, ?_⟩
  · intro U f
    obtain ⟨ho, hd⟩ := hc U f
    have hsub : ∀ w : ℂ, max (max T₁ T₂) T₀ < w.im → Ψ.T < w.im := fun w hw => lt_of_le_of_lt hle hw
    refine ⟨?_, hd.mono fun w hw => ⟨hsub w hw.1, hw.2⟩⟩
    have h3 : IsOpen {w : ℂ | max (max T₁ T₂) T₀ < w.im} := isOpen_lt continuous_const Complex.continuous_im
    convert h3.inter ho using 1
    ext w
    exact ⟨fun h => ⟨h.1, hsub w h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · intro w hw
    have hw₁ : T₁ < w.im := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw
    have hw₂ : T₂ < w.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hw
    have hw₃ : T₀ < w.im := lt_of_le_of_lt (le_max_right _ _) hw
    have hw₀ : Ψ.T < w.im := lt_of_le_of_lt hT₁ hw₁
    obtain ⟨a1, a2, a3, a4⟩ := GlobalTheory.SpecGroup.specPts_group E H D l B bb S s o A y Φ Γ Ψ w hw₀
    obtain ⟨b1, b2, b3, b4⟩ := h₁ w hw₁
    obtain ⟨σt, -, σ₀, -, c1, -⟩ := h₂ w hw₀ hw₂
    exact ⟨a1, a2, b1, b2, b3, a3, a4, b4, fun th hth => ⟨σ₀ 0 th, c1 0 th hth⟩,
      fun th hth v => AnArc.summable_term hT₀ one_ne_zero hth hw₃ v⟩

end GlobalTheory.SpecFibre
