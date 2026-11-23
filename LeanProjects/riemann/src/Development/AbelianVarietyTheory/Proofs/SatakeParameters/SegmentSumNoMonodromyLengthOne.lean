import Mathlib
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NoMonodromyOfMemWeilDeligneListSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaAndZelevinskyPolynomialRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMono0LpCharLpSp

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SegSumOne

theorem segSum_of_mono0 : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (rc : IrrGL (w.adicCompletion E) → WD h), UpperTheory.Zero.LLC.IsRecT h rc →
    ∀ (l : List (Segment (w.adicCompletion E))), (segSum rc l).mono0 →
      (∀ Δ ∈ l, Δ.len = 1) ∧ segSum rc l = sumList (l.map fun Δ => rc Δ.first) := by
  intro E Ω _ _ _ _ _ A w h rc hrc l hm
  obtain ⟨a, ha, H⟩ := hrc
  have hlen : ∀ Δ ∈ l, Δ.len = 1 := by
    intro Δ hΔ
    have hirr : IsIrrWD ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)) := by
      rw [← H.nu]; exact (H.cusp _ (Δ.isCusp_first.nu _))
    have hmi : (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len)).mono0 :=
      GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm _ (List.mem_map.2 ⟨Δ, hΔ, rfl⟩)
    have hpos := Δ.len_pos
    by_contra hne
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by omega) hmi
  refine ⟨hlen, ?_⟩
  unfold segSum
  congr 1
  refine List.map_congr_left fun Δ hΔ => ?_
  rw [hlen Δ hΔ, GlobalTheory.SegLen.lpChar_lpSp_one']
  simp [WD.lpTw_zero]

end GlobalTheory.SegSumOne
