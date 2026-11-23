import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedNefFX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefAmpleFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights

theorem nefOnFibres_of_generatesOn :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ)
      (a : K → ℤ) (q : ℕ) (w : Fin q → Ω), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro K _ ι _ Ω _ y D a m w _ _ hw hg W hW hPW hchar hdim
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have : W.IsPrime := hW.1
  set ℓ := charOf W with hℓdef
  have hℓ : ℓ.Prime := SemiampleNefAlt.charOf_prime hchar
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hgen : KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a :=
    (GenOnFibres.proof K ι Ω y _ m w hw hg).2 ℓ hℓ
  have hpW : ((ℓ : ℕ) : MRing ι) ∈ W := by
    have h := GroundTheory.Heights₂.Heights.Inter.C_charOf_mem W
    rwa [map_natCast] at h
  set W' := W.map (NefAmpleFibreAlt.red (ι := ι) ℓ) with hW'def
  have hker := NefAmpleFibreAlt.ker_red_le (ι := ι) ℓ hpW
  have hW'proj : IsProjVarF W' 1 := by
    refine ⟨⟨Ideal.map_isPrime_of_surjective (NefAmpleFibreAlt.red_surjective ℓ) hker,
      NefAmpleFibreAlt.isMultiHomogIdeal_map _ hW.2.1, fun k => ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := hW.2.2 k
      refine ⟨i, fun h => hi ?_⟩
      rw [← NefAmpleFibreAlt.mem_map_red_iff ℓ hpW]
      simpa [NefAmpleFibreAlt.red] using h
    · rw [NefAmpleFibreAlt.ringKrullDim_red ℓ hpW, hdim, add_comm]
  have hle : fibreIdeal ℓ y ≤ W' := Ideal.map_mono hPW
  have hI := GeoNumTarget.isFieldIntersection_intNum (K := K) (ι := ι) ℓ
  have hnef := GeneratedNefF.proof (ZMod ℓ) K ι _ (fibreIdeal ℓ y) a hI hgen W' hW'proj hle
  have hgeo := geoNumStatement ι ℓ _ hI W 1 (fun _ => a) hW hpW hW'proj
  rw [hgeo]
  convert hnef using 2
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.Giv
