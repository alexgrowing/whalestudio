import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCoreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoExV
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.GeoExProof

set_option maxHeartbeats 2000000 in

theorem geoExV_of_top : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D) [Algebra C.Q.c.F D.what₂.LL] (F : Face D A3.A), VolTieG D → LawsJ C → LawsCore C.toCore → AlgTie C → Finite T0 → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Mem.R3.GeoExV A3 C F := by
  intro hRD D G _ _ Pl0 I0 T0 A3 C _ F hVol hL hLC hA hT hVS hn R cG hVal hPre _hlev hpb hK
  obtain ⟨dict, mu, chiW, x₀, cE, nW, FW, B, -, -, hFired, -, -, hPre', hchi, hU, -, -⟩ :=
    GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core hRD D G Pl0 T0 A3.A C R hVol hL hLC hA hpb hPre hK.valKs hK.frameKs hVal hT hK.guard hVS hn
  refine ⟨dict, mu, chiW, x₀, cE, nW, FW, hchi, ⟨B⟩, fun i x => ?_⟩
  have hHW := hPre'.models.HW
  obtain ⟨m, a, f, hf⟩ := (hFired.1 i).2.2 x
  have hm : (1 : ℂ) • ((updFW R nW FW).HW i (sg0 D A3.A)).e (R.thG i A3.A.μ0 (jVx (updFW R nW FW) i A3.A.μ0 x)) ∈
      (updFW R nW FW).Wall i (sg0 D A3.A) :=
    ((updFW R nW FW).Wall i (sg0 D A3.A)).smul_mem 1 ((hHW i _).2.1.le (LinearMap.mem_range_self _ _))
  obtain ⟨y, hy⟩ := GlobalTheory.TwistedClassSum.exists_adForm B.fw hHW hU (B.O i).hV hm a f 1 fun q =>
    (hf q.out).trans (one_mul _).symm
  rw [one_smul, one_smul] at hy
  exact ⟨y, (hHW i _).1 hy.symm⟩

end GlobalTheory.Mem.R3.GeoExProof
