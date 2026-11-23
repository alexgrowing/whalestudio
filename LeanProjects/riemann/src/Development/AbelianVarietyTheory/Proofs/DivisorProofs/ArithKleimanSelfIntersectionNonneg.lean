import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGenericPointNonnegAmpleSemiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTensStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.KleimanStep

theorem selfInter_nonneg : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D →
    (∀ (C : HermLB p) (h : X → ℝ), C.IsNef D → C.IsArithHeight h → ∀ z, z ≠ genericPoint X → 0 ≤ h z) →
    ∀ (C : HermLB p) (c : ℝ), C.IsNef D → C.IsSelfInter c → 0 ≤ c := by
  intro hC hHS k _ X _ p D hX hD hlow C c hnef hc
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX C A c hc
  refine ge_of_tendsto' hlim fun n => div_nonneg ?_ (by positivity)
  have hpow := GlobalTheory.NefPow.isNef_pow hC k X p D hX C n hnef
  have htens := GlobalTheory.T.hermLineBundle_isNef_tens hC k X p D hX _ _ hpow hAn
  have hamp := GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX _ A hpow.vertical hA
  obtain ⟨h, hh, he⟩ := hα n
  rw [← he]
  exact GlobalTheory.T.height_genericPoint_nonneg_ample_semiPositive hC hHS k X p D hX hD _ h hamp htens.semiPos hh (hlow _ h htens hh)

end GlobalTheory.KleimanStep
