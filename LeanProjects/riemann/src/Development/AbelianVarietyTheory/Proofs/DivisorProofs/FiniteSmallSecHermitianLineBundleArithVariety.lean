import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SmallFin

theorem smallSec_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  intro k _ X _ p D hX M
  obtain ⟨P, hL, -⟩ := GlobalTheory.VolBr.exists_pair M M
  subst hL
  have hrep : P.Rep 1 0 P.L := (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  obtain ⟨e, he, hrange, hnorm, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P 1 0 P.L hrep
  have hfin : (P.Bl 1 0 1).Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  refine (hfin.preimage he.injOn).subset ?_
  intro u hu
  refine ⟨?_, fun σ y => ?_⟩
  · have hm : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at hm
    exact hm
  have h0 : 0 ≤ P.nu 1 0 σ y (e u) := by
    unfold Pair.nu; positivity
  have h1 : P.nu 1 0 σ y (e u) ^ 2 ≤ 1 := by
    rw [hnorm]; exact hu σ y
  exact (pow_le_one_iff_of_nonneg h0 two_ne_zero).1 h1

end GlobalTheory.SmallFin
