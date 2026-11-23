import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

open GlobalTheory.TrueGeo.SmallSec

theorem pair_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    ∀ P : Pair p, ∃ (Q : Pair q) (e : X.functionField →+* Y.functionField), Q.L = P.L.pull π hπ ∧
      Q.A = P.A.pull π hπ ∧ ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map π hπ _ y) f := by
  intro k _ X _ p Y _ q π hπ hgen P
  subst hπ
  have hη : π (genericPoint Y) ⤳ genericPoint X := hgen ▸ specializes_rfl
  let Q : Pair (π ≫ p) :=
    ⟨P.L.pull π rfl, P.A.pull π rfl, _, _, MultPull.isRatSec_pull_map π hη P.hr,
      MultPull.isRatSec_pull_map π hη P.hr'⟩
  have hloc : ∀ (a b : ℤ) (f : X.functionField) (i : Q.L.B.ι) (j : Q.A.B.ι),
      Q.loc a b (fnMap π hη f) i j = fnMap π hη (P.loc a b f (i PUnit.unit) (j PUnit.unit)) := by
    intro a b f i j
    simp only [Pair.loc, map_mul, map_zpow₀]
    rfl
  have hmem : ∀ (a b : ℤ), ∀ f ∈ P.H a b, fnMap π hη f ∈ Q.H a b := by
    intro a b f hf x i j hi hj
    rw [hloc]
    exact FrameGlue.Pull.regAt_fnMap π hη
      (hf (π x) (i PUnit.unit) (j PUnit.unit) (Set.mem_iInter.1 hi PUnit.unit) (Set.mem_iInter.1 hj PUnit.unit))
  refine ⟨Q, fnMap π hη, rfl, rfl, fun a b f hf => ⟨hmem a b f hf, fun σ y => ?_⟩⟩
  let z := Points.PtsOver.map π (rfl : π ≫ p = π ≫ p) (spMap σ) y
  set i0 := pick (P.L.φ σ).isLB z
  set j0 := pick (P.A.φ σ).isLB z
  have hi0 : z ∈ ptsIn p σ (P.L.B.U i0) := mem_pick _ z
  have hj0 : z ∈ ptsIn p σ (P.A.B.U j0) := mem_pick _ z
  have hi : y ∈ ptsIn (π ≫ p) σ (Q.L.B.U fun _ => i0) :=
    mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hi0)
  have hj : y ∈ ptsIn (π ≫ p) σ (Q.A.B.U fun _ => j0) :=
    mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hj0)
  have hreg : RegAt (under z) (P.loc a b f i0 j0) :=
    hf (under z) i0 j0 (mem_ptsIn.1 hi0) (mem_ptsIn.1 hj0)
  have hval : ratVal (fnMap π hη (P.loc a b f i0 j0)) y = ratVal (P.loc a b f i0 j0) z := by
    show ratVal (fnMap π hη (P.loc a b f i0 j0)) y = ratVal (P.loc a b f i0 j0)
      (Points.PtsOver.map π (rfl : π ≫ p = π ≫ p) (spMap σ) y)
    rw [ratVal_eq_valAt y (FrameGlue.Pull.regAt_fnMap π hη hreg), valAt_fnMap π hη _ hreg,
      ratVal_eq_valAt _ hreg]
    rfl
  rw [GlobalTheory.VolBr.nu_eq k Y (π ≫ p) Q a b _ (hmem a b f hf) σ y _ _ hi hj,
    GlobalTheory.VolBr.nu_eq k X p P a b f hf σ z i0 j0 hi0 hj0]
  erw [hloc a b f (fun _ => i0) (fun _ => j0), hval]
  erw [(P.L.φ σ).pull_φ π rfl (fun _ => i0) y, (P.A.φ σ).pull_φ π rfl (fun _ => j0) y]

end GlobalTheory.HSAmp
