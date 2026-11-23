import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocBasisMaps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdHNatsmulRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLocSpOfNatCastSmulMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FrameLat

theorem colSpan_mul' (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M g : Matrix (Fin k) (Fin k) K) :
    Formalism.MainNotions.G.colSpan R (M * g) = (Formalism.MainNotions.G.colSpan R g).map ((M.mulVecLin).restrictScalars R) := by
  unfold Formalism.MainNotions.G.colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem latMap_pair' (D : D7) {p : ℕ} (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K)
    (hu : ∀ s : ℕ, Nat.Coprime s p → IsUnit (s : R)) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin N') (Fin N') K)
    (hG : Formalism.MainNotions.G.colSpan R G = locSp R ρ L) (hG' : Formalism.MainNotions.G.colSpan R G' = locSp R ρ L')
    (B : Matrix (Fin N') (Fin N) D.host.E) (hB : ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L')
    (hL : Formalism.BasicNotions.IsSDLat D.host.E N L) (hL' : Formalism.BasicNotions.IsSDLat D.host.E N' L') :
    (∀ c, (B.map ρ) *ᵥ (fun x => G x c) ∈ Formalism.MainNotions.G.colSpan R G') ∧
    (∀ c, (B.map (fun y => ρ (D.host.conj y)))ᵀ *ᵥ (fun x => G' x c) ∈ Formalism.MainNotions.G.colSpan R G) := by
  obtain ⟨s, hs, hB'⟩ := hB
  constructor
  · intro c
    rw [hG']
    refine locSp_maps_of_unit_smul R K ρ L L' B s (hu s hs) hB' _ ?_
    rw [← hG]
    exact Submodule.subset_span ⟨c, rfl⟩
  · intro c
    have e : (B.map (fun y => ρ (D.host.conj y)))ᵀ = ((B.map D.host.conj)ᵀ).map ρ := by
      ext a b
      rfl
    rw [e, hG]
    refine locSp_maps_of_unit_smul R K ρ L' L _ s (hu s hs) (adj_maps_sd D L L' B s hL hL' hB') _ ?_
    rw [← hG']
    exact Submodule.subset_span ⟨c, rfl⟩

end GlobalTheory.TwV.FrameLat

open GlobalTheory.TwV.FrameLat in

theorem GlobalTheory.TwV.frameLatMapLt_of_ties : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧ ∀ v, locSp (X.G.P.W v) (ρ v) (fd.kerN j La) = (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧ locSp (X.G.P.W v) (ρ v) (fd.kerN (j + 1) La') = (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))) → Lt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ := by
  intro p _ X _ hfin D fd ρ hA hT
  intro j hj L0 hL0 La' hLa' φ r b hb _ i v
  have hL0' : (X.Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat X.Lv hfin j L0 hL0
  obtain ⟨hAd, hK⟩ := hT j hj L0 La' hL0' hLa'
  obtain ⟨hK1, hK2⟩ := hK v
  refine latMap_pair' D (X.G.P.W v) (ρ v) (natCast_isUnit_localRing X v) (Formalism.L2.KerInert.RepFrame.Gm X fd.frM φ v)
    (Formalism.L2.KerInert.RepFrame.Gp X fd.frM φ v) ?_ ?_ (b i)
    (GlobalTheory.TwV.YYMaps.locBasis_maps D p hA _ _ b hb i) hAd.2.2.1 hAd.2.2.2
  · rw [hK1]
    unfold Formalism.L2.KerInert.RepFrame.Gm
    rw [colSpan_mul', ← φ.hg v]
  · rw [hK2]
    unfold Formalism.L2.KerInert.RepFrame.Gp
    rw [colSpan_mul', ← φ.hg' v]
