import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulRightInvariantMapWittFlagCoordinatesHaarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainFlagUnipotentCoordsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoordsUnit

theorem eq_of_rightInvariant_of_fundamentalDomain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] (ν m : Measure G) (𝓝 𝓕 : Set G)
    (h1 : ν.IsHaarMeasure) (h2 : IsFundamentalDomain Γ 𝓝 ν) (h3 : ν 𝓝 = 1) (k0 : SigmaFinite m) (k1 : m.IsMulRightInvariant)
    (k2 : IsFundamentalDomain Γ 𝓕 m) (k3 : m 𝓕 = 1) : m = ν := by
  haveI : ν.IsMulRightInvariant := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain Γ ν h2
    (by rw [h3]; exact one_ne_zero) (by rw [h3]; exact ENNReal.one_ne_top)
  have hinv : ν.inv 𝓝⁻¹ = 1 := by rw [Measure.inv_apply, inv_inv, h3]
  have e1 := measure_eq_div_smul m.inv ν.inv (s := 𝓝⁻¹) (by rw [hinv]; exact one_ne_zero) (by rw [hinv]; exact ENNReal.one_ne_top)
  rw [hinv, div_one, Measure.inv_apply, inv_inv] at e1
  set κ := m 𝓝 with hκ
  have e2 : m = κ • ν := by
    ext s -
    have := congrArg (fun μ : Measure G => μ s⁻¹) e1
    simpa only [Measure.inv_apply, inv_inv, Measure.smul_apply] using this
  have hκ0 : κ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at e2
    rw [e2] at k3
    simp at k3
  haveI : m.IsMulLeftInvariant := by rw [e2]; infer_instance
  have h2' : IsFundamentalDomain Γ 𝓝 m := h2.mono (by rw [e2]; exact Measure.smul_absolutelyContinuous)
  have h4 : m 𝓝 = 1 := (h2'.measure_eq k2).trans k3
  have hk1 : κ = 1 := by rw [hκ]; exact h4
  rw [e2, hk1, one_smul]

theorem volN_eq_map_coords : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → lC 𝓒 = 1 → vN.ν = (lC.prod (vb.μ.prod vU.ν)).map e := by
  intro D V V₀ ρ d vN vb vU e he lC 𝓒 hC hCs hCF hC1
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  obtain ⟨hU, 𝓤, hU𝓤, hU1⟩ := vU.unit
  obtain ⟨hb, hbF, hb1⟩ := vb.covol
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨-, m2, m3, m4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨-, n2, n3, n4, -⟩ := lattice_Mx D ρ ρ
  haveI := vN.unit.1
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite lC := inferInstance
  haveI : SigmaFinite vb.μ := inferInstance
  haveI : SigmaFinite vU.ν := inferInstance
  haveI hm : SigmaFinite ((lC.prod (vb.μ.prod vU.ν)).map e) := e.sigmaFinite_map
  have hR := GlobalTheory.T.isMulRightInvariant_map_wittFlagCoordinates_haar D V V₀ ρ d vb vU e he lC hC hCs
  have hF := GlobalTheory.T.isFundamentalDomain_flagUnipotent_coords D V V₀ ρ d vb vU e he lC 𝓒 𝓤 hC hCs hCF hU𝓤
  have h1 : (lC.prod (vb.μ.prod vU.ν)).map e (e '' (𝓒 ×ˢ (vb.𝓕 ×ˢ 𝓤))) = 1 := by
    rw [MeasurableEquiv.map_apply, e.preimage_image, Measure.prod_prod, Measure.prod_prod, hC1, hb1, hU1, one_mul, one_mul]
  exact (eq_of_rightInvariant_of_fundamentalDomain (NFlagQ V d.e) vN.ν _ vN.𝓝 _ vN.unit.1 vN.unit.2.1 vN.unit.2.2 hm hR hF h1).symm

end GlobalTheory.HaarCoordsUnit

end
