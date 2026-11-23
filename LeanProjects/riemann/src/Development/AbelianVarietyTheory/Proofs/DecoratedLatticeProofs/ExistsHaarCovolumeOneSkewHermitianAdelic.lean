import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SkewVol

variable (D : D7) (ρ : ℕ)

def skewPart (x : Mx D ρ ρ) : Mx D ρ ρ := half D • (x - adj x)

variable {D ρ}

theorem skewPart_mem (x : Mx D ρ ρ) : skewPart D ρ x ∈ skewA D ρ := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {c : Mx D ρ ρ} (hc : c ∈ skewA D ρ) : skewPart D ρ c = c := by
  rw [skewPart, (mem_skewA).1 hc, sub_neg_eq_add, smul_add, half_smul_add]

theorem skewPart_add (x y : Mx D ρ ρ) : skewPart D ρ (x + y) = skewPart D ρ x + skewPart D ρ y := by
  rw [skewPart, skewPart, skewPart, adj_add, add_sub_add_comm, smul_add]

theorem skewPart_rat {x : Mx D ρ ρ} (hx : x ∈ ratMx D ρ ρ) : skewPart D ρ x ∈ ratMx D ρ ρ := by
  obtain ⟨γ, rfl⟩ := (mem_ratMx).1 hx
  refine (mem_ratMx).2 ⟨(1 / 2 : D.host.E) • (γ - γᴴ), ?_⟩
  rw [rat_smul, rat_sub, rat_conjTranspose]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPart D ρ) :=
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := (lattice_Mx D ρ ρ).1
  show Continuous fun x => half D • (x - adj x) from (continuous_id.sub continuous_adj).const_smul (half D)

theorem isClosed_skewA : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) :=
  haveI : T2Space (Mx D ρ ρ) := (lattice_Mx D ρ ρ).2.2.2.1
  isClosed_eq continuous_adj continuous_neg

theorem isCoLat_skew :
    GlobalTheory.CuspGeneric.IsCoLat ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) := by
  obtain ⟨-, -, -, -, i5, K, hK, hKc⟩ := lattice_Mx D ρ ρ
  refine ⟨?_, ?_⟩
  · let φ : (ratMx D ρ ρ).addSubgroupOf (skewA D ρ) → ratMx D ρ ρ := fun q => ⟨q.1.1, q.2⟩
    have hinj : Function.Injective φ := fun a b h =>
      Subtype.ext (Subtype.ext (by simpa [φ] using congrArg Subtype.val h))
    have hcont : Continuous φ :=
      ((continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hcont hinj
  · let P : Mx D ρ ρ → skewA D ρ := fun x => ⟨skewPart D ρ x, skewPart_mem x⟩
    have hP : Continuous P := continuous_skewPart.subtype_mk _
    refine ⟨P '' K, hK.image hP, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKc x.1
    refine ⟨P γ, AddSubgroup.mem_addSubgroupOf.2 (skewPart_rat hγ), γ + x.1, hx, ?_⟩
    apply Subtype.ext
    change skewPart D ρ (γ + x.1) = skewPart D ρ γ + x.1
    rw [skewPart_add, skewPart_of_mem x.2]

theorem exists_haar_covol_one : ∀ (D : D7) (ρ : ℕ), ∃ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure ∧ SFinite lC ∧ IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC ∧ lC 𝓒 = 1 := by
  intro D ρ
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (skewA D ρ) := (isClosed_skewA (D := D) (ρ := ρ)).locallyCompactSpace
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ :=
    GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one (skewA D ρ) _ isCoLat_skew
  exact ⟨μ, 𝓕, hμ, inferInstance, hF, h1⟩

end GlobalTheory.SkewVol
