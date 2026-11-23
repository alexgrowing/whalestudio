import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.UnitN

theorem exists_unit_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ]
    {K : Set G} (hK : IsCompact K) (hcov : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) :
    ∃ (ν : Measure G) (𝓝 : Set G), ν.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓝 ν ∧ ν 𝓝 = 1 := by
  let μ : Measure G := Measure.haar
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain Γ μ
  have hle : μ 𝓕 ≤ μ K := by
    rw [h.measure_eq_tsum K]
    refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hK.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h.measure_ne_zero (NeZero.ne μ)
  refine ⟨(μ 𝓕)⁻¹ • μ, 𝓕, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 hpos),
    h.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

theorem exists_isUnitN : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ ν 𝓝, GlobalTheory.Per.IsUnitN B e ν 𝓝 := by
  intro D B ρ e he
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcl : IsClosed (NFlag B e : Set (GA D B)) := by
    have : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
      DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have : LocallyCompactSpace (NFlag B e) := hcl.locallyCompactSpace
  have : SecondCountableTopology (NFlag B e) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))
  have : Countable (NFlagQ B e) := hinj.countable
  have : DiscreteTopology (NFlagQ B e) :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  exact exists_unit_of_cocompact (NFlagQ B e) hK h

end GlobalTheory.Per.UnitN
