import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeModPrime
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField StackedExceptionalFirstGeometric

noncomputable section

namespace StackedExceptionalResidueExists

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i}

theorem exists_mem_not_mem (hlt : F'.lattice < F.lattice) :
    ∃ φc ∈ dualLattice F', φc ∉ dualLattice F := by
  by_contra! h
  have h1 : (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr fun φ hφ => h φ hφ
  rw [DualLatticeIndex.proof K i F F' hlt.le] at h1
  have h2 := AddSubgroup.relIndex_eq_one.mp h1
  exact hlt.not_ge fun x hx => h2 hx

def annIdeal (F : HermLattice K i) (φc : Fin i → K) : Ideal (𝓞 K) where
  carrier := {μ | algebraMap (𝓞 K) K μ • φc ∈ dualLattice F}
  add_mem' {a b} ha hb := by
    show algebraMap (𝓞 K) K (a + b) • φc ∈ dualLattice F
    rw [map_add, add_smul]
    exact add_mem ha hb
  zero_mem' := by
    show algebraMap (𝓞 K) K 0 • φc ∈ dualLattice F
    rw [map_zero, zero_smul]
    exact zero_mem _
  smul_mem' c x hx := by
    show algebraMap (𝓞 K) K (c * x) • φc ∈ dualLattice F
    rw [map_mul, mul_smul]
    exact smul_mem_dual F c hx

theorem mem_annIdeal {φc : Fin i → K} {μ : 𝓞 K} :
    μ ∈ annIdeal F φc ↔ algebraMap (𝓞 K) K μ • φc ∈ dualLattice F := Iff.rfl

theorem annIdeal_isMaximal (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) : (annIdeal F φc).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hc' ?_, fun J x hle hx hxJ => ?_⟩
  · have := mem_annIdeal.mp h
    rwa [map_one, one_smul] at this
  obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov (smul_mem_dual F' x hc) (mem_annIdeal.not.mp hx) hc
  have h1 : 1 - l * x ∈ annIdeal F φc := by
    rw [mem_annIdeal, map_sub, map_one, map_mul, sub_smul, one_smul, mul_smul]
    exact hl
  have h2 := J.add_mem (hle h1) (J.mul_mem_left l hxJ)
  rwa [sub_add_cancel] at h2

theorem mk_eq_of {φc φ : Fin i → K} {l l' : 𝓞 K} (h : φ - algebraMap (𝓞 K) K l • φc ∈ dualLattice F)
    (h' : φ - algebraMap (𝓞 K) K l' • φc ∈ dualLattice F) :
    Ideal.Quotient.mk (annIdeal F φc) l = Ideal.Quotient.mk (annIdeal F φc) l' := by
  rw [Ideal.Quotient.eq, mem_annIdeal, map_sub, sub_smul]
  have e : algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l' • φc =
      (φ - algebraMap (𝓞 K) K l' • φc) - (φ - algebraMap (𝓞 K) K l • φc) := by abel
  rw [e]
  exact sub_mem h' h

def coeff (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') : 𝓞 K :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose

theorem coeff_spec (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') :
    (φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc ∈ dualLattice F :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose_spec

def rhoDual (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) :
    dualLattice F' →+ 𝓞 K ⧸ annIdeal F φc where
  toFun φ := Ideal.Quotient.mk _ (coeff hlt hcov hc hc' φ)
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk (annIdeal F φc))]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' 0) ?_
    rw [map_zero, zero_smul, sub_zero]
    exact zero_mem _
  map_add' φ ψ := by
    rw [← map_add]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' (φ + ψ)) ?_
    have e : ((φ + ψ : dualLattice F') : Fin i → K) - algebraMap (𝓞 K) K
        (coeff hlt hcov hc hc' φ + coeff hlt hcov hc hc' ψ) • φc =
        ((φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc) +
        ((ψ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' ψ) • φc) := by
      rw [Submodule.coe_add, map_add, add_smul]
      abel
    rw [e]
    exact add_mem (coeff_spec hlt hcov hc hc' φ) (coeff_spec hlt hcov hc hc' ψ)

theorem rhoDual_eq (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') (l : 𝓞 K)
    (h : (φ : Fin i → K) - algebraMap (𝓞 K) K l • φc ∈ dualLattice F) :
    rhoDual hlt hcov hc hc' φ = Ideal.Quotient.mk _ l :=
  mk_eq_of (coeff_spec hlt hcov hc hc' φ) h

end StackedExceptionalResidueExists

open StackedExceptionalResidueExists in

theorem DualStackedExcResidueExists.proof (hσ : DualLatticeModPrime.Statement) :
    DualStackedExcResidueExists.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov _
  obtain ⟨φc, hc, hc'⟩ := exists_mem_not_mem hlt
  set 𝔭 := annIdeal F φc with h𝔭
  have hmax : 𝔭.IsMaximal := annIdeal_isMaximal hlt hcov hc hc'
  let _ : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  obtain ⟨σ, hσs, hσl⟩ := hσ K i F 𝔭 hmax
  set ρ' := rhoDual hlt hcov hc hc' with hρ'
  have hker : ∀ φ : dualLattice F', ρ' φ = 0 ↔ (φ : Fin i → K) ∈ dualLattice F := by
    intro φ
    have hs := coeff_spec hlt hcov hc hc' φ
    change Ideal.Quotient.mk 𝔭 (coeff hlt hcov hc hc' φ) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_annIdeal]
    constructor
    · intro h
      have := add_mem hs h
      rwa [sub_add_cancel] at this
    · intro h
      have := sub_mem h hs
      rwa [sub_sub_cancel] at this
  have hsurj : Function.Surjective ρ' := by
    intro x
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨⟨algebraMap (𝓞 K) K l • φc, smul_mem_dual F' l hc⟩, rhoDual_eq hlt hcov hc hc' _ l ?_⟩
    show algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l • φc ∈ dualLattice F
    rw [sub_self]
    exact zero_mem _
  have hcard : Nat.card (𝓞 K ⧸ 𝔭) = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup := by
    rw [← DualLatticeIndex.proof K i F F' hlt.le]
    have hk : (dualLattice F).toAddSubgroup.addSubgroupOf (dualLattice F').toAddSubgroup = ρ'.ker := by
      ext φ
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
      rfl
    rw [AddSubgroup.relIndex, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr (Equiv.Set.univ _)).symm
  refine ⟨𝓞 K ⧸ 𝔭, inferInstance, Fintype.ofFinite _, fun t => ρ' (b' t), fun t => σ (b t),
    ⟨Ideal.Quotient.mk 𝔭, ρ', σ, Ideal.Quotient.mk_surjective, hsurj, hσs, hker, ?_, hσl,
      fun t => rfl, fun t => rfl⟩, ?_⟩
  · intro μ φ ψ h
    rw [rhoDual_eq hlt hcov hc hc' ψ (μ * coeff hlt hcov hc hc' φ), map_mul]
    · rfl
    rw [h, map_mul, mul_smul, ← smul_sub]
    exact smul_mem_dual F μ (coeff_spec hlt hcov hc hc' φ)
  · rw [← hcard]
    exact Fintype.card_eq_nat_card

end

end GroundTheory.Heights₂.Heights
