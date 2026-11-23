import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem exists_frob_pow_inv_mul_mem : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (q : Pl) (B : ValuationSubring Ω) (K : Subgroup (G ℚ Ω)), IsPlaceOver B q → Ine (F := ℚ) B ≤ K → IsOpen ((K.subgroupOf (Dec (F := ℚ) B) : Subgroup ↥(Dec (F := ℚ) B)) : Set ↥(Dec (F := ℚ) B)) → ∃ (φ : ↥(Dec (F := ℚ) B)) (m : ℕ), 0 < m ∧ ((φ ^ m : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K ∧ ∀ N : ℕ, 0 < N → ∃ d : ↥(Dec (F := ℚ) B) →* Multiplicative (ZMod (m * N)), IsOpen (d.ker : Set ↥(Dec (F := ℚ) B)) ∧ ∀ s : ↥(Dec (F := ℚ) B), (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥(Dec (F := ℚ) B)) : G ℚ Ω) ∈ K := by
  intro Ω _ _ _ q B K hq hIK hKo
  obtain ⟨φ, -, hcl, hd⟩ := UpperTheory.V.GC.decZhat ℚ Ω q B hq
  haveI : CompactSpace (Dec (F := ℚ) B) :=
    isCompact_iff_compactSpace.1 (ReciprocityTheory.Gal.isClosed_Dec (F := ℚ) B).isCompact
  set K' : Subgroup (Dec (F := ℚ) B) := K.subgroupOf (Dec (F := ℚ) B) with hK'
  haveI : Finite (Dec (F := ℚ) B ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hKo
  haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨m, hm0, -, hmK'⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K')) φ
  refine ⟨φ, m, hm0, Subgroup.mem_subgroupOf.1 hmK', fun N hN => ?_⟩
  obtain ⟨d, hdlc, hdI, hdφ⟩ := hd (m * N) (Nat.mul_pos hm0 hN)
  haveI : NeZero (m * N) := ⟨(Nat.mul_pos hm0 hN).ne'⟩
  refine ⟨d, hdlc.isOpen_fiber 1, ?_⟩

  have hK'cl : IsClosed (K' : Set (Dec (F := ℚ) B)) := Subgroup.isClosed_of_isOpen K' hKo
  have hcont : Continuous (fun s : Dec (F := ℚ) B => (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s) := by
    have h1 : IsLocallyConstant (fun s : Dec (F := ℚ) B => (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹) :=
      hdlc.comp (fun x => (φ ^ (Multiplicative.toAdd x).val)⁻¹)
    exact h1.continuous.mul continuous_id
  have hS : IsClosed {s : Dec (F := ℚ) B | (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s ∈ K'} :=
    hK'cl.preimage hcont
  have hI'K' : (Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B) ≤ K' := fun i hi =>
    Subgroup.mem_subgroupOf.2 (hIK (Subgroup.mem_subgroupOf.1 hi))
  have hsub : ((((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B) ⊔ Subgroup.zpowers φ :
      Subgroup (Dec (F := ℚ) B))) : Set (Dec (F := ℚ) B)) ⊆
      {s : Dec (F := ℚ) B | (φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s ∈ K'} := by
    intro x hx
    rw [Subgroup.normal_mul] at hx
    obtain ⟨i, hi, y, hy, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    simp only [Set.mem_ofPred_eq]
    set v := (Multiplicative.toAdd (d (i * φ ^ j))).val with hv
    have hdv : ((v : ℤ) : ZMod (m * N)) = (j : ZMod (m * N)) := by
      rw [Int.cast_natCast, hv, ZMod.natCast_zmod_val, map_mul, hdI i hi, one_mul, map_zpow, hdφ,
        ← ofAdd_zsmul, toAdd_ofAdd, zsmul_one]
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (j - v) (m * N)).1 (by
      rw [Int.cast_sub, hdv, sub_self])
    have e : (φ ^ v)⁻¹ * (i * φ ^ j) = ((φ ^ v)⁻¹ * i * ((φ ^ v)⁻¹)⁻¹) * (φ ^ m) ^ ((N : ℤ) * t) := by
      rw [← zpow_natCast φ m, ← zpow_mul, ← zpow_natCast φ v]
      have : j = (v : ℤ) + (m : ℤ) * (N * t) := by push_cast at ht; linarith [ht]
      rw [this, zpow_add]
      group
    rw [e]
    refine K'.mul_mem (hI'K' ?_) (K'.zpow_mem hmK' _)
    exact Subgroup.Normal.conj_mem inferInstance i hi _
  intro s
  have hs : s ∈ (((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B) ⊔ Subgroup.zpowers φ).topologicalClosure :
      Set (Dec (F := ℚ) B)) := by rw [hcl]; trivial
  rw [Subgroup.topologicalClosure_coe] at hs
  exact Subgroup.mem_subgroupOf.1 (closure_minimal hsub hS hs)

end GlobalTheory.Ord2
