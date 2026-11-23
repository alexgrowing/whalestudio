import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.DerExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem isOpen_O : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer

theorem isCompact_O : IsCompact (𝒪[k] : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem exists_ne_zero_mem {U : Set k} (hU : U ∈ 𝓝 (0 : k)) : ∃ z : k, z ≠ 0 ∧ z ∈ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).mp hU
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact γ.ne_zero (by simpa using hy.symm)
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  refine ⟨r * y, mul_ne_zero hr0 hy0, hγ ?_⟩
  show valuation k (r * y) < γ
  rw [map_mul, hy]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1

variable (k) in

def intGL (N : ℕ) : Subgroup (GL (Fin N) k) where
  carrier := {g | ∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] ∧
    ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k]}
  mul_mem' {a b} ha hb := by
    intro i j
    simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact ⟨Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l).1 (hb l j).1,
      Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hb i l).2 (ha l j).2⟩
  one_mem' := by
    intro i j
    simp only [inv_one, Units.val_one, Matrix.one_apply, and_self]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  inv_mem' {a} ha := by
    intro i j
    simpa [and_comm] using ha i j

theorem isCompact_intGL (N : ℕ) : IsCompact (intGL k N : Set (GL (Fin N) k)) := by
  haveI := t2 (k := k)
  let S : Set (Matrix (Fin N) (Fin N) k) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (𝒪[k] : Set k)
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_O
  have hS' : IsCompact (S ×ˢ (MulOpposite.op '' S)) :=
    hS.prod (hS.image MulOpposite.continuous_op)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage hS' using 1
  ext g
  constructor
  · intro h
    refine ⟨fun i _ j _ => (h i j).1, ⟨_, fun i _ j _ => (h i j).2, rfl⟩⟩
  · rintro ⟨h1, ⟨x, hx, hxe⟩⟩ i j
    have hx' : x = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := MulOpposite.op_injective hxe
    subst hx'
    exact ⟨h1 i (Set.mem_univ _) j (Set.mem_univ _), hx i (Set.mem_univ _) j (Set.mem_univ _)⟩

theorem isClosed_derUnip (N n : ℕ) : IsClosed (derUnip k N n : Set (GL (Fin N) k)) := by
  haveI := t2 (k := k)
  have hv : Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) := Units.continuous_val
  have he : ∀ i j : Fin N, Continuous fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j :=
    fun i j => hv.matrix_elem i j
  have h1 : (unipB k (Fin N) : Set (GL (Fin N) k)) =
      (⋂ i, ⋂ j, ⋂ (_ : j < i), {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i j = 0}) ∩
        ⋂ i, {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  have h2 : (colFix k N n : Set (GL (Fin N) k)) =
      ⋂ i : Fin N, ⋂ (_ : (i : ℕ) < n),
        {g : GL (Fin N) k | (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  show IsClosed ((unipB k (Fin N) ⊓ colFix k N n : Subgroup _) : Set (GL (Fin N) k))
  rw [Subgroup.coe_inf, h1, h2]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (he i j) continuous_const
  · exact isClosed_iInter fun i => isClosed_eq (he i i) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hv.matrix_mulVec continuous_const) continuous_const

theorem conj_entry_mem {N : ℕ} (y : kˣ) (hy : (y : k) ∈ 𝒪[k]) {u : GL (Fin N) k}
    (hu : u ∈ unipB k (Fin N)) (hyu : ∀ i j, (y : k) * (u : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k])
    (i j : Fin N) :
    (((diagT k (Fin N) (fun l : Fin N => y ^ (l : ℕ)))⁻¹ * u *
      diagT k (Fin N) (fun l : Fin N => y ^ (l : ℕ)) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j
      ∈ 𝒪[k] := by
  obtain ⟨h0, h1⟩ := (mem_unipB k).1 hu
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have ha0 : (y : k) ≠ 0 := y.ne_zero
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
    rw [hd]
    have e : ((y : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin N) (Fin N) k) i j * (y : k) ^ ((i : ℕ) + d + 1) =
        ((y : k) * (u : Matrix (Fin N) (Fin N) k) i j) * (y : k) ^ d := by
      rw [pow_succ, pow_add]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hyu i j) (Subring.pow_mem _ hy d)
  · have : i = j := Fin.ext hij
    subst this
    rw [h1 i, mul_one, inv_mul_cancel₀ (pow_ne_zero _ ha0)]
    exact Subring.one_mem _
  · rw [h0 i j (Fin.lt_def.2 hij), mul_zero, zero_mul]
    exact Subring.zero_mem _

theorem exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N n : ℕ) (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ derUnip k N n →
    ∃ L : Subgroup (GL (Fin N) k), L ≤ derUnip k N n ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
      IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N n s hs
  have hmul : ∀ c : k, ∀ᶠ z in 𝓝 (0 : k), z * c ∈ 𝒪[k] := by
    intro c
    have h := (continuous_mul_right c).tendsto (0 : k)
    rw [zero_mul] at h
    exact h (isOpen_O.mem_nhds (Subring.zero_mem _))
  have hU : ∀ᶠ z in 𝓝 (0 : k), z ∈ 𝒪[k] ∧ ∀ g ∈ s, ∀ i j : Fin N,
      z * (g : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] ∧
        z * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ 𝒪[k] :=
    (show ∀ᶠ z in 𝓝 (0 : k), z ∈ 𝒪[k] from isOpen_O.mem_nhds (Subring.zero_mem _)).and ((Filter.eventually_all_finset _).2 fun g _ =>
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hmul _).and (hmul _))
  obtain ⟨y, hy0, hyO, hyS⟩ := exists_ne_zero_mem hU
  set t := diagT k (Fin N) (fun l : Fin N => (Units.mk0 y hy0) ^ (l : ℕ)) with ht
  refine ⟨(intGL k N).map (MulAut.conj t).toMonoidHom ⊓ derUnip k N n, inf_le_right, ?_, ?_⟩
  · intro g hg
    have hgu : g ∈ unipB k (Fin N) := (hs hg).1
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨t⁻¹ * g * t, ?_, ?_⟩, hs hg⟩
    · intro i j
      have hinv : (t⁻¹ * g * t)⁻¹ = t⁻¹ * g⁻¹ * t := by group
      rw [hinv]
      exact ⟨conj_entry_mem (Units.mk0 y hy0) hyO hgu (fun i j => (hyS g hg i j).1) i j,
        conj_entry_mem (Units.mk0 y hy0) hyO (inv_mem hgu) (fun i j => (hyS g hg i j).2) i j⟩
    · show t * (t⁻¹ * g * t) * t⁻¹ = g
      group
  · rw [Subgroup.coe_inf, Subgroup.coe_map]
    have hc : Continuous fun g : GL (Fin N) k => t * g * t⁻¹ := by fun_prop
    exact ((isCompact_intGL N).image hc).inter_right (isClosed_derUnip N n)

end GlobalTheory.CompanionTheory.DerExhaust
