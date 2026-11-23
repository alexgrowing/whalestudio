import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
import GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation

namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Density

theorem isClosed_multiples (N : ℕ) : IsClosed (multiples N : Set ℤ̂) := by
  have : (multiples N : Set ℤ̂) = Set.range (fun y : ℤ̂ => (N : ℤ̂) * y) := by
    ext x
    simp [multiples]
  rw [this]
  exact (isCompact_range (continuous_const.mul continuous_id)).isClosed

instance finiteIndex_multiples (N : ℕ+) : (multiples N).FiniteIndex :=
  ⟨by rw [index_multiples]; exact N.ne_zero⟩

theorem isOpen_multiples (N : ℕ+) : IsOpen (multiples N : Set ℤ̂) :=
  AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_multiples N)

theorem denseRange_intCast : DenseRange (Int.cast : ℤ → ℤ̂) := by
  intro x
  rw [mem_closure_iff]
  intro U hU hxU
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalAddSubgroup_sub_open_nhds_of_zero
    (hU.preimage (continuous_const_add x)) (by simpa using hxU)
  have : Finite (ℤ̂ ⧸ W.toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen W.toAddSubgroup W.isOpen'
  have hfi : W.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hm : W.toAddSubgroup.index ≠ 0 := hfi.index_ne_zero
  have hWm := eq_multiples_index hm
  set m : ℕ+ := ⟨W.toAddSubgroup.index, Nat.pos_of_ne_zero hm⟩ with hmdef
  refine ⟨((((proj m x).val : ℕ) : ℤ) : ℤ̂), ?_, Set.mem_range_self _⟩
  have hk : ((((proj m x).val : ℕ) : ℤ) : ℤ̂) - x ∈ W.toAddSubgroup := by
    rw [hWm]
    have := (proj_eq_zero_iff (n := m) (x := ((((proj m x).val : ℕ) : ℤ) : ℤ̂) - x)).1 (by
      rw [map_sub, map_intCast, Int.cast_natCast, ZMod.natCast_zmod_val, sub_self])
    simpa [hmdef] using this
  have := hW hk
  simpa using this

end Density

section FixedField

variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem mem_zpowers_sup_iff (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G))
    {h : G} : h ∈ Subgroup.zpowers σ ⊔ (L ⊓ d.ker) ↔ ∃ k : ℤ, ∃ j ∈ L ⊓ d.ker, h = σ ^ k * j := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (Subgroup.zpowers_le.2 hσ), Set.mem_mul]
  constructor
  · rintro ⟨a, ha, j, hj, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ⟨k, j, hj, rfl⟩
  · rintro ⟨k, j, hj, rfl⟩
    exact ⟨σ ^ k, Subgroup.zpow_mem_zpowers σ k, j, hj, rfl⟩

theorem deg_zpow_mul {N : ℕ} (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) (k : ℤ) {j : G}
    (hj : j ∈ L ⊓ d.ker) :
    Multiplicative.toAdd (d (σ ^ k * j)) = ((k * N : ℤ) : ℤ̂) := by
  rw [map_mul, map_zpow, hdσ, (MonoidHom.mem_ker).1 hj.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
    zsmul_eq_mul]
  push_cast
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable (d L σ) in

def frobeniusClosure : Subgroup G :=
  (Subgroup.zpowers σ ⊔ (L ⊓ d.ker)).topologicalClosure

theorem le_frobeniusClosure : L ⊓ d.ker ≤ frobeniusClosure d L σ :=
  le_sup_right.trans (Subgroup.le_topologicalClosure _)

theorem mem_frobeniusClosure_self : σ ∈ frobeniusClosure d L σ :=
  Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))

theorem isClosed_frobeniusClosure : IsClosed (frobeniusClosure d L σ : Set G) :=
  Subgroup.isClosed_topologicalClosure _

theorem frobeniusClosure_le {K : Subgroup G} (hK : IsClosed (K : Set G)) (hσK : σ ∈ K)
    (hLK : L ⊓ d.ker ≤ K) : frobeniusClosure d L σ ≤ K :=
  Subgroup.topologicalClosure_minimal _ (sup_le (Subgroup.zpowers_le.2 hσK) hLK) hK

theorem mem_fixedModule_frobeniusClosure {A : Type*} [CommGroup A] [MulDistribMulAction G A]
    [IsDiscreteModule G A] {a : A} :
    a ∈ fixedModule A (frobeniusClosure d L σ) ↔ a ∈ fixedModule A (L ⊓ d.ker) ∧ σ • a = a := by
  constructor
  · intro ha
    exact ⟨fixedModule_anti le_frobeniusClosure ha, ha σ mem_frobeniusClosure_self⟩
  · rintro ⟨ha, hσa⟩
    have hS : IsClosed (MulAction.stabilizer G a : Set G) :=
      Subgroup.isClosed_of_isOpen _ (IsDiscreteModule.isOpen_stabilizer a)
    have hle : frobeniusClosure d L σ ≤ MulAction.stabilizer G a :=
      frobeniusClosure_le hS (MulAction.mem_stabilizer_iff.2 hσa) fun g hg => ha g hg
    exact fun g hg => MulAction.mem_stabilizer_iff.1 (hle hg)

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem frobeniusClosure_inf_ker (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    frobeniusClosure d L σ ⊓ d.ker = L ⊓ d.ker := by
  refine le_antisymm ?_ (le_inf le_frobeniusClosure inf_le_right)
  intro x hx0
  obtain ⟨hx, hxk⟩ := Subgroup.mem_inf.1 hx0
  rw [MonoidHom.mem_ker] at hxk
  obtain ⟨U0, hU0⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hL L.one_mem
  have : Finite (G ⧸ U0.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U0.isOpen'
  set t := orderOf (σ : G ⧸ U0.toSubgroup) with htdef
  have ht : 0 < t := orderOf_pos _
  set M : ℕ+ := ⟨t * N, Nat.mul_pos ht (Nat.pos_of_ne_zero hN)⟩ with hMdef
  set V : Set G := (U0 : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
  have hV : IsOpen V :=
    U0.isOpen'.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
  have hO : IsOpen ((fun y => x⁻¹ * y) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
  have hxO : x ∈ (fun y => x⁻¹ * y) ⁻¹' V := by
    simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
    exact ⟨U0.one_mem', (multiples M).zero_mem⟩
  have hx' : x ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hx
  obtain ⟨h, hhO, hhH⟩ := mem_closure_iff.1 hx' _ hO hxO
  obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhH
  obtain ⟨hU, hWm⟩ := hhO
  have hdk : Multiplicative.toAdd (d (x⁻¹ * (σ ^ k * j))) = ((k * N : ℤ) : ℤ̂) := by
    rw [map_mul, map_inv, hxk, inv_one, one_mul]
    exact deg_zpow_mul hdσ k hj
  have hdiv : ((M : ℕ) : ℤ) ∣ k * N := by
    have hmem : ((k * N : ℤ) : ℤ̂) ∈ multiples M := by
      rw [← hdk]
      exact hWm
    exact (intCast_mem_multiples_iff M.pos).1 hmem
  have htk : (t : ℤ) ∣ k := by
    have h2 : (t : ℤ) * N ∣ k * N := by simpa [hMdef] using hdiv
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hN)).1 h2
  have hσk : σ ^ k ∈ U0.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_zpow, ← orderOf_dvd_iff_zpow_eq_one]
    exact htk
  refine ⟨?_, (MonoidHom.mem_ker).2 hxk⟩
  have hx_eq : x = σ ^ k * j * (x⁻¹ * (σ ^ k * j))⁻¹ := by group
  rw [hx_eq]
  exact L.mul_mem (L.mul_mem (hU0 hσk) hj.1) (L.inv_mem (hU0 hU))

omit [TotallyDisconnectedSpace G] in

theorem map_frobeniusClosure (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ}
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    (frobeniusClosure d L σ).map d = AddSubgroup.toSubgroup (multiples N) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hcl : IsClosed (d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples N : Set ℤ̂))) :=
      (isClosed_multiples N).preimage (continuous_toAdd.comp hd)
    have hsub : ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) ⊆
        d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples N : Set ℤ̂)) := by
      intro h hh
      obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hh
      simp only [Set.mem_preimage, SetLike.mem_coe]
      rw [deg_zpow_mul hdσ k hj, mem_multiples]
      exact ⟨(k : ℤ̂), by push_cast; rw [nsmul_eq_mul]; ring⟩
    have hx' : x ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hx
    exact closure_minimal hsub hcl hx'
  · intro y hy
    have hy' : Multiplicative.toAdd y ∈ multiples N := hy
    obtain ⟨w, hw⟩ := mem_multiples.1 hy'
    set S : Set (Multiplicative ℤ̂) := d '' (frobeniusClosure d L σ : Set G) with hSdef
    have hS : IsClosed S := (isClosed_frobeniusClosure.isCompact.image hd).isClosed
    have key : ∀ w : ℤ̂, Multiplicative.ofAdd ((N : ℤ̂) * w) ∈ S := by
      intro w
      refine denseRange_intCast.induction_on w
        (hS.preimage (continuous_ofAdd.comp (continuous_const.mul continuous_id))) fun k => ?_
      refine ⟨σ ^ k, Subgroup.zpow_mem _ mem_frobeniusClosure_self k, ?_⟩
      rw [map_zpow, hdσ, ← ofAdd_zsmul, zsmul_eq_mul, mul_comm]
    obtain ⟨x, hx, hxy⟩ := key w
    refine ⟨x, hx, ?_⟩
    rw [hxy, ← nsmul_eq_mul, ← hw]
    rfl

theorem isOpen_frobeniusClosure (hd : Continuous d) (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    IsOpen (frobeniusClosure d L σ : Set G) := by
  set S := frobeniusClosure d L σ with hSdef
  have hsup : S ⊔ d.ker = (AddSubgroup.toSubgroup (multiples N)).comap d := by
    rw [← map_frobeniusClosure hd hσ hdσ, Subgroup.comap_map_eq]
  have hsupOpen : IsOpen ((S ⊔ d.ker : Subgroup G) : Set G) := by
    rw [hsup]
    exact (isOpen_multiples ⟨N, Nat.pos_of_ne_zero hN⟩).preimage (continuous_toAdd.comp hd)
  have : Finite (G ⧸ (S ⊔ d.ker)) := Subgroup.quotient_finite_of_isOpen _ hsupOpen
  have h1 : (S ⊔ d.ker).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : Finite (G ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hL
  have : L.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h2 : S.relIndex (S ⊔ d.ker) ≠ 0 := by
    rw [relIndex_sup_of_le_normalizer (Subgroup.le_normalizer_of_normal),
      ← Subgroup.inf_relIndex_right, frobeniusClosure_inf_ker hd hL hσ hN hdσ,
      Subgroup.inf_relIndex_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  have : S.FiniteIndex :=
    ⟨by rw [← Subgroup.relIndex_mul_index le_sup_left]; exact mul_ne_zero h2 h1.index_ne_zero⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ isClosed_frobeniusClosure

omit [TotallyDisconnectedSpace G] in

theorem inertiaDegree_frobeniusClosure (hd : Continuous d)
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) :
    inertiaDegree d (frobeniusClosure d L σ) = N := by
  rw [inertiaDegree, map_frobeniusClosure hd hσ hdσ, AddSubgroup.index_toSubgroup]
  exact index_multiples ⟨N, Nat.pos_of_ne_zero hN⟩

end FixedField

end GroundTheory.LocalField.Abstract
