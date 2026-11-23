import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormSubEqOneOfPowEqOne

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial

variable {p : ℕ} [Fact p.Prime]

noncomputable def red (x : PadicAlgCl p) : kbar p :=
  open Classical in if h : ‖x‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0

theorem red_coe (x : Obar p) : red (x : PadicAlgCl p) = res x := dif_pos (norm_le_one x)

theorem red_of_le {x : PadicAlgCl p} (h : ‖x‖ ≤ 1) : red x = res ⟨x, mem_Obar_iff.2 h⟩ := dif_pos h

theorem red_eq_iff {x y : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : red x = red y ↔ ‖x - y‖ < 1 := by
  rw [red_of_le hx, red_of_le hy, res_eq_iff]

theorem red_pow {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) (k : ℕ) : red (x ^ k) = red x ^ k := by
  rw [red_of_le hx, ← map_pow, ← red_coe]
  rfl

theorem pow_qK_eq (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {c : kbar p} (hc : c ∈ resK p K) : c ^ qK p K = c := by
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have h := FiniteField.pow_card (⟨c, hc⟩ : resK p K)
  rw [← Nat.card_eq_fintype_card] at h
  exact congrArg Subtype.val h

theorem mem_resK_of_pow (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {c : kbar p} (h : c ^ qK p K = c) : c ∈ resK p K := by
  classical
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have hq := one_lt_qK K hK
  set P : (kbar p)[X] := X ^ qK p K - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (kbar p) hq
  have hdeg : P.natDegree = qK p K := FiniteField.X_pow_card_sub_X_natDegree_eq (kbar p) hq
  let T : Finset (kbar p) := (Finset.univ : Finset (resK p K)).image Subtype.val
  have hT : T.card = qK p K := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ, qK,
      Nat.card_eq_fintype_card]
  have hsub : T ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp [pow_qK_eq K hK y.2]
  have hle : P.roots.toFinset.card ≤ T.card := by
    rw [hT, ← hdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc : c ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
    simp [h]
  rw [← heq] at hc
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hc
  exact y.2

theorem exists_primitiveRoot {m : ℕ} (hm : m ≠ 0) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ m := by
  have : NeZero m := ⟨hm⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) m

theorem exists_lift_root {m : ℕ} (hm : ¬ p ∣ m) {c : kbar p} (hc : c ^ m = 1) :
    ∃ ζ : PadicAlgCl p, ζ ^ m = 1 ∧ red ζ = c := by
  classical
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hmp : 0 < m := Nat.pos_of_ne_zero hm0
  obtain ⟨ζ0, hζ0⟩ := exists_primitiveRoot (p := p) hm0
  let T : Finset (kbar p) := (nthRootsFinset m (1 : PadicAlgCl p)).image red
  have hinj : Set.InjOn red (nthRootsFinset m (1 : PadicAlgCl p) : Set (PadicAlgCl p)) := by
    intro x hx y hy hxy
    have hx' := (mem_nthRootsFinset hmp 1).1 hx
    have hy' := (mem_nthRootsFinset hmp 1).1 hy
    by_contra hne
    have h1 := norm_sub_eq_one_of_pow_eq_one hm hx' hy' hne
    have h2 := (red_eq_iff (norm_eq_one_of_pow hm0 hx').le (norm_eq_one_of_pow hm0 hy').le).1 hxy
    exact absurd h1 (ne_of_lt h2)
  have hT : T.card = m := by
    rw [Finset.card_image_of_injOn hinj, hζ0.card_nthRootsFinset]
  have hsub : T ⊆ nthRootsFinset m (1 : kbar p) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    have hy' := (mem_nthRootsFinset hmp 1).1 hy
    rw [mem_nthRootsFinset hmp, ← red_pow (norm_eq_one_of_pow hm0 hy').le, hy']
    have : red (1 : PadicAlgCl p) = res 1 := red_coe 1
    rw [this, map_one]
  have hle : (nthRootsFinset m (1 : kbar p)).card ≤ T.card := by
    rw [hT]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots m 1)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hc' : c ∈ nthRootsFinset m (1 : kbar p) := (mem_nthRootsFinset hmp 1).2 hc
  rw [← heq] at hc'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc'
  exact ⟨y, (mem_nthRootsFinset hmp 1).1 hy, rfl⟩

theorem mem_of_fixed (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {x : PadicAlgCl p}
    (h : ∀ σ : GK p K, σ x = x) : x ∈ K := by
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := PadicAlgCl p) x).2 h
  rw [← hy]
  exact y.2

theorem mem_of_pow_qK_sub_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K - 1) = 1) : ζ ∈ K := by
  have hq := one_lt_qK K hK
  have hnd : ¬ p ∣ qK p K - 1 := by simpa using not_dvd_qK_pow_sub_one K hK (n := 1) one_pos
  have hm0 : qK p K - 1 ≠ 0 := by omega
  have h1 := norm_eq_one_of_pow hm0 hζ
  have hc : red ζ ∈ resK p K := by
    apply mem_resK_of_pow K hK
    rw [← red_pow h1.le]
    congr 1
    have : qK p K = (qK p K - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  obtain ⟨x, hx, hxc⟩ := (mem_resK_iff K _).1 hc
  rw [← red_coe, red_eq_iff (norm_le_one x) h1.le] at hxc
  apply mem_of_fixed K
  intro σ
  by_contra hne
  have hσζ : (σ ζ) ^ (qK p K - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have h2 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζ hne
  have hσx : σ (x : PadicAlgCl p) = x := σ.commutes ⟨x, hx⟩
  have h3 : σ ζ - ζ = ((x : PadicAlgCl p) - ζ) - σ ((x : PadicAlgCl p) - ζ) := by
    rw [map_sub, hσx]; ring
  have h4 : ‖σ ζ - ζ‖ < 1 := by
    rw [h3]
    refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt hxc ?_)
    rw [norm_GK]; exact hxc
  exact absurd h2 (ne_of_lt h4)

theorem exists_teichmuller (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {x : PadicAlgCl p} (hx : x ∈ K) (h1 : ‖x‖ = 1) :
    ∃ ζ ∈ K, ζ ^ (qK p K - 1) = 1 ∧ ‖x - ζ‖ < 1 := by
  have hq := one_lt_qK K hK
  have hnd : ¬ p ∣ qK p K - 1 := by simpa using not_dvd_qK_pow_sub_one K hK (n := 1) one_pos
  have hm0 : qK p K - 1 ≠ 0 := by omega
  have hmem : red x ∈ resK p K := (mem_resK_iff K _).2 ⟨⟨x, mem_Obar_iff.2 h1.le⟩, hx, (red_of_le h1.le).symm⟩
  have hne : red x ≠ 0 := by
    rw [red_of_le h1.le, Ne, res_eq_zero_iff]
    exact not_lt.2 h1.ge
  have hpow : red x ^ (qK p K - 1) = 1 := by
    have h2 := pow_qK_eq K hK hmem
    have : qK p K = (qK p K - 1) + 1 := by omega
    rw [this, pow_succ] at h2
    exact mul_right_cancel₀ hne (by rw [h2, one_mul])
  obtain ⟨ζ, hζ, hr⟩ := exists_lift_root hnd hpow
  refine ⟨ζ, mem_of_pow_qK_sub_one K hK hζ, hζ, ?_⟩
  exact (red_eq_iff h1.le (norm_eq_one_of_pow hm0 hζ).le).1 hr.symm

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
