import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Mathlib.Topology.Algebra.ClopenNhdofOne

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen_of_max {A : Type} [CommGroup A] (l : ℕ)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n)
    (a : ℕ) (z : A) (h1 : z ^ l ^ (a + 1) = 1) (h0 : z ^ l ^ a ≠ 1) :
    ∀ b, b ≤ a + 1 → ∀ s : A, s ^ l ^ b = 1 → s ∈ Subgroup.zpowers z := by
  intro b
  induction b with
  | zero => intro _ s hs; simp at hs; simp [hs]
  | succ b ih =>
    intro hb s hs
    obtain ⟨n, hn⟩ := hl (z ^ l ^ a) (s ^ l ^ b) (by rw [← pow_mul, ← pow_succ, h1])
      (by rw [← pow_mul, ← pow_succ, hs]) h0
    obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
    have h2 : (s / z ^ (l ^ c * n)) ^ l ^ b = 1 := by
      rw [div_pow, hn, ← pow_mul, ← pow_mul, pow_add, mul_right_comm, div_self']
    have h3 := ih (by omega) _ h2
    have h4 := mul_mem h3 (Subgroup.npow_mem_zpowers z (l ^ c * n))
    rwa [div_mul_cancel] at h4

private theorem cyc_abs {A : Type} [CommGroup A] (l : ℕ) (hp : l.Prime)
    (hres : ∀ x : A, x ≠ 1 → ∃ U : Subgroup A, U.index ≠ 0 ∧ x ∉ U)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n) :
    ∃ z : A, (∃ a, z ^ l ^ a = 1) ∧ ∀ s : A, (∃ a, s ^ l ^ a = 1) → ∃ n : ℕ, s = z ^ n := by
  classical
  by_cases hx : ∃ x : A, x ^ l = 1 ∧ x ≠ 1
  · obtain ⟨x, hx1, hx0⟩ := hx
    obtain ⟨U, hU, hxU⟩ := hres x hx0
    let P : ℕ → Prop := fun a => ∃ s : A, s ^ l ^ (a + 1) = 1 ∧ s ^ l ^ a ≠ 1
    have hP0 : P 0 := ⟨x, by simpa using hx1, by simpa using hx0⟩
    have hbd : ∀ a, P a → a ≤ U.index := by
      rintro a ⟨s, h1, h0⟩
      by_contra hlt
      obtain ⟨n, hn⟩ := hl (s ^ l ^ a) x (by rw [← pow_mul, ← pow_succ, h1]) hx1 h0
      apply hxU
      rw [hn]
      apply pow_mem
      have d1 : orderOf (QuotientGroup.mk' U s) ∣ l ^ (a + 1) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, h1, map_one]
      have d2 : orderOf (QuotientGroup.mk' U s) ∣ U.index := orderOf_dvd_natCard _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 d1
      have d3 : l ^ j ≤ U.index := hj ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero hU) d2
      have d4 : j < l ^ j := Nat.lt_pow_self hp.one_lt
      have d5 : orderOf (QuotientGroup.mk' U s) ∣ l ^ a := hj ▸ pow_dvd_pow l (by omega)
      have d6 := orderOf_dvd_iff_pow_eq_one.1 d5
      rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at d6
      exact d6
    obtain ⟨z, h1, h0⟩ : P (Nat.findGreatest P U.index) := Nat.findGreatest_spec (Nat.zero_le _) hP0
    refine ⟨z, ⟨_, h1⟩, ?_⟩
    rintro s ⟨c, hc⟩
    have key : ∀ c, s ^ l ^ c = 1 → s ^ l ^ (Nat.findGreatest P U.index + 1) = 1 := by
      intro c
      induction c with
      | zero => intro h; simp at h; simp [h]
      | succ c ih =>
        intro h
        by_cases h' : s ^ l ^ c = 1
        · exact ih h'
        · have hPc : P c := ⟨s, h, h'⟩
          have := Nat.le_findGreatest (hbd c hPc) hPc
          exact orderOf_dvd_iff_pow_eq_one.1
            ((orderOf_dvd_of_pow_eq_one h).trans (pow_dvd_pow l (by omega)))
    have hm := gen_of_max l hl _ z h1 h0 _ le_rfl s (key c hc)
    have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, h1⟩
    obtain ⟨n, hn⟩ := hf.mem_powers_iff_mem_zpowers.2 hm
    exact ⟨n, hn.symm⟩
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    rintro s ⟨c, hc⟩
    refine ⟨0, ?_⟩
    rw [pow_zero]
    induction c with
    | zero => simpa using hc
    | succ c ih =>
      apply ih
      by_contra h
      exact hx ⟨_, by rw [← pow_mul, ← pow_succ, hc], h⟩

theorem UpperTheory.V.Ws.X1.muCyc :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) → ∃ ζ, MuGen H (muOf l H) ζ := by
  intro Γ _ _ _ _ _ _ l hp H hH hl
  unfold MuGen muOf
  have hcl : IsClosed (((⁅H, H⁆ : Subgroup Γ).topologicalClosure : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure :=
    fun a ha b hb => Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator ha hb)
  generalize (⁅H, H⁆ : Subgroup Γ).topologicalClosure = C at hl hcl hcomm ⊢
  haveI hN : (C.subgroupOf H).Normal := ⟨fun c hc h => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using mul_mem (hcomm h h.2 c c.2) hc⟩
  let π := QuotientGroup.mk' (C.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 : ∀ x : H, π x = 1 ↔ (x : Γ) ∈ C := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have h2 : ∀ x y : H, π x = π y ↔ (x : Γ) * (y : Γ)⁻¹ ∈ C := fun x y => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, h1]; simp
  letI : CommGroup (H ⧸ C.subgroupOf H) :=
    { (inferInstance : Group (H ⧸ C.subgroupOf H)) with
      mul_comm := fun a b => by
        obtain ⟨a, rfl⟩ := hπ a
        obtain ⟨b, rfl⟩ := hπ b
        rw [← map_mul, ← map_mul, h2]
        simpa [mul_assoc] using hcomm a a.2 b b.2 }
  refine (cyc_abs (A := H ⧸ C.subgroupOf H) l hp.out ?_ ?_).elim ?_
  rotate_left 2
  · rintro z ⟨⟨a, ha⟩, hz⟩
    obtain ⟨z, rfl⟩ := hπ z
    refine ⟨z, ⟨z.2, a, ?_⟩, ?_⟩
    · rw [← map_pow, h1] at ha
      simpa using ha
    · rintro s ⟨hs, c, hc⟩
      obtain ⟨n, hn⟩ := hz (π ⟨s, hs⟩) ⟨c, by rw [← map_pow, h1]; simpa using hc⟩
      rw [← map_pow, h2] at hn
      exact ⟨n, by simpa using hn⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := hπ x
    have ho : IsOpen {g : Γ | (x : Γ) * g ∉ C} :=
      hcl.isOpen_compl.preimage (continuous_const_mul (x : Γ))
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
      (by simpa [← h1] using hx)
    refine ⟨(N.toSubgroup.subgroupOf H).map π, ?_, ?_⟩
    · refine ne_zero_of_dvd_ne_zero ?_ (Subgroup.index_map_dvd _ hπ)
      haveI : Finite (Γ ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
      haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact Subgroup.FiniteIndex.index_ne_zero
    · rintro ⟨n, hn, e⟩
      have hn' : (n : Γ)⁻¹ ∈ N.toSubgroup := inv_mem (Subgroup.mem_subgroupOf.1 hn)
      exact hN hn' ((h2 x n).1 e.symm)
  · intro s t hs ht h0
    obtain ⟨s, rfl⟩ := hπ s
    obtain ⟨t, rfl⟩ := hπ t
    rw [← map_pow, h1] at hs ht
    obtain ⟨n, hn⟩ := hl s s.2 t t.2 (by simpa using hs) (by simpa using ht) (by rwa [← h1])
    exact ⟨n, by rw [← map_pow, h2]; simpa using hn⟩
