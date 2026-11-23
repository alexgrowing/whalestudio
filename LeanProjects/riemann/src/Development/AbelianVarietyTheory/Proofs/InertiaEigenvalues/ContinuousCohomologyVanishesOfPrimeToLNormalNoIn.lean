import Mathlib
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

open ReciprocityTheory.Gal

namespace GlobalTheory.PrimeToNormalVanishing

section Algebra

variable {G Q R M : Type} [Group G] [Group Q] [CommRing R] [AddCommGroup M] [Module R M]
  (ρ : Representation R G M) (π : G →* Q) (J : Subgroup G) (K : Subgroup Q) [Fintype K]

theorem sum_shift [hK : K.Normal] (φ : Q → M) (a k : Q) (hk : k ∈ K) :
    ∑ i : K, φ (k * (a * i)) = ∑ i : K, φ (a * i) := by
  have h : a⁻¹ * k * a ∈ K := by simpa using hK.conj_mem k hk a⁻¹
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨_, h⟩ : K)) _ _ fun i => ?_
  simp [mul_assoc]

theorem two_variables [K.Normal] (hJK : ∀ j ∈ J, π j ∈ K)
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → M)
    (heq : ∀ g a b, F (π g * a) (π g * b) = ρ g (F a b))
    (hc : ∀ a b c, F b c - F a c + F a b = 0) :
    ∃ m : M, ∀ g, (Fintype.card K) ^ 2 • F 1 (π g) = ρ g m - m := by
  have hS : ∀ a b, ∑ i : K, ∑ j : K, F (a * i) (b * j) = 0 := by
    intro a b
    refine hinv _ fun g hg => ?_
    simp only [map_sum, ← heq]
    rw [← sum_shift K (fun x => ∑ j : K, F x (b * j)) a _ (hJK g hg)]
    exact Finset.sum_congr rfl fun i _ => sum_shift K (fun x => F _ x) b _ (hJK g hg)
  have key : ∀ a b, (Fintype.card K) ^ 2 • F a b =
      Fintype.card K • ∑ i : K, F a (a * i) - Fintype.card K • ∑ i : K, F b (b * i) := by
    intro a b
    have e : ∀ a' b', F a b = F a' b' + F a a' - F b b' := by
      intro a' b'
      have e1 := hc a a' b'
      have e2 := hc a b b'
      rw [← sub_eq_zero, ← sub_self (0 : M)]
      nth_rewrite 1 [← e2]
      rw [← e1]; abel
    calc _ = ∑ i : K, ∑ j : K, F a b := by simp [pow_two, mul_smul]
      _ = ∑ i : K, ∑ j : K, (F (a * i) (b * j) + F a (a * i) - F b (b * j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e _ _
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, zero_add, Finset.sum_const,
          Finset.card_univ, ← Finset.smul_sum]
  refine ⟨-(Fintype.card K • ∑ i : K, F 1 (1 * i)), fun g => ?_⟩
  rw [key, map_neg, map_nsmul, map_sum]
  simp only [← heq, mul_one, one_mul]
  abel

theorem three_variables [K.Normal] (hJK : ∀ j ∈ J, π j ∈ K)
    (hinv : ∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) (F : Q → Q → Q → M)
    (heq : ∀ g a b c, F (π g * a) (π g * b) (π g * c) = ρ g (F a b c))
    (hc : ∀ a b c d, F b c d - F a c d + F a b d - F a b c = 0) :
    ∃ H : Q → M, ∀ g h, (Fintype.card K) ^ 3 • F 1 (π g) (π (g * h)) =
      ρ g (H (π h)) - H (π (g * h)) + H (π g) := by
  have hS : ∀ a b c, ∑ i : K, ∑ j : K, ∑ k : K, F (a * i) (b * j) (c * k) = 0 := by
    intro a b c
    refine hinv _ fun g hg => ?_
    simp only [map_sum, ← heq]
    rw [← sum_shift K (fun x => ∑ j : K, ∑ k : K, F x (b * j) (c * k)) a _ (hJK g hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_shift K (fun x => ∑ k : K, F _ x (c * k)) b _ (hJK g hg)]
    exact Finset.sum_congr rfl fun i _ => sum_shift K (fun x => F _ _ x) c _ (hJK g hg)
  let H : Q → Q → M := fun a b =>
    Fintype.card K • ∑ i : K, ∑ j : K, (F a b (b * j) - F a (a * i) (b * j))
  have key : ∀ a b c, (Fintype.card K) ^ 3 • F a b c = H b c - H a c + H a b := by
    intro a b c
    have e : ∀ a' b' c', F a b c = F a' b' c' + (F b c c' - F b b' c') - (F a c c' - F a a' c')
        + (F a b b' - F a a' b') := by
      intro a' b' c'
      have e1 := hc a a' b' c'
      have e2 := hc a b b' c'
      have e3 := hc a b c c'
      have e4 : (0 : M) = 0 - 0 - 0 := by simp
      rw [← sub_eq_zero, e4]
      nth_rewrite 1 [← e2]
      nth_rewrite 1 [← e1]
      rw [← e3]; abel
    calc _ = ∑ i : K, ∑ j : K, ∑ k : K, F a b c := by simp [pow_succ, mul_smul]
      _ = ∑ i : K, ∑ j : K, ∑ k : K, (F (a * i) (b * j) (c * k) +
          (F b c (c * k) - F b (b * j) (c * k)) - (F a c (c * k) - F a (a * i) (c * k))
          + (F a b (b * j) - F a (a * i) (b * j))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => e _ _ _
      _ = _ := by
        simp only [H, Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, zero_add, Finset.sum_const,
          Finset.card_univ, ← Finset.smul_sum, smul_sub]
  have hH : ∀ g a b, H (π g * a) (π g * b) = ρ g (H a b) := by
    intro g a b
    simp only [H, map_nsmul, map_sum, map_sub, ← heq, mul_assoc]
  refine ⟨H 1, fun g h => ?_⟩
  rw [key, ← hH, mul_one, map_mul]

theorem exists_inverse {X : Type} [Finite X] (l N : ℕ) (hN : Nat.Coprime N l)
    (htor : ∀ m : M, ∃ n, l ^ n • m = 0) (φ : X → M) : ∃ a : ℤ, ∀ x, a • N • φ x = φ x := by
  choose n hn using htor
  obtain ⟨k, hk⟩ := (Set.finite_range fun x => n (φ x)).bddAbove
  have h0 : ∀ x, l ^ k • φ x = 0 := fun x => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (hk ⟨x, rfl⟩)
    rw [hd, pow_add, mul_smul, hn, smul_zero]
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (hN.pow_right k)
  refine ⟨a, fun x => ?_⟩
  have : (a * N + b * (l ^ k : ℕ)) • φ x = φ x := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, h0, smul_zero, add_zero] at this

theorem card_coprime (l : ℕ) (hl : l.Prime) (h : ∀ k ∈ K, ∃ n, Nat.Coprime n l ∧ k ^ n = 1) :
    Nat.Coprime (Fintype.card K) l := by
  rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
  obtain ⟨n, hn, hxn⟩ := h x x.2
  have : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxn))
  rw [hx] at this
  exact hl.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hn this dvd_rfl)

end Algebra

theorem exists_level {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace M]
    [DiscreteTopology M] (F : Γ × Γ × Γ → M) (hF : Continuous F) :
    ∃ U : OpenNormalSubgroup Γ, ∃ F' : Γ ⧸ U.toSubgroup → Γ ⧸ U.toSubgroup → Γ ⧸ U.toSubgroup → M,
      ∀ a b c : Γ, F' a b c = F (a, b, c) := by
  have h1 : ∀ᶠ u in nhds (1 : Γ × Γ × Γ), ∀ x ∈ (Set.univ : Set (Γ × Γ × Γ)), F (x * u) = F x := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ => ?_
    have ho : IsOpen {z : (Γ × Γ × Γ) × (Γ × Γ × Γ) | F (z.2 * z.1) = F z.2} :=
      (isOpen_discrete {p : M × M | p.1 = p.2}).preimage
        (f := fun z : (Γ × Γ × Γ) × (Γ × Γ × Γ) => (F (z.2 * z.1), F z.2)) (by fun_prop)
    exact ho.mem_nhds (by simp)
  obtain ⟨A, hA, BC, hBC, h2⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨B, hB, C, hC, h3⟩ := mem_nhds_prod_iff.1 hBC
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (Filter.inter_mem hA (Filter.inter_mem hB hC))
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo hW1
  refine ⟨U, fun a b c => F (a.out, b.out, c.out), fun a b c => ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup a
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup b
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup c
  simp only [hu, hv, hw]
  exact h2 (a := ((u : Γ), (v : Γ), (w : Γ))) ⟨(hW (hU u.2)).1,
    h3 ⟨(hW (hU v.2)).2.1, (hW (hU w.2)).2.2⟩⟩ (a, b, c) trivial

theorem cohomology_vanishes : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  intro Γ _ _ _ _ _ _ R M _ _ _ _ _ _ ρ l J hl hJ _ hord hρ htor hinv
  classical
  have hcop : ∀ (U : OpenNormalSubgroup Γ) [Fintype (J.map (QuotientGroup.mk' U.toSubgroup))],
      Nat.Coprime (Fintype.card (J.map (QuotientGroup.mk' U.toSubgroup))) l := by
    intro U _
    refine card_coprime _ l hl ?_
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨n, hn, hjn⟩ := hord U.toSubgroup inferInstance U.isOpen j hj
    exact ⟨n, hn, by rw [← map_pow]; exact (QuotientGroup.eq_one_iff _).2 hjn⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (Submodule.eq_bot_iff _).2 fun m hm => hinv m fun j _ => hm j
  · refine Submodule.Quotient.subsingleton_iff.2 (Submodule.eq_top_iff'.2 ?_)
    rintro ⟨f, hf, hfc⟩
    obtain ⟨U, F, hF⟩ := exists_level (fun p : Γ × Γ × Γ => ρ p.1 (f (p.1⁻¹ * p.2.1)))
      (hρ.comp (continuous_fst.prodMk (hf.comp (by fun_prop))))
    haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI := Fintype.ofFinite (J.map (QuotientGroup.mk' U.toSubgroup))
    haveI := hJ.map _ (QuotientGroup.mk'_surjective U.toSubgroup)
    have hF' : ∀ a b : Γ, F a b 1 = ρ a (f (a⁻¹ * b)) := fun a b => hF a b 1
    obtain ⟨m, hm⟩ := two_variables ρ (QuotientGroup.mk' U.toSubgroup) J
      (J.map (QuotientGroup.mk' U.toSubgroup)) (fun j hj => ⟨j, hj, rfl⟩) hinv
      (fun a b => F a b 1) (by
        intro g a b
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hF']
        simp [mul_assoc]) (by
        intro a b c
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        induction c using QuotientGroup.induction_on with | H c => ?_
        have e := hfc (a⁻¹ * b) (b⁻¹ * c)
        have e' : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
        simp only [hF']
        rw [← e', e, map_add, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        abel)
    obtain ⟨a, ha⟩ := exists_inverse l _ ((hcop U).pow_left 2) htor (fun q => F 1 q 1)
    refine (mem_coboundaries1 ρ _).2 ⟨a • m, fun g => ?_⟩
    have e := ha g
    have e2 := hF 1 g 1
    have e3 := hm g
    simp only [QuotientGroup.mk'_apply] at e3
    rw [e3] at e
    rw [map_zsmul, ← smul_sub, e, ← QuotientGroup.mk_one, e2]
    simp
  · refine Submodule.Quotient.subsingleton_iff.2 (Submodule.eq_top_iff'.2 ?_)
    rintro ⟨f, hf, hfc⟩
    obtain ⟨U, F, hF⟩ := exists_level
      (fun p : Γ × Γ × Γ => ρ p.1 (f (p.1⁻¹ * p.2.1, p.2.1⁻¹ * p.2.2)))
      (hρ.comp (continuous_fst.prodMk (hf.comp (by fun_prop))))
    haveI : Finite (Γ ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
    haveI : DiscreteTopology (Γ ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
    haveI := Fintype.ofFinite (J.map (QuotientGroup.mk' U.toSubgroup))
    haveI := hJ.map _ (QuotientGroup.mk'_surjective U.toSubgroup)
    simp only at hF
    obtain ⟨H, hH⟩ := three_variables ρ (QuotientGroup.mk' U.toSubgroup) J
      (J.map (QuotientGroup.mk' U.toSubgroup)) (fun j hj => ⟨j, hj, rfl⟩) hinv F (by
        intro g a b c
        induction a using QuotientGroup.induction_on
        induction b using QuotientGroup.induction_on
        induction c using QuotientGroup.induction_on
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hF]
        simp [mul_assoc]) (by
        intro a b c d
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        induction c using QuotientGroup.induction_on with | H c => ?_
        induction d using QuotientGroup.induction_on with | H d => ?_
        have e := congrArg (ρ a) (hfc (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d))
        have e1 : a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := by group
        have e2 : b⁻¹ * c * (c⁻¹ * d) = b⁻¹ * d := by group
        rw [e1, e2, map_sub, map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel_left, map_zero] at e
        simp only [hF]
        exact e)
    obtain ⟨a, ha⟩ := exists_inverse l _ ((hcop U).pow_left 3) htor
      (fun q : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) => F 1 q.1 q.2)
    refine (separated_dvr_second_cohomology_mem ρ _).2 ⟨fun g => a • H g, ?_, ?_⟩
    · exact (continuous_of_discreteTopology (f := fun q => a • H q)).comp QuotientGroup.continuous_mk
    · funext ⟨g, h⟩
      have e := ha ((g : Γ ⧸ U.toSubgroup), ((g * h : Γ) : Γ ⧸ U.toSubgroup))
      have e2 := hF 1 g (g * h)
      have e3 := hH g h
      simp only [QuotientGroup.mk'_apply] at e3
      simp only at e
      rw [e3] at e
      rw [d1_apply, map_zsmul, ← smul_sub, ← smul_add, e, ← QuotientGroup.mk_one, e2]
      simp

end GlobalTheory.PrimeToNormalVanishing
