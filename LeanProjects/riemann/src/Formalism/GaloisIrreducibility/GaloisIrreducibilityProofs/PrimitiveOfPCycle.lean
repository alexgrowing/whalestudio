import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility

open scoped Pointwise

theorem poc_powSmul_injective {M Y : Type*} [Group M] [MulAction M Y] (s : M) (p : ℕ) (hp : p.Prime)
    (hs : s ^ p = 1) (y : Y) (hy : s • y ≠ y) :
    ∀ i < p, ∀ j < p, s ^ i • y = s ^ j • y → i = j := by
  have key : ∀ d : ℕ, 0 < d → d < p → s ^ d • y ≠ y := by
    intro d hd0 hdp hd
    have hnd : ¬ p ∣ d := fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)
    have hcop : Nat.Coprime d p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    have h1 : s ^ d ∈ MulAction.stabilizer M y := MulAction.mem_stabilizer_iff.mpr hd
    have h2 : s ^ p ∈ MulAction.stabilizer M y := by rw [hs]; exact one_mem _
    have hb := Nat.gcd_eq_gcd_ab d p
    rw [hcop.gcd_eq_one] at hb
    have e : s = (s ^ d) ^ (Nat.gcdA d p) * (s ^ p) ^ (Nat.gcdB d p) := by
      rw [← zpow_natCast s d, ← zpow_natCast s p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb,
        Nat.cast_one, zpow_one]
    have h3 : s ∈ MulAction.stabilizer M y := by
      rw [e]; exact mul_mem (zpow_mem h1 _) (zpow_mem h2 _)
    exact hy (MulAction.mem_stabilizer_iff.mp h3)
  have step : ∀ i j : ℕ, i < j → j < p → s ^ i • y = s ^ j • y → False := by
    intro i j hij hjp h
    apply key (j - i) (by omega) (by omega)
    have h' : s ^ i • (s ^ (j - i) • y) = s ^ i • y := by
      rw [smul_smul, ← pow_add, show i + (j - i) = j by omega]
      exact h.symm
    exact (smul_left_cancel_iff _).mp h'
  intro i hi j hj hij
  rcases lt_trichotomy i j with h | h | h
  · exact (step i j h hj hij).elim
  · exact h
  · exact (step j i h hi hij.symm).elim

theorem primitive_of_p_cycle : PrimitiveOfPCycle := by
  unfold PrimitiveOfPCycle
  intro α _ _ G σ p hp hσG hcyc hsupp hcard htr
  refine @MulAction.IsPreprimitive.mk _ _ _ htr ?_
  intro B hB
  by_contra hcon
  unfold MulAction.IsTrivialBlock at hcon
  rw [not_or] at hcon
  obtain ⟨hns, hnt⟩ := hcon
  obtain ⟨b, hb, c, hc, hbc⟩ : ∃ b ∈ B, ∃ c ∈ B, b ≠ c := by
    by_contra h
    push_neg at h
    exact hns (fun u hu v hv => h u hu v hv)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B := by
    by_contra h
    push_neg at h
    exact hnt (Set.eq_univ_of_forall h)
  have hσp : σ ^ p = 1 := by
    rw [← hsupp, ← hcyc.orderOf]; exact pow_orderOf_eq_one σ
  obtain ⟨x, hxs⟩ : σ.support.Nonempty := Finset.card_pos.mp (by rw [hsupp]; exact hp.pos)
  obtain ⟨s, hsσ⟩ : ∃ s : G, (s : Equiv.Perm α) = σ := ⟨⟨σ, hσG⟩, rfl⟩
  have hs : s ^ p = 1 := Subtype.ext (by simp [hsσ, hσp])
  have hx : s • x ≠ x := by
    rw [Subgroup.smul_def, hsσ, Equiv.Perm.smul_def]; exact Equiv.Perm.mem_support.mp hxs
  obtain ⟨g, hgb⟩ := MulAction.exists_smul_eq G b x
  set t : G := g⁻¹ * s * g with ht
  have htp : t ^ p = 1 := by
    have e : ∀ i : ℕ, t ^ i = g⁻¹ * s ^ i * g := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, ih, ht, pow_succ]; group
    rw [e, hs]; group
  have htb : t • b ≠ b := by
    intro h
    apply hx
    have h2 : g • (t • b) = g • b := by rw [h]
    rw [ht, mul_smul, mul_smul, smul_inv_smul, hgb] at h2
    exact h2
  have blk : ∀ g₁ g₂ : G, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B) := by
    intro g₁ g₂ hne
    rcases hB.smul_eq_or_disjoint (g₂⁻¹ * g₁) with h | h
    · exfalso; apply hne
      rw [mul_smul] at h
      calc g₁ • B = g₂ • (g₂⁻¹ • g₁ • B) := (smul_inv_smul g₂ _).symm
        _ = g₂ • B := by rw [h]
    · rw [Set.disjoint_left]
      intro a ha1 ha2
      rw [Set.mem_smul_set_iff_inv_smul_mem] at ha1 ha2
      have h3 : g₂⁻¹ • a ∈ (g₂⁻¹ * g₁) • B := by
        rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
        exact ha1
      exact Set.disjoint_left.mp h h3 ha2
  rcases hB.smul_eq_or_disjoint t with hE | hD
  · have hpow : ∀ i : ℕ, t ^ i • b ∈ B := by
      intro i
      induction i with
      | zero => simpa using hb
      | succ i ih =>
        rw [pow_succ', mul_smul, ← hE]
        exact Set.smul_mem_smul_set ih
    obtain ⟨h, hhb⟩ := MulAction.exists_smul_eq G b z
    have hne : h • B ≠ B := by
      intro e; apply hz; rw [← e, ← hhb]; exact Set.smul_mem_smul_set hb
    have hdis : Disjoint (h • B) B := by
      have h4 := blk h 1 (by rwa [one_smul])
      rwa [one_smul] at h4
    let f : Fin p ⊕ Fin p → α :=
      Sum.elim (fun i => t ^ (i : ℕ) • b) (fun i => h • (t ^ (i : ℕ) • b))
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        exact congrArg Sum.inl (Fin.ext (poc_powSmul_injective t p hp htp b htb i i.2 j j.2 hij))
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact (Set.disjoint_left.mp hdis (Set.smul_mem_smul_set (hpow j))
          (by rw [← hij]; exact hpow i)).elim
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact (Set.disjoint_left.mp hdis (Set.smul_mem_smul_set (hpow i))
          (by rw [hij]; exact hpow j)).elim
      · simp only [f, Sum.elim_inr] at hij
        exact congrArg Sum.inr (Fin.ext (poc_powSmul_injective t p hp htp b htb i i.2 j j.2
          ((smul_left_cancel_iff h).mp hij)))
    have hcd := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd
    omega
  · have htB : t • B ≠ B := by
      intro e; rw [e] at hD
      exact Set.disjoint_left.mp hD hb hb
    have hinj := poc_powSmul_injective t p hp htp B htB
    have key : ∀ i j : Fin p, ∀ u v : α, u ∈ B → v ∈ B → t ^ (i : ℕ) • u = t ^ (j : ℕ) • v → i = j := by
      intro i j u v hu hv e
      by_contra hij
      have hne : t ^ (i : ℕ) • B ≠ t ^ (j : ℕ) • B := fun h => hij (Fin.ext (hinj i i.2 j j.2 h))
      exact Set.disjoint_left.mp (blk _ _ hne) (Set.smul_mem_smul_set hu)
        (by rw [e]; exact Set.smul_mem_smul_set hv)
    let f : Fin p ⊕ Fin p → α := Sum.elim (fun i => t ^ (i : ℕ) • b) (fun i => t ^ (i : ℕ) • c)
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        have := key i j b b hb hb hij; subst this; rfl
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        have := key i j b c hb hc hij; subst this
        exact absurd ((smul_left_cancel_iff _).mp hij) hbc
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        have := key i j c b hc hb hij; subst this
        exact absurd ((smul_left_cancel_iff _).mp hij).symm hbc
      · simp only [f, Sum.elim_inr] at hij
        have := key i j c c hc hc hij; subst this; rfl
    have hcd := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd
    omega

end Formalism.GaloisIrreducibility
