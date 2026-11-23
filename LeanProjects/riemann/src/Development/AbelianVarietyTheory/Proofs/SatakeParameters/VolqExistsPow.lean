import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv

noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col GlobalTheory.TopStep

theorem volq_index {G : Type} [Group G] (H : Subgroup G) {q k : ℕ} (hq : q.Prime) (h : ∀ g : G, g ^ q ^ k ∈ H) :
    H.index = 0 ∨ ∃ e : ℕ, H.index = q ^ e := by
  by_cases h0 : H.index = 0
  · exact Or.inl h0
  right
  haveI : H.FiniteIndex := ⟨h0⟩
  haveI := Fact.mk hq
  have hp : IsPGroup q (G ⧸ H.normalCore) := by
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    intro b
    have := h (b * g * b⁻¹)
    rwa [conj_pow] at this
  obtain ⟨e, he⟩ := IsPGroup.iff_card.1 hp
  have hd : H.index ∣ q ^ e := by
    rw [← he]
    exact Subgroup.index_dvd_of_le H.normalCore_le
  obtain ⟨e', -, he'⟩ := (Nat.dvd_prime_pow hq).1 hd
  exact ⟨e', he'⟩

theorem volq_choose {q : ℕ} (hq : q.Prime) (a c i : ℕ) (h0 : i ≠ 0) (hi : i ≤ c) : q ^ a ∣ (q ^ (a + c)).choose i := by
  by_cases h : i ≤ q ^ (a + c)
  · have h1 := Nat.factorization_choose_prime_pow_add_factorization hq h h0
    have h2 := Nat.factorization_lt q h0
    rw [hq.pow_dvd_iff_le_factorization (Nat.choose_pos h).ne']
    omega
  · rw [Nat.choose_eq_zero_of_lt (not_le.1 h)]
    exact dvd_zero _

theorem volq_pow_mem {V : Type} [AddCommGroup V] (A B : AddSubgroup V) {q : ℕ} (hq : q.Prime) (b c : ℕ)
    (hAB : ∀ v ∈ A, q ^ b • v ∈ B) (hBA : ∀ v ∈ B, q ^ b • v ∈ A) (r : Module.End ℤ V) (hr : ∀ v ∈ B, r v ∈ B)
    (hn : (r - 1) ^ (c + 1) = 0) : ∀ v ∈ A, (r ^ q ^ (2 * b + c)) v ∈ A := by
  intro v hv
  have hν : ∀ i : ℕ, ∀ v ∈ B, ((r - 1) ^ i) v ∈ B := by
    intro i
    induction i with
    | zero => intro v hv; simpa using hv
    | succ i ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (B.sub_mem (hr v hv) hv)
  have e : r = (r - 1) + 1 := by simp
  rw [e, (Commute.one_right _).add_pow, LinearMap.sum_apply]
  refine A.sum_mem fun i _ => ?_
  rw [one_pow, mul_one, ← nsmul_eq_mul', LinearMap.smul_apply]
  rcases eq_or_ne i 0 with rfl | h0
  · simpa using hv
  by_cases hi : i ≤ c
  · obtain ⟨t, ht⟩ := volq_choose hq (2 * b) c i h0 hi
    have h1 := hBA _ (hν i _ (hAB v hv))
    rw [map_nsmul, smul_smul, ← pow_add, ← two_mul] at h1
    rw [ht, mul_comm, mul_smul]
    exact A.nsmul_mem h1 t
  · rw [pow_eq_zero_of_le (by omega) hn]
    simpa using A.zero_mem

section Nil

variable {k : Type} [CommRing k] {n c : ℕ}

theorem volq_lower {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) (i : ℕ) :
    ∀ v ∈ Loc.Ufl k n c (i + 1), r v - v ∈ Loc.Ufl k n c i := by
  intro v hv
  have h1 : v - Loc.atN v (n + i) • Loc.eN k (n + c) (n + i) ∈ Loc.Ufl k n c i := by
    intro l hl
    by_cases h : l.1 = n + i
    · have h2 : n + i < n + c := h ▸ l.2
      have h3 : l = ⟨n + i, h2⟩ := Fin.ext h
      subst h3
      simp [Loc.atN, Loc.eN, h2]
    · have := hv l (by simp only [Set.mem_setOf_eq] at hl ⊢; omega)
      simp [Loc.eN, h, this]
  have h2 := hr.1.1.1 i _ h1
  have h3 := (Loc.Ufl k n c i).smul_mem (Loc.atN v (n + i)) (hr.1.1.2.2 i)
  have h4 := add_mem (sub_mem h2 h1) h3
  convert h4 using 1
  simp only [map_sub, map_smul, smul_sub]
  abel

theorem volq_zero {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) :
    ∀ v ∈ Loc.Ufl k n c 0, r v - v = 0 := by
  intro v hv
  have e : v = Loc.inX k n c fun l => v (Fin.castAdd c l) := by
    funext l
    by_cases h : l.1 < n
    · simp [Loc.inX, h]
    · simp only [Loc.inX, LinearMap.pi_apply, h, dif_neg, not_false_eq_true, LinearMap.zero_apply]
      exact hv l (by simpa using h)
  rw [sub_eq_zero, e]
  exact hr.2 _

theorem volq_nil {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.N1 k n c) :
    ((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Fin (n + c) → k)) - 1) ^ (c + 1) = 0 := by
  have h : ∀ i, ∀ v ∈ Loc.Ufl k n c i,
      (((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Fin (n + c) → k)) - 1) ^ (i + 1)) v = 0 := by
    intro i
    induction i with
    | zero => intro v hv; simpa using volq_zero hr v hv
    | succ i ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (volq_lower hr i v hv)
  exact LinearMap.ext fun v => h c v fun l hl => absurd l.2 hl

end Nil

section Loc

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem volq_exists_pow (a : E) : ∃ b : ℕ, IntAt P ((qOf P : E) ^ b * a) := by
  have hq : P.valuation E (qOf P : E) < 1 := by
    have := (P.valuation_lt_one_iff_mem (K := E) _).2 (qOf_mem (P := P))
    change P.valuation E (algebraMap (𝓞 E) E _) < 1 at this
    rwa [map_natCast] at this
  have : ∃ b : ℕ, P.valuation E ((qOf P : E) ^ b * a) ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, by simp⟩
    have h0 : P.valuation E a ≠ 0 := (map_ne_zero _).2 ha
    obtain ⟨b, hb⟩ := exists_pow_lt₀ hq (Units.mk0 _ h0)⁻¹
    refine ⟨b, ?_⟩
    rw [map_mul, map_pow, ← le_mul_inv_iff₀ (zero_lt_iff.2 h0), one_mul]
    simpa using hb.le
  obtain ⟨b, hb⟩ := this
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer _ hb
  exact ⟨b, n, d, d.2, by rw [mul_comm]; exact h⟩

variable [StarRing E]

theorem volq_bound {N : ℕ} (f : Sp E N →ₗ[E] Sp E N) :
    ∃ b : ℕ, ∀ b', b ≤ b' → ∀ v ∈ stdAt E N P, qOf P ^ b' • f v ∈ stdAt E N P := by
  choose g hg using fun p : Fin N × Fin N => volq_exists_pow (P := P) (f (Pi.single p.2 1) p.1)
  refine ⟨Finset.univ.sup g, fun b' hb v hv => mem_stdAt.2 fun i => ?_⟩
  rw [Pi.smul_apply, apply_eq_sum, nsmul_eq_mul, Finset.mul_sum]
  refine intAt_sum _ fun j _ => ?_
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le ((Finset.le_sup (f := g) (Finset.mem_univ (i, j))).trans hb)
  have := ((mem_stdAt.1 hv j).mul (hg (i, j))).mul (intAt_pow (intAt_nat (qOf P)) t)
  convert this using 1
  push_cast
  ring

theorem volq_lamY {n c : ℕ} : LocE.lamY P (qOf P) n c 0 = stdAt E (n + c) P := by
  ext v
  unfold LocE.lamY LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt, mem_stdAt]
  simp [LocE.scE]

theorem volq_relIndex (hq : (qOf P).Prime) {n c : ℕ} (J : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)))
    (hJ : J ≤ stabL E _ (stdAt E (n + c) P)) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :
    (Loc.N1 E n c ⊓ stabL E _ (stdAt E (n + c) P)).relIndex (Loc.Cbe J h ⊓ Loc.N1 E n c) = 0 ∨
    ∃ e : ℕ, (Loc.N1 E n c ⊓ stabL E _ (stdAt E (n + c) P)).relIndex (Loc.Cbe J h ⊓ Loc.N1 E n c) = qOf P ^ e := by
  obtain ⟨b₁, h₁⟩ := volq_bound (P := P) h.toLinearMap
  obtain ⟨b₂, h₂⟩ := volq_bound (P := P) h.symm.toLinearMap
  have key : ∀ r ∈ Loc.Cbe J h ⊓ Loc.N1 E n c, ∀ v ∈ stdAt E (n + c) P,
      (r ^ qOf P ^ (2 * (b₁ + b₂) + c)) v ∈ stdAt E (n + c) P := by
    intro r hr v hv
    have hs : h⁻¹ * r * h ∈ stabL E _ (stdAt E (n + c) P) := by
      have := hJ (Subgroup.mem_comap.1 hr.1.2)
      simpa using this
    have := volq_pow_mem (stdAt E (n + c) P).toAddSubgroup
      ((stdAt E (n + c) P).toAddSubgroup.comap h.symm.toLinearMap.toAddMonoidHom) hq (b₁ + b₂) c
      (fun v hv => ?_) (fun v hv => ?_) (r.toLinearMap.restrictScalars ℤ) (fun v hv => ?_) (volq_nil hr.2) v hv
    · have e : ∀ m : ℕ, ((r.toLinearMap.restrictScalars ℤ : Module.End ℤ (Sp E (n + c))) ^ m) v = (r ^ m) v := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih]; rfl
      rw [e] at this
      exact this
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h₂ _ (by omega) v hv
    · have := h₁ (b₁ + b₂) (by omega) _ hv
      simpa using this
    · have := (hs (h.symm v)).2 hv
      change h.symm (r (h (h.symm v))) ∈ _ at this
      rw [h.apply_symm_apply] at this
      exact this
  refine volq_index _ hq (k := 2 * (b₁ + b₂) + c) fun g => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  refine ⟨pow_mem g.2.2 _, fun v => ⟨fun hv => ?_, key g.1 g.2 v⟩⟩
  have := key g.1⁻¹ (inv_mem g.2) _ hv
  rw [inv_pow] at this
  change (g.1 ^ _).symm _ ∈ _ at this
  rwa [LinearEquiv.symm_apply_apply] at this

end Loc

theorem volumeAtQ : VolumeAtQ := by
  intro X Pr R sharp j P h w hP hd hw
  unfold Loc.volN Jat lamYat
  simp only [if_neg hP]
  rw [volq_lamY, inv_div, map_div₀]
  have hn : ∀ m : ℕ, w.valuation X.K (m : X.K) ≤ 1 := fun m => by
    have := w.valuation_le_one (K := X.K) (m : 𝓞 X.K)
    change w.valuation X.K (algebraMap (𝓞 X.K) X.K _) ≤ 1 at this
    rwa [map_natCast] at this
  have hq : w.valuation X.K (qOf P : X.K) = 1 := by
    have := (w.valuation_eq_one_iff_notMem (K := X.K)).2 hw
    rwa [map_natCast] at this
  rcases volq_relIndex hd.1 (LocE.JQ P (qOf P) (R.k + j) (R.N j) (cOf R j)) inf_le_left h with h0 | ⟨e, he⟩
  · rw [h0]
    simp
  · rw [he, Nat.cast_pow, map_pow, hq, one_pow, div_one]
    exact hn _

end GlobalTheory.ColPeriod
