import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CmIdealGlue

variable {Λ : Type} [CommRing Λ]

theorem natCast_tmul (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (b : Λ) :
    ((n : ℤ_[ℓ]) ⊗ₜ[ℤ] b) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] ((n : Λ) * b) := by
  rw [← nsmul_one, TensorProduct.smul_tmul, nsmul_eq_mul]

theorem natCast_eq (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ((n : ℤ_[ℓ] ⊗[ℤ] Λ)) = (n : ℤ_[ℓ]) ⊗ₜ[ℤ] (1 : Λ) := by
  rw [← Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast]

theorem exists_decomp (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (x : ℤ_[ℓ] ⊗[ℤ] Λ) :
    ∃ a : Λ, ∃ r : ℤ_[ℓ] ⊗[ℤ] Λ, x = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a + ((ℓ : ℤ_[ℓ] ⊗[ℤ] Λ) ^ k) * r := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z b =>
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec k z)
    refine ⟨(PadicInt.appr z k : Λ) * b, w ⊗ₜ[ℤ] b, ?_⟩
    have hz : z = (PadicInt.appr z k : ℤ_[ℓ]) + (ℓ : ℤ_[ℓ]) ^ k * w := by rw [mul_comm, hw]; ring
    conv_lhs => rw [hz]
    have hl : ((ℓ : ℤ_[ℓ] ⊗[ℤ] Λ)) ^ k = ((ℓ : ℤ_[ℓ]) ^ k) ⊗ₜ[ℤ] (1 : Λ) := by
      rw [natCast_eq, Algebra.TensorProduct.tmul_pow, one_pow]
    rw [TensorProduct.add_tmul, natCast_tmul, hl, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy =>
    obtain ⟨a, r, rfl⟩ := hx
    obtain ⟨a', r', rfl⟩ := hy
    exact ⟨a + a', r + r', by rw [TensorProduct.tmul_add]; ring⟩

theorem isUnit_natCast (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (n : ℕ) (hn : ¬ ℓ ∣ n) :
    IsUnit (n : ℤ_[ℓ] ⊗[ℤ] Λ) := by
  have h : IsUnit (n : ℤ_[ℓ]) := PadicInt.isUnit_iff.mpr
    (PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hn))
  simpa using h.map (Algebra.TensorProduct.includeLeftRingHom : ℤ_[ℓ] →+* ℤ_[ℓ] ⊗[ℤ] Λ)

theorem castRingHom_pow_eq_zero (ℓ k : ℕ) :
    (Int.castRingHom (Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)})) ((ℓ ^ k : ℕ) : ℤ) = 0 := by
  rw [eq_intCast, Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

noncomputable def padicToQuot (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    ℤ_[ℓ] →+* Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)} :=
  ((Ideal.Quotient.lift (Ideal.span {((ℓ ^ k : ℕ) : ℤ)})
      (Int.castRingHom (Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)})) (fun a ha => by
        obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, castRingHom_pow_eq_zero, mul_zero])).comp
    (Int.quotientSpanNatEquivZMod (ℓ ^ k)).symm.toRingHom).comp (PadicInt.toZModPow k)

noncomputable def toQuot (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) :
    ℤ_[ℓ] ⊗[ℤ] Λ →+* Λ ⧸ Ideal.span {((ℓ ^ k : ℕ) : Λ)} :=
  (Algebra.TensorProduct.lift (padicToQuot ℓ k).toIntAlgHom (Ideal.Quotient.mk _).toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toQuot_tmul (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ) (a : Λ) :
    toQuot ℓ k ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) = Ideal.Quotient.mk _ a := by
  simp [toQuot]

theorem exists_coprime_mul_mem (J : Ideal Λ) (m : ℕ) (hm : 0 < m) (hmJ : (m : Λ) ∈ J) (x : Λ)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hx : (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ) x ∈
      J.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom) :
    ∃ n : ℕ, 0 < n ∧ ¬ ℓ ∣ n ∧ (n : Λ) * x ∈ J := by
  obtain ⟨k, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.one_lt.ne'
  refine ⟨n, Nat.pos_of_ne_zero (by rintro rfl; simp at hmn; omega), hn, ?_⟩
  have h1 := Ideal.mem_map_of_mem (toQuot (Λ := Λ) ℓ k) hx
  rw [Ideal.map_map] at h1
  have hcomp : (toQuot (Λ := Λ) ℓ k).comp
      (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.Quotient.mk _ := by
    ext a; simp [toQuot_tmul]
  rw [hcomp] at h1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    toQuot_tmul] at h1
  obtain ⟨j, hj, hjx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hjx.symm)
  have : (n : Λ) * x = n * j + t * m := by
    rw [hmn, Nat.cast_mul]
    have : x = j + t * ((ℓ ^ k : ℕ) : Λ) := by rw [ht]; ring
    rw [this]; ring
  rw [this]
  exact J.add_mem (J.mul_mem_left _ hj) (J.mul_mem_left _ hmJ)

theorem mem_of_forall_map (J : Ideal Λ) (m : ℕ) (hm : 0 < m) (hmJ : (m : Λ) ∈ J) (x : Λ)
    (hx : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ) x ∈
      J.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom) :
    x ∈ J := by
  classical
  have hex : ∃ g : ℕ, 0 < g ∧ (g : Λ) * x ∈ J := ⟨m, hm, J.mul_mem_right _ hmJ⟩
  set g := Nat.find hex with hg
  obtain ⟨hg0, hgJ⟩ := Nat.find_spec hex

  have hdvd : ∀ n : ℕ, 0 < n → (n : Λ) * x ∈ J → g ∣ n := by
    intro n hn hnJ
    have hgcd0 : 0 < Nat.gcd g n := Nat.gcd_pos_of_pos_left _ hg0
    have hgcdJ : ((Nat.gcd g n : ℕ) : Λ) * x ∈ J := by
      have e := Nat.gcd_eq_gcd_ab g n
      have e' : ((Nat.gcd g n : ℕ) : Λ) = (g : Λ) * ((Nat.gcdA g n : ℤ) : Λ) + (n : Λ) * ((Nat.gcdB g n : ℤ) : Λ) := by
        have := congrArg (fun z : ℤ => (z : Λ)) e
        push_cast at this
        exact this
      rw [e', add_mul]
      refine J.add_mem ?_ ?_
      · rw [mul_comm (g : Λ), mul_assoc]; exact J.mul_mem_left _ hgJ
      · rw [mul_comm (n : Λ), mul_assoc]; exact J.mul_mem_left _ hnJ
    have hle : g ≤ Nat.gcd g n := Nat.find_min' hex ⟨hgcd0, hgcdJ⟩
    have hge : Nat.gcd g n ≤ g := Nat.le_of_dvd hg0 (Nat.gcd_dvd_left g n)
    have : Nat.gcd g n = g := le_antisymm hge hle
    rw [← this]; exact Nat.gcd_dvd_right g n
  have hg1 : g = 1 := by
    by_contra hne
    have hp : (Nat.minFac g).Prime := Nat.minFac_prime hne
    haveI : Fact (Nat.minFac g).Prime := ⟨hp⟩
    obtain ⟨n, hn0, hnd, hnJ⟩ := exists_coprime_mul_mem J m hm hmJ x (Nat.minFac g) (hx _)
    exact hnd ((Nat.minFac_dvd g).trans (hdvd n hn0 hnJ))
  rw [← hg, hg1, Nat.cast_one, one_mul] at hgJ
  exact hgJ

theorem natCast_eq_tmul (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (n : ℤ_[ℓ] ⊗[ℤ] Λ) = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] (n : Λ) := by
  rw [← Algebra.TensorProduct.includeRight_apply (R := ℤ) (A := ℤ_[ℓ]), map_natCast]

theorem natCast_mem_span_of_assoc (ℓ : ℕ) [Fact ℓ.Prime] {d e : ℤ_[ℓ] ⊗[ℤ] Λ} {D : Λ} {m : ℕ}
    (hmD : (m : Λ) ∈ Ideal.span {D}) (h : Associated (d * e) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) :
    (m : ℤ_[ℓ] ⊗[ℤ] Λ) ∈ Ideal.span {d} := by
  rw [Ideal.mem_span_singleton]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmD
  obtain ⟨u, hu⟩ := h
  refine ⟨e * u * ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] t), ?_⟩
  rw [natCast_eq_tmul, ← ht, ← one_mul (1 : ℤ_[ℓ]), ← Algebra.TensorProduct.tmul_mul_tmul, ← hu]
  ring

noncomputable def glued (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ) : Ideal Λ :=
  ⨅ (ℓ : ℕ) (_ : Fact ℓ.Prime), (Ideal.span {δ ℓ}).comap
    (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom

theorem mem_glued (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ) (x : Λ) :
    x ∈ glued δ ↔ ∀ (ℓ : ℕ) [Fact ℓ.Prime], (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] x ∈ Ideal.span {δ ℓ} := by
  simp [glued, Ideal.mem_iInf]

theorem glue : ∀ (Λ : Type) [CommRing Λ] (c : Λ →+* Λ) (D : Λ) (m : ℕ), 0 < m → (m : Λ) ∈ Ideal.span {D} →
    ∀ (δ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℤ_[ℓ] ⊗[ℤ] Λ),
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], Associated
      (δ ℓ * Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom (δ ℓ)) ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D)) →
    ∃ 𝔫 : Ideal Λ, 𝔫 * 𝔫.map c = Ideal.span {D} ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      𝔫.map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom = Ideal.span {δ ℓ} := by
  intro Λ _ c D m hm hmD δ hδ
  have hmδ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], (m : ℤ_[ℓ] ⊗[ℤ] Λ) ∈ Ideal.span {δ ℓ} :=
    fun ℓ _ => natCast_mem_span_of_assoc ℓ hmD (hδ ℓ)
  have hmN : (m : Λ) ∈ glued δ := by
    rw [mem_glued]; intro ℓ _
    rw [← natCast_eq_tmul]; exact hmδ ℓ
  have hloc : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {δ ℓ} := by
    intro ℓ hℓ
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [mem_glued] at hx
      simpa using hx ℓ
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      obtain ⟨k, n, hn, hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' ℓ hℓ.out.one_lt.ne'
      obtain ⟨a, r, hdec⟩ := exists_decomp ℓ k (δ ℓ)
      have hnu : IsUnit (n : ℤ_[ℓ] ⊗[ℤ] Λ) := isUnit_natCast ℓ n hn
      have hna : (n : Λ) * a ∈ glued δ := by
        rw [mem_glued]; intro ℓ' hℓ'
        rw [Ideal.mem_span_singleton]
        have hm' := hmδ ℓ'
        rw [Ideal.mem_span_singleton, hmn, Nat.cast_mul] at hm'
        have e : (1 : ℤ_[ℓ']) ⊗ₜ[ℤ] ((n : Λ) * a) = (n : ℤ_[ℓ'] ⊗[ℤ] Λ) * ((1 : ℤ_[ℓ']) ⊗ₜ[ℤ] a) := by
          rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rw [e]
        by_cases h : ℓ' = ℓ
        · subst h
          have hk : δ ℓ' ∣ ((ℓ' ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) := (IsUnit.dvd_mul_right hnu).mp hm'
          have e2 : (1 : ℤ_[ℓ']) ⊗ₜ[ℤ] a = δ ℓ' - ((ℓ' ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) * r := by
            rw [hdec]; push_cast; ring
          rw [e2]
          exact Dvd.dvd.mul_left (dvd_sub dvd_rfl (hk.mul_right r)) _
        · have hku : IsUnit ((ℓ ^ k : ℕ) : ℤ_[ℓ'] ⊗[ℤ] Λ) := isUnit_natCast ℓ' _ (fun hd =>
            h ((Nat.prime_dvd_prime_iff_eq hℓ'.out hℓ.out).mp (hℓ'.out.dvd_of_dvd_pow hd)))
          have : δ ℓ' ∣ (n : ℤ_[ℓ'] ⊗[ℤ] Λ) := (IsUnit.dvd_mul_left hku).mp hm'
          exact this.mul_right _
      have h1 : (n : ℤ_[ℓ] ⊗[ℤ] Λ) * ((1 : ℤ_[ℓ]) ⊗ₜ[ℤ] a) ∈
          (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
        have := Ideal.mem_map_of_mem
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom hna
        simpa [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul] using this
      have h2 : ((ℓ ^ k : ℕ) : ℤ_[ℓ] ⊗[ℤ] Λ) * (n : ℤ_[ℓ] ⊗[ℤ] Λ) ∈
          (glued δ).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
        have := Ideal.mem_map_of_mem
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom hmN
        rw [map_natCast, hmn, Nat.cast_mul] at this
        exact this
      have h1' := (Ideal.unit_mul_mem_iff_mem _ hnu).mp h1
      have h2' := (Ideal.mul_unit_mem_iff_mem _ hnu).mp h2
      rw [hdec]
      push_cast at h2'
      exact Ideal.add_mem _ h1' (Ideal.mul_mem_right _ _ h2')
  refine ⟨glued δ, ?_, hloc⟩
  have hJ1 : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (glued δ * (glued δ).map c).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D} := by
    intro ℓ _
    have hc : (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom.comp c =
        (Algebra.TensorProduct.map (AlgHom.id ℤ_[ℓ] ℤ_[ℓ]) c.toIntAlgHom).toRingHom.comp
          (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom := by
      ext a; simp
    rw [Ideal.map_mul, Ideal.map_map, hc, ← Ideal.map_map, hloc ℓ, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
    obtain ⟨u, hu⟩ := hδ ℓ
    rw [← hu, Ideal.span_singleton_mul_right_unit u.isUnit]
    rfl
  have hJ2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      (Ideal.span {D}).map (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[ℓ] ⊗[ℤ] Λ).toRingHom =
        Ideal.span {(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] D} := by
    intro ℓ _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  apply le_antisymm
  · intro x hx
    apply mem_of_forall_map _ m hm hmD x
    intro ℓ _
    rw [hJ2 ℓ, ← hJ1 ℓ]
    exact Ideal.mem_map_of_mem _ hx
  · intro x hx
    have hmm : (((m * m : ℕ)) : Λ) ∈ glued δ * (glued δ).map c := by
      rw [Nat.cast_mul]
      refine Ideal.mul_mem_mul hmN ?_
      have := Ideal.mem_map_of_mem c hmN
      rwa [map_natCast] at this
    apply mem_of_forall_map _ (m * m) (Nat.mul_pos hm hm) hmm x
    intro ℓ _
    rw [hJ1 ℓ, ← hJ2 ℓ]
    exact Ideal.mem_map_of_mem _ hx

end GlobalTheory.CmIdealGlue
