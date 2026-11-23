import Mathlib

namespace Formalism.HermitianLattices.Ext.L3.NormLifting

theorem card_fiber_mul_card_range {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (h : H) (hh : h ∈ f.range) :
    Nat.card {g : G // f g = h} * Nat.card f.range = Nat.card G := by

  obtain ⟨g0, hg0⟩ := hh
  have e1 : {g : G // f g = h} ≃ f.ker :=
    { toFun := fun g => ⟨g.1 - g0, by rw [AddMonoidHom.mem_ker, map_sub, g.2, hg0, sub_self]⟩
      invFun := fun k => ⟨k.1 + g0, by rw [map_add, (AddMonoidHom.mem_ker).mp k.2, hg0, zero_add]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun k => by ext; simp }
  rw [Nat.card_congr e1, ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv, mul_comm]
  exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker).symm

theorem card_eq_mul_of_fibers {X Y : Type*} [Finite X] (f : X → Y) (c : ℕ)
    (hc : ∀ y, Nat.card {x : X // f x = y} = c) : Nat.card X = c * Nat.card Y := by

  classical
  by_cases hY : Finite Y
  · haveI := Fintype.ofFinite Y
    haveI := Fintype.ofFinite X
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
      Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card (α := Y), mul_comm]
  · haveI : Infinite Y := not_finite_iff_infinite.mp hY
    rw [Nat.card_eq_zero_of_infinite (α := Y), mul_zero]
    obtain ⟨y, hy⟩ := (Set.finite_range f).infinite_compl.nonempty
    have hc0 : c = 0 := by
      rw [← hc y, Nat.card_eq_zero]
      left
      exact ⟨fun x => hy ⟨x.1, x.2⟩⟩
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun x => ?_⟩
    have h1 := hc (f x)
    rw [hc0, Nat.card_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact h1.false ⟨x, rfl⟩
    · exact absurd (inferInstance : Finite {x' : X // f x' = f x}) (not_finite_iff_infinite.mpr h1)

section Inv

variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)

def fixSub : AddSubgroup A where
  carrier := {w | w ∈ I ∧ σ w = w}
  zero_mem' := ⟨I.zero_mem, map_zero σ⟩
  add_mem' := fun ha hb => ⟨I.add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2]⟩
  neg_mem' := fun ha => ⟨I.neg_mem ha.1, by rw [map_neg, ha.2]⟩

theorem mem_fixSub {w : A} : w ∈ fixSub σ I ↔ w ∈ I ∧ σ w = w := Iff.rfl

variable {σ I}

theorem map_inv_eq_neg (hσ : ∀ a, σ (σ a) = a) {θ e : A} (he : (θ - σ θ) * e = 1) : σ e = -e := by

  have h1 : (θ - σ θ) * (-σ e) = 1 := by
    have h0 := congrArg σ he
    rw [map_mul, map_sub, hσ, map_one] at h0
    linear_combination h0
  have h2 : e = -σ e := by
    calc e = e * ((θ - σ θ) * (-σ e)) := by rw [h1, mul_one]
      _ = ((θ - σ θ) * e) * (-σ e) := by ring
      _ = -σ e := by rw [he, one_mul]
  linear_combination h2

theorem exists_trace (hσ : ∀ a, σ (σ a) = a) {θ e : A} (he : (θ - σ θ) * e = 1) {w : A}
    (hw : w ∈ fixSub σ I) : ∃ v ∈ I, v + σ v = w := by

  have hw' := (mem_fixSub σ I).mp hw
  refine ⟨w * (θ * e), I.mul_mem_right _ hw'.1, ?_⟩
  rw [map_mul, map_mul, hw'.2, map_inv_eq_neg hσ he]
  linear_combination w * he

def trI (σ : A →+* A) (I : Ideal A) : I →+ A :=
  AddMonoidHom.mk' (fun w => (w : A) + σ w) (fun a b => by
    simp only [Submodule.coe_add, map_add]; abel)

theorem range_trI (hσ : ∀ a, σ (σ a) = a) (hI : ∀ a ∈ I, σ a ∈ I) {θ e : A}
    (he : (θ - σ θ) * e = 1) : (trI σ I).range = fixSub σ I := by

  ext x
  rw [mem_fixSub, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    show ((w : A) + σ w) ∈ I ∧ σ ((w : A) + σ w) = (w : A) + σ w
    refine ⟨I.add_mem w.2 (hI _ w.2), ?_⟩
    rw [map_add, hσ, add_comm]
  · intro hx
    obtain ⟨v, hv, hv2⟩ := exists_trace hσ he ((mem_fixSub σ I).mpr hx)
    exact ⟨⟨v, hv⟩, hv2⟩

theorem card_fixSub_sq (hσ : ∀ a, σ (σ a) = a) (hI : ∀ a ∈ I, σ a ∈ I) {θ e : A}
    (he : (θ - σ θ) * e = 1) : Nat.card (fixSub σ I) ^ 2 = Nat.card I := by

  have hδ : σ (θ - σ θ) = -(θ - σ θ) := by
    rw [map_sub, hσ]
    ring
  have he' := map_inv_eq_neg hσ he
  have h1 := card_fiber_mul_card_range (trI σ I) 0 (zero_mem _)
  rw [range_trI hσ hI he] at h1
  have e1 : {w : I // trI σ I w = 0} ≃ fixSub σ I :=
    { toFun := fun w => ⟨e * (w.1 : A), (mem_fixSub σ I).mpr ⟨I.mul_mem_left _ w.1.2, by
          have hw : (w.1 : A) + σ (w.1 : A) = 0 := w.2
          rw [map_mul, he']
          linear_combination (-e) * hw⟩⟩
      invFun := fun x => ⟨⟨(θ - σ θ) * (x : A), I.mul_mem_left _ ((mem_fixSub σ I).mp x.2).1⟩, by
          show (θ - σ θ) * (x : A) + σ ((θ - σ θ) * (x : A)) = 0
          rw [map_mul, hδ, ((mem_fixSub σ I).mp x.2).2]
          ring⟩
      left_inv := fun w => by
        apply Subtype.ext
        apply Subtype.ext
        show (θ - σ θ) * (e * (w.1 : A)) = w.1
        rw [← mul_assoc, he, one_mul]
      right_inv := fun x => by
        apply Subtype.ext
        show e * ((θ - σ θ) * (x : A)) = x
        rw [← mul_assoc, mul_comm e, he, one_mul] }
  rw [Nat.card_congr e1] at h1
  rw [sq]
  exact h1

end Inv

section Lift

variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

def linPart (σ : A →+* A) (I : Ideal A) {M : ℕ} (y : Fin M → A) : (Fin M → I) →+ A :=
  AddMonoidHom.mk' (fun δ => ∑ i, (σ (y i) * (δ i : A) + σ (δ i) * y i)) (fun a b => by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Submodule.coe_add, map_add]; ring)

theorem linPart_apply (I : Ideal A) {M : ℕ} (y : Fin M → A) (δ : Fin M → I) :
    linPart σ I y δ = ∑ i, (σ (y i) * (δ i : A) + σ (δ i) * y i) := rfl

theorem range_linPart (hσ : ∀ a, σ (σ a) = a) {I : Ideal A} (hI : ∀ a ∈ I, σ a ∈ I)
    (hsq : ∀ a ∈ I, ∀ b ∈ I, a * b = 0) {θ e : A} (he : (θ - σ θ) * e = 1) {n m : A}
    (hnm : n * m = 1) {M : ℕ} (y : Fin M → A) (hy : n - ∑ i, σ (y i) * y i ∈ I) :
    (linPart σ I y).range = fixSub σ I := by

  ext w
  rw [mem_fixSub, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨δ, rfl⟩
    rw [linPart_apply]
    constructor
    · exact sum_mem (fun i _ => I.add_mem (I.mul_mem_left _ (δ i).2) (I.mul_mem_right _ (hI _ (δ i).2)))
    · rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [map_add, map_mul, hσ]
      ring
  · rintro ⟨hwI, hwσ⟩
    obtain ⟨v, hv, hv2⟩ := exists_trace hσ he ((mem_fixSub σ I).mpr ⟨hwI, hwσ⟩)
    refine ⟨fun i => ⟨y i * (m * v), I.mul_mem_left _ (I.mul_mem_left _ hv)⟩, ?_⟩
    rw [linPart_apply]
    have hs : ∑ i, σ (y i) * (y i * (m * v)) = v := by
      have h1 : ∑ i, σ (y i) * (y i * (m * v)) = (∑ i, σ (y i) * y i) * (m * v) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [h1]
      have h2 := hsq _ hy _ hv
      linear_combination (-m) * h2 + v * hnm
    calc ∑ i, (σ (y i) * ((⟨y i * (m * v), I.mul_mem_left _ (I.mul_mem_left _ hv)⟩ : I) : A) +
          σ ((⟨y i * (m * v), I.mul_mem_left _ (I.mul_mem_left _ hv)⟩ : I) : A) * y i)
        = ∑ i, σ (y i) * (y i * (m * v)) + σ (∑ i, σ (y i) * (y i * (m * v))) := by
          rw [Finset.sum_add_distrib, map_sum]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [map_mul, hσ]
          ring
      _ = w := by rw [hs, hv2]

theorem card_lift [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n m : A} (hnm : n * m = 1) (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) :
    Nat.card {x : Fin M → A // ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // ∑ i, τ (x i) * x i = π n} := by

  classical
  let I : Ideal A := RingHom.ker π
  have hmemI : ∀ a, a ∈ I ↔ π a = 0 := fun a => RingHom.mem_ker
  have hI : ∀ a ∈ I, σ a ∈ I := by
    intro a ha
    rw [hmemI] at ha ⊢
    rw [hστ, ha, map_zero]
  have hsqI : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := fun a ha b hb => hsq a b ((hmemI a).mp ha) ((hmemI b).mp hb)
  haveI : Finite B := Finite.of_surjective π hπ
  have hAIB : Nat.card I * Nat.card B = Nat.card A := by
    have h1 := card_fiber_mul_card_range π.toAddMonoidHom 0 (zero_mem _)
    have e1 : {g : A // π.toAddMonoidHom g = 0} ≃ I :=
      { toFun := fun g => ⟨g.1, (hmemI _).mpr g.2⟩
        invFun := fun g => ⟨g.1, (hmemI _).mp g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
    have e2 : (π.toAddMonoidHom.range) ≃ B :=
      { toFun := fun b => b.1
        invFun := fun b => ⟨b, (hπ b).elim fun a ha => ⟨a, ha⟩⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
    rw [Nat.card_congr e1, Nat.card_congr e2] at h1
    exact h1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hq
      simp at hq
      omega
    · exact h
  have hIcard : Nat.card I = q ^ 2 := by
    have h1 := hAIB
    rw [hq] at h1
    exact Nat.eq_of_mul_eq_mul_right hBpos h1
  have hFix : Nat.card (fixSub σ I) = q := by
    have h1 := card_fixSub_sq hσ hI he
    rw [hIcard] at h1
    exact Nat.pow_left_injective (by norm_num) h1
  let Φ : {x : Fin M → A // ∑ i, σ (x i) * x i = n} → {x : Fin M → B // ∑ i, τ (x i) * x i = π n} :=
    fun x => ⟨fun i => π (x.1 i), by
      have h1 : ∑ i, τ (π (x.1 i)) * π (x.1 i) = π (∑ i, σ (x.1 i) * x.1 i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hστ])
      rw [h1, x.2]⟩
  refine card_eq_mul_of_fibers Φ _ (fun yb => ?_)
  choose lift hlift using hπ
  let y : Fin M → A := fun i => lift (yb.1 i)
  have hyπ : ∀ i, π (y i) = yb.1 i := fun i => hlift _
  have hwI : n - ∑ i, σ (y i) * y i ∈ I := by
    rw [hmemI, map_sub, map_sum]
    have h1 : ∑ i, π (σ (y i) * y i) = ∑ i, τ (yb.1 i) * yb.1 i :=
      Finset.sum_congr rfl (fun i _ => by rw [map_mul, hστ, hyπ])
    rw [h1, yb.2, sub_self]
  have hwσ : σ (n - ∑ i, σ (y i) * y i) = n - ∑ i, σ (y i) * y i := by
    rw [map_sub, hn, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hσ, mul_comm])
  have hwR : n - ∑ i, σ (y i) * y i ∈ (linPart σ I y).range := by
    rw [range_linPart hσ hI hsqI he hnm y hwI]
    exact (mem_fixSub σ I).mpr ⟨hwI, hwσ⟩
  have h1 := card_fiber_mul_card_range (linPart σ I y) _ hwR
  rw [range_linPart hσ hI hsqI he hnm y hwI, hFix] at h1
  have hcardI : Nat.card (Fin M → I) = q ^ (2 * M) := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hIcard, ← pow_mul]
  rw [hcardI] at h1
  have key : ∀ x : Fin M → A, ∀ hx : ∀ i, x i - y i ∈ I,
      ∑ i, σ (x i) * x i = ∑ i, σ (y i) * y i + linPart σ I y (fun i => ⟨x i - y i, hx i⟩) := by
    intro x hx
    rw [linPart_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h0 : σ (x i - y i) * (x i - y i) = 0 := hsqI _ (hI _ (hx i)) _ (hx i)
    simp only [map_sub] at h0 ⊢
    linear_combination h0
  have hmem : ∀ x : {x : {x : Fin M → A // ∑ i, σ (x i) * x i = n} // Φ x = yb}, ∀ i, x.1.1 i - y i ∈ I := by
    intro x i
    rw [hmemI, map_sub, hyπ]
    have h2 := congrArg (fun z : {x : Fin M → B // ∑ i, τ (x i) * x i = π n} => z.1 i) x.2
    simp only [Φ] at h2
    rw [h2, sub_self]
  have e : {x : {x : Fin M → A // ∑ i, σ (x i) * x i = n} // Φ x = yb} ≃
      {δ : Fin M → I // linPart σ I y δ = n - ∑ i, σ (y i) * y i} :=
    { toFun := fun x => ⟨fun i => ⟨x.1.1 i - y i, hmem x i⟩, by
          have h2 := key x.1.1 (hmem x)
          rw [x.1.2] at h2
          linear_combination -h2⟩
      invFun := fun δ => ⟨⟨fun i => y i + δ.1 i, by
            have h2 := key (fun i => y i + δ.1 i) (fun i => by simp [(δ.1 i).2])
            rw [h2]
            have h3 : (fun i => (⟨y i + (δ.1 i : A) - y i, by simp [(δ.1 i).2]⟩ : I)) = δ.1 := by
              funext i
              apply Subtype.ext
              simp
            rw [h3, δ.2]
            ring⟩, by
          apply Subtype.ext
          funext i
          simp only [Φ]
          rw [map_add, hyπ, (hmemI _).mp (δ.1 i).2, add_zero]⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        simp
      right_inv := fun δ => by
        apply Subtype.ext
        funext i
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e]
  have h4 : q ^ (2 * M) = q ^ (2 * M - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h4] at h1
  exact Nat.eq_of_mul_eq_mul_right hq0 h1

end Lift

end Formalism.HermitianLattices.Ext.L3.NormLifting
