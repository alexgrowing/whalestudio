import Mathlib

open IsLocalRing

namespace GlobalTheory.CoeffSubring

section Basis

variable {k : Type} [Field k] {p : ℕ} {B : Set k}

theorem exists_ringHom_pow
    (hB : ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
      ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b)
    (n : ℕ) (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q) (h : ∀ b ∈ B, g b ^ p ^ n = f b) :
    ∃ σ : k →+* Q, (∀ x, σ (x ^ p ^ n) = f x) ∧ ∀ b ∈ B, σ b = g b := by
  induction n generalizing f with
  | zero => exact ⟨f, by simp, fun b hb => by simpa using (h b hb).symm⟩
  | succ n ih =>
    obtain ⟨σ₁, h1, h2⟩ := hB Q f (fun b => g b ^ p ^ n) fun b hb => by
      rw [← pow_mul, ← pow_succ, h b hb]
    obtain ⟨σ, h3, h4⟩ := ih σ₁ fun b hb => (h2 b hb).symm
    exact ⟨σ, fun x => by rw [pow_succ', pow_mul, h3, h1], h4⟩

theorem closure_pow_eq_top (hp : p.Prime) (h0 : (p : k) = 0)
    (hB : Subring.closure (Set.range (fun x : k => x ^ p) ∪ B) = ⊤) (n : ℕ) :
    Subring.closure (Set.range (fun x : k => x ^ p ^ n) ∪ B) = ⊤ := by
  have := Fact.mk hp
  have : CharP k p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  induction n with
  | zero => exact eq_top_iff.2 fun x _ => Subring.subset_closure (Or.inl ⟨x, by simp⟩)
  | succ n ih =>
    set K := Subring.closure (Set.range (fun x : k => x ^ p ^ (n + 1)) ∪ B)
    have h1 : K.comap (frobenius k p) = ⊤ := by
      rw [eq_top_iff, ← ih, Subring.closure_le]
      rintro _ (⟨x, rfl⟩ | hb)
      · exact Subring.subset_closure (Or.inl ⟨x, by simp [frobenius_def, pow_succ, pow_mul]⟩)
      · exact pow_mem (Subring.subset_closure (Or.inr hb) : _ ∈ K) p
    rw [eq_top_iff, ← hB, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | hb)
    · exact h1.ge (Subring.mem_top x)
    · exact Subring.subset_closure (Or.inr hb)

end Basis

variable {S : Type} [CommRing S] [IsLocalRing S] (p : ℕ) (L : Set S)

def level (n : ℕ) : Subring S :=
  Subring.closure (Set.range (fun x : S => x ^ p ^ n) ∪ L ∪ (maximalIdeal S ^ (n + 1) : Ideal S))

variable {p L}

theorem pow_mem_level (n : ℕ) (x : S) : x ^ p ^ n ∈ level p L n :=
  Subring.subset_closure (Or.inl (Or.inl ⟨x, rfl⟩))

theorem mem_level_of_mem {n : ℕ} {x : S} (hx : x ∈ L) : x ∈ level p L n :=
  Subring.subset_closure (Or.inl (Or.inr hx))

theorem mem_level_of_mem_pow {n : ℕ} {x : S} (hx : x ∈ maximalIdeal S ^ (n + 1)) :
    x ∈ level p L n :=
  Subring.subset_closure (Or.inr hx)

theorem mem_level_of_sub_mem {n : ℕ} {x a : S} (ha : a ∈ level p L n)
    (hx : x - a ∈ maximalIdeal S ^ (n + 1)) : x ∈ level p L n := by
  simpa using add_mem (mem_level_of_mem_pow hx) ha

theorem level_antitone : Antitone (level p L) := by
  refine antitone_nat_of_succ_le fun n => Subring.closure_le.2 ?_
  rintro _ ((⟨x, rfl⟩ | hx) | hx)
  · simpa only [pow_succ', pow_mul, SetLike.mem_coe] using pow_mem_level n (x ^ p)
  · exact mem_level_of_mem hx
  · exact mem_level_of_mem_pow (Ideal.pow_le_pow_right (by omega) hx)

theorem exists_level_sub_mem (hp : p.Prime) (h0 : (p : S) ∈ maximalIdeal S)
    (hB : Subring.closure (Set.range (fun x : ResidueField S => x ^ p) ∪ residue S '' L) = ⊤)
    (n : ℕ) (s : S) : ∃ t ∈ level p L n, s - t ∈ maximalIdeal S := by
  have h1 := closure_pow_eq_top hp
    (by rw [← map_natCast (residue S), residue_eq_zero_iff]; exact h0) hB n
  have h2 : (level p L n).map (residue S) = ⊤ := by
    rw [eq_top_iff, ← h1, Subring.closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, hx, rfl⟩)
    · obtain ⟨x, rfl⟩ := residue_surjective x
      exact ⟨_, pow_mem_level n x, map_pow _ _ _⟩
    · exact ⟨x, mem_level_of_mem hx, rfl⟩
  obtain ⟨t, ht, h⟩ := h2.ge (Subring.mem_top (residue S s))
  exact ⟨t, ht, by rw [← residue_eq_zero_iff, map_sub, h, sub_self]⟩

theorem pow_sub_pow_mem (h0 : (p : S) ∈ maximalIdeal S) {x y : S} (h : x - y ∈ maximalIdeal S)
    (n : ℕ) : x ^ p ^ n - y ^ p ^ n ∈ maximalIdeal S ^ (n + 1) :=
  SModEq.sub_mem.1 ((SModEq.sub_mem.2 h).pow_pow_add_one h0 n)

theorem exists_level_succ (h0 : (p : S) ∈ maximalIdeal S)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (n : ℕ) {s : S}
    (h : s ∈ level p L n) : ∃ t ∈ level p L (n + 1), s - t ∈ maximalIdeal S ^ (n + 1) := by
  let π := Ideal.Quotient.mk (maximalIdeal S ^ (n + 1))
  have : level p L n ≤ ((level p L (n + 1)).map π).comap π := by
    refine Subring.closure_le.2 ?_
    rintro _ ((⟨x, rfl⟩ | hx) | hx)
    · obtain ⟨t, ht, hxt⟩ := hs (n + 1) x
      exact ⟨t ^ p ^ n, pow_mem ht _, (Ideal.Quotient.eq.2 (pow_sub_pow_mem h0 hxt n)).symm⟩
    · exact ⟨_, mem_level_of_mem hx, rfl⟩
    · exact ⟨0, Subring.zero_mem _, (map_zero π).trans (Ideal.Quotient.eq_zero_iff_mem.2 hx).symm⟩
  obtain ⟨t, ht, h'⟩ := this h
  exact ⟨t, ht, Ideal.Quotient.eq.1 h'.symm⟩

theorem exists_iInf_sub_mem [IsAdicComplete (maximalIdeal S) S] (h0 : (p : S) ∈ maximalIdeal S)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (s : S) :
    ∃ a ∈ ⨅ n, level p L n, s - a ∈ maximalIdeal S := by
  choose F hF hF' using fun n (t : level p L n) => exists_level_succ h0 hs n t.2
  let u : ∀ n, level p L n := fun n =>
    Nat.rec (motive := fun n => level p L n) ⟨s, by simpa using pow_mem_level (p := p) (L := L) 0 s⟩
      (fun n t => ⟨F n t, hF n t⟩) n
  have hu : ∀ n : ℕ, (u n).1 - (u (n + 1)).1 ∈ maximalIdeal S ^ (n + 1) :=
    fun n => hF' n (u n)
  have hc : AdicCompletion.IsAdicCauchy (maximalIdeal S) S fun n => (u n).1 := by
    rw [AdicCompletion.isAdicCauchy_iff]
    exact fun n => SModEq.sub_mem.2 (by simpa using Ideal.pow_le_pow_right n.le_succ (hu n))
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' (I := maximalIdeal S) (fun n => (u n).1) hc
  have ha' : ∀ n, a - (u n).1 ∈ maximalIdeal S ^ (n + 1) := fun n => by
    have h1 : (u (n + 1)).1 - a ∈ maximalIdeal S ^ (n + 1) := by
      simpa using SModEq.sub_mem.1 (ha (n + 1))
    have := neg_mem (add_mem (hu n) h1)
    convert this using 1
    ring
  refine ⟨a, Subring.mem_iInf.2 fun n => mem_level_of_sub_mem (u n).2 (ha' n), ?_⟩
  have : a - s ∈ maximalIdeal S ^ (0 + 1) := ha' 0
  simpa using neg_mem this

theorem exists_sub_mul_mem (hp : p.Prime) (h0 : (p : S) ∈ maximalIdeal S)
    (hL : Set.InjOn (residue S) L)
    (hB : ∀ (Q : Type) [CommRing Q] (f : ResidueField S →+* Q) (g : ResidueField S → Q),
      (∀ b ∈ residue S '' L, g b ^ p = f b) →
      ∃ σ : ResidueField S →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ residue S '' L, σ b = g b)
    (hs : ∀ n s, ∃ t ∈ level p L n, s - t ∈ maximalIdeal S) (n : ℕ) {a : S}
    (ha : a ∈ level p L n) (ha' : a ∈ maximalIdeal S) :
    ∃ t ∈ level p L n, a - p * t ∈ maximalIdeal S ^ (n + 1) := by
  classical
  let J : Ideal (level p L n) :=
    Ideal.span {(p : level p L n)} ⊔ (maximalIdeal S ^ (n + 1)).comap (level p L n).subtype
  let π := Ideal.Quotient.mk J
  let ρ : level p L n →+* ResidueField S := (residue S).comp (level p L n).subtype
  have hπ : ∀ x y : level p L n, (x : S) - y ∈ maximalIdeal S ^ (n + 1) → π x = π y :=
    fun x y h => Ideal.Quotient.eq.2 (Ideal.mem_sup_right h)
  have hp0 : (p : level p L n ⧸ J) = 0 := by
    rw [← map_natCast π]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
  let φ : level p L n →+* level p L n ⧸ J :=
    { toFun := fun x => π x ^ p ^ n
      map_one' := by simp
      map_mul' := fun x y => by simp [mul_pow]
      map_zero' := by rw [map_zero, zero_pow hq]
      map_add' := fun x y => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (π x) (π y) n
        rw [map_add, hr, hp0]
        simp }
  have hρ : Function.Surjective ρ := fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    obtain ⟨t, ht, h⟩ := hs n x
    exact ⟨⟨t, ht⟩, (Ideal.Quotient.eq.2 h).symm⟩
  have hker : RingHom.ker ρ ≤ RingHom.ker φ := fun x hx => by
    have h1 : (x : S) - 0 ∈ maximalIdeal S := by simpa using (residue_eq_zero_iff _).1 hx
    have h2 := hπ (x ^ p ^ n) (0 ^ p ^ n) (pow_sub_pow_mem h0 h1 n)
    rw [zero_pow hq, map_zero, map_pow] at h2
    exact h2
  let f := ρ.liftOfSurjective hρ ⟨φ, hker⟩
  have hf : ∀ x, f (ρ x) = π x ^ p ^ n := fun x => ρ.liftOfSurjective_comp_apply hρ ⟨φ, hker⟩ x
  let g : ResidueField S → level p L n ⧸ J := fun b =>
    if h : b ∈ residue S '' L then π ⟨h.choose, mem_level_of_mem h.choose_spec.1⟩ else 0
  have hg : ∀ x (hx : x ∈ L), g (residue S x) = π ⟨x, mem_level_of_mem hx⟩ := fun x hx => by
    have h : residue S x ∈ residue S '' L := ⟨x, hx, rfl⟩
    simp only [g, dif_pos h, hL h.choose_spec.1 hx h.choose_spec.2]
  obtain ⟨σ, h1, h2⟩ := exists_ringHom_pow hB n _ f g (by
    rintro _ ⟨x, hx, rfl⟩
    rw [hg x hx, ← hf]
    rfl)
  have key : ∀ x (hx : x ∈ level p L n), σ (residue S x) = π ⟨x, hx⟩ := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with (⟨x, rfl⟩ | hx) | hx
      · obtain ⟨t, ht, h⟩ := hs n x
        have h3 : residue S x = ρ ⟨t, ht⟩ := Ideal.Quotient.eq.2 h
        rw [map_pow, h1, h3, hf, ← map_pow]
        exact (hπ _ _ (pow_sub_pow_mem h0 h n)).symm
      · rw [h2 _ ⟨x, hx, rfl⟩, hg x hx]
      · rw [(residue_eq_zero_iff _).2 (Ideal.pow_le_self n.succ_ne_zero hx), map_zero]
        exact ((hπ _ 0 (by simpa using hx)).trans (map_zero π)).symm
    | zero => rw [map_zero, map_zero]; exact (map_zero π).symm
    | one => rw [map_one, map_one]; exact (map_one π).symm
    | add x y hx hy ihx ihy => rw [map_add, map_add, ihx, ihy, ← map_add]; rfl
    | neg x hx ihx => rw [map_neg, map_neg, ihx, ← map_neg]; rfl
    | mul x y hx hy ihx ihy => rw [map_mul, map_mul, ihx, ihy, ← map_mul]; rfl
  have h3 := key a ha
  rw [(residue_eq_zero_iff _).2 ha', map_zero, eq_comm] at h3
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (Ideal.Quotient.eq_zero_iff_mem.1 h3)
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 hy
  refine ⟨t, t.2, ?_⟩
  have h4 : (p : S) * t + z = a := by simpa using congrArg Subtype.val hyz
  rw [← h4, add_sub_cancel_left]
  exact hz

omit [IsLocalRing S] in
theorem exists_mem_pow_of_mul_mem [IsDomain S] [IsNoetherianRing S] (I : Ideal S) {r : S}
    (hr : r ≠ 0) : ∃ c : ℕ, ∀ (n : ℕ) (x : S), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (M := S) (Ideal.span {r})
  refine ⟨c, fun n x hx => ?_⟩
  have h := hc (n + c) (Nat.le_add_left _ _)
  have hm : r * x ∈ I ^ (n + c) • (⊤ : Submodule S S) ⊓ Ideal.span {r} :=
    ⟨by rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hx,
      Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self r)⟩
  rw [h, Nat.add_sub_cancel] at hm
  have hm' : r * x ∈ I ^ n * Ideal.span {r} := Submodule.smul_mono le_rfl inf_le_right hm
  obtain ⟨z, hz, hzx⟩ := Ideal.mem_mul_span_singleton.1 hm'
  rw [mul_comm] at hzx
  rwa [← mul_left_cancel₀ hr hzx]

theorem dvd_of_forall_sub_mul_mem [IsNoetherianRing S] {r a : S}
    (h : ∀ n, ∃ t, a - r * t ∈ maximalIdeal S ^ n) : r ∣ a := by
  have h1 := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := S ⧸ Ideal.span {r}) (maximalIdeal S)
    (maximalIdeal.isMaximal S).ne_top
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← Submodule.mem_bot S, ← h1,
    Submodule.mem_iInf]
  intro n
  obtain ⟨t, ht⟩ := h n
  have : Ideal.Quotient.mk (Ideal.span {r}) a = (a - r * t) • (1 : S ⧸ Ideal.span {r}) := by
    rw [← Algebra.algebraMap_eq_smul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
    simp [Ideal.mem_span_singleton]
  rw [this]
  exact Submodule.smul_mem_smul ht trivial

theorem exists_coeffSubring [IsDomain S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (hp : p.Prime) (hp0 : (p : S) ≠ 0) (h0 : (p : S) ∈ maximalIdeal S) {B : Set (ResidueField S)}
    (hB : Subring.closure (Set.range (fun x : ResidueField S => x ^ p) ∪ B) = ⊤)
    (hB' : ∀ (Q : Type) [CommRing Q] (f : ResidueField S →+* Q) (g : ResidueField S → Q),
      (∀ b ∈ B, g b ^ p = f b) →
      ∃ σ : ResidueField S →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b) :
    ∃ Λ : Subring S, (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) ∧
      (∀ a : Λ, (a : S) ∈ maximalIdeal S → (p : Λ) ∣ a) ∧
      (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) := by
  choose l hl using residue_surjective (R := S)
  have hL : residue S '' (l '' B) = B := by simp [Set.image_image, hl]
  have hinj : Set.InjOn (residue S) (l '' B) := by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ h
    rw [hl, hl] at h
    rw [h]
  rw [← hL] at hB hB'
  have hs := exists_level_sub_mem hp h0 hB
  refine ⟨⨅ n, level p (l '' B) n, exists_iInf_sub_mem h0 hs, fun a ha => ?_, fun s h => ?_⟩
  · choose t ht ht' using fun n =>
      exists_sub_mul_mem hp h0 hinj hB' hs n (Subring.mem_iInf.1 a.2 n) ha
    obtain ⟨s, hs'⟩ := dvd_of_forall_sub_mul_mem fun n =>
      ⟨t n, Ideal.pow_le_pow_right n.le_succ (ht' n)⟩
    obtain ⟨c, hc⟩ := exists_mem_pow_of_mul_mem (maximalIdeal S) hp0
    refine ⟨⟨s, Subring.mem_iInf.2 fun n => ?_⟩, Subtype.ext (by simpa using hs')⟩
    refine mem_level_of_sub_mem (level_antitone (Nat.le_add_right n c) (ht (n + c))) (hc _ _ ?_)
    rw [mul_sub, ← hs', add_right_comm]
    exact ht' _
  · refine Subring.mem_iInf.2 fun n => ?_
    obtain ⟨a, ha, h'⟩ := h (n + 1)
    exact mem_level_of_sub_mem (Subring.mem_iInf.1 ha n) h'

end GlobalTheory.CoeffSubring
