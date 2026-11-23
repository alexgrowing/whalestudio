import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchangeStatement

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

namespace ColRecProof

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem patChar_add_single {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ι → K) (ψ₀ : AddChar K ℂ)
    (p q : ι) (t : K) (u : GL ι K) :
    patChar (fun i j => E i j + if i = p ∧ j = q then t else 0) ψ₀ u =
      patChar E ψ₀ u * ψ₀ (t * (u : Matrix ι ι K) p q) := by
  unfold patChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem mem_patSet_remove {ι : Type} [Fintype ι] [DecidableEq ι] {Φ Φ' : ι → ι → Prop} {p q : ι}
    (hne : p ≠ q) (hiff : ∀ i j, Φ' i j ↔ Φ i j ∧ ¬ (i = p ∧ j = q)) (hpq : Φ p q) (u : GL ι K) :
    u ∈ patSet K Φ' ↔ u ∈ patSet K Φ ∧ (u : Matrix ι ι K) p q = 0 := by
  constructor
  · intro h
    refine ⟨fun i j => ⟨(h i j).1, fun hij hn => (h i j).2 hij fun h' => hn ((hiff i j).1 h').1⟩, ?_⟩
    exact (h p q).2 hne fun h' => ((hiff p q).1 h').2 ⟨rfl, rfl⟩
  · rintro ⟨h, h0⟩ i j
    refine ⟨(h i j).1, fun hij hn => ?_⟩
    by_cases hΦ : Φ i j
    · have : i = p ∧ j = q := by
        by_contra hc
        exact hn ((hiff i j).2 ⟨hΦ, hc⟩)
      rw [this.1, this.2]; exact h0
    · exact (h i j).2 hij hΦ

theorem ncard_patSet_remove {ι : Type} [Fintype ι] [DecidableEq ι] {Φ Φ' : ι → ι → Prop} {p q : ι}
    (hΦ : IsPat Φ) (hΦ' : IsPat Φ') (hiff : ∀ i j, Φ' i j ↔ Φ i j ∧ ¬ (i = p ∧ j = q)) (hpq : Φ p q) :
    (patSet K Φ).ncard = Fintype.card K * (patSet K Φ').ncard := by
  have h1 := (GlobalTheory.T.pattern_group_statement K ι Φ hΦ).2.1
  have h2 := (GlobalTheory.T.pattern_group_statement K ι Φ' hΦ').2.1
  have hset : {x : ι × ι | Φ x.1 x.2} = insert (p, q) {x : ι × ι | Φ' x.1 x.2} := by
    ext ⟨i, j⟩
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Prod.mk.injEq, hiff]
    constructor
    · intro h
      by_cases hc : i = p ∧ j = q
      · exact Or.inl hc
      · exact Or.inr ⟨h, hc⟩
    · rintro (⟨rfl, rfl⟩ | h)
      · exact hpq
      · exact h.1
  have hn : Nat.card {x : ι × ι // Φ x.1 x.2} = Nat.card {x : ι × ι // Φ' x.1 x.2} + 1 := by
    have h3 := Set.ncard_insert_of_notMem (s := {x : ι × ι | Φ' x.1 x.2}) (a := (p, q))
      (by simp [hiff]) (Set.toFinite _)
    rw [← hset] at h3
    have e1 := Nat.card_coe_set_eq {x : ι × ι | Φ x.1 x.2}
    have e2 := Nat.card_coe_set_eq {x : ι × ι | Φ' x.1 x.2}
    change Nat.card {x : ι × ι | Φ x.1 x.2} = Nat.card {x : ι × ι | Φ' x.1 x.2} + 1
    rw [e1, e2, h3]
  rw [h1, h2, hn, pow_succ, mul_comm]

theorem wh_fourier {ι : Type} [Fintype ι] [DecidableEq ι] {Φ Φ' : ι → ι → Prop} {p q : ι}
    (hΦ : IsPat Φ) (hΦ' : IsPat Φ') (hiff : ∀ i j, Φ' i j ↔ Φ i j ∧ ¬ (i = p ∧ j = q)) (hpq : Φ p q)
    (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (χ : GL ι K → ℂ) (hψ : ψ₀ ≠ 1) :
    wh Φ' E ψ₀ χ = ∑ t : K, wh Φ (fun i j => E i j + if i = p ∧ j = q then t else 0) ψ₀ χ := by
  classical
  have hne : p ≠ q := by
    rintro rfl
    exact hΦ.1 p hpq
  have hprim : ψ₀.IsPrimitive := AddChar.IsPrimitive.of_ne_one hψ
  have hq : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc := ncard_patSet_remove (K := K) hΦ hΦ' hiff hpq
  have hS : ((patSet K Φ').ncard : ℂ) = (Fintype.card K : ℂ)⁻¹ * ((patSet K Φ).ncard : ℂ) := by
    rw [hc]; push_cast; field_simp
  have key : ∀ u : GL ι K, ∑ t : K, (if u ∈ patSet K Φ then
      (patChar E ψ₀ u * ψ₀ (t * (u : Matrix ι ι K) p q))⁻¹ * χ u else 0) =
      (Fintype.card K : ℂ) * (if u ∈ patSet K Φ' then (patChar E ψ₀ u)⁻¹ * χ u else 0) := by
    intro u
    by_cases hu : u ∈ patSet K Φ
    · have hs : ∑ t : K, (ψ₀ (t * (u : Matrix ι ι K) p q))⁻¹ =
          if (u : Matrix ι ι K) p q = 0 then (Fintype.card K : ℂ) else 0 := by
        have := AddChar.sum_mulShift (-(u : Matrix ι ι K) p q) hprim
        simp only [neg_eq_zero, Nat.cast_ite, Nat.cast_zero] at this
        rw [← this]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← AddChar.map_neg_eq_inv]
        congr 1
        ring
      simp only [if_pos hu, mul_inv]
      have : ∀ t : K, (patChar E ψ₀ u)⁻¹ * (ψ₀ (t * (u : Matrix ι ι K) p q))⁻¹ * χ u =
          ((patChar E ψ₀ u)⁻¹ * χ u) * (ψ₀ (t * (u : Matrix ι ι K) p q))⁻¹ := fun t => by ring
      simp only [this]
      rw [← Finset.mul_sum, hs]
      by_cases h0 : (u : Matrix ι ι K) p q = 0
      · rw [if_pos h0, if_pos ((mem_patSet_remove hne hiff hpq u).2 ⟨hu, h0⟩)]; ring
      · rw [if_neg h0, if_neg fun h => h0 ((mem_patSet_remove hne hiff hpq u).1 h).2]; ring
    · have hu' : u ∉ patSet K Φ' := fun h => hu ((mem_patSet_remove hne hiff hpq u).1 h).1
      simp [hu, hu']
  unfold wh
  simp only [patChar_add_single]
  rw [← Finset.mul_sum, Finset.sum_comm, hS]
  simp only [key]
  rw [← Finset.mul_sum, mul_inv, inv_inv]
  field_simp

theorem wh_conj {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E E' : ι → ι → K)
    (ψ₀ : AddChar K ℂ) (χ : GL ι K → ℂ) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (x : GL ι K)
    (hmem : ∀ u, x * u * x⁻¹ ∈ patSet K Φ ↔ u ∈ patSet K Φ)
    (hE : ∀ u ∈ patSet K Φ, patChar E' ψ₀ (x * u * x⁻¹) = patChar E ψ₀ u) :
    wh Φ E ψ₀ χ = wh Φ E' ψ₀ χ := by
  classical
  unfold wh
  congr 1
  rw [← Equiv.sum_comp (MulAut.conj x).toEquiv
    (fun u => if u ∈ patSet K Φ then (patChar E' ψ₀ u)⁻¹ * χ u else 0)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e : (MulAut.conj x).toEquiv u = x * u * x⁻¹ := rfl
  rw [e]
  by_cases hu : u ∈ patSet K Φ
  · rw [if_pos hu, if_pos ((hmem u).2 hu), hE u hu, hχ]
  · rw [if_neg hu, if_neg fun h => hu ((hmem u).1 h)]

theorem sum_sum_ite {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι) (c : K) :
    ∑ i : ι, ∑ j : ι, (if i = p ∧ j = q then c else 0) = c := by
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; simp [hi]
  · simp

def Dp (N k a : ℕ) (i j : Fin N) : Prop := i < j ∧ ¬ (a ≤ (i : ℕ) ∧ (j : ℕ) = k)

theorem isPat_Dp (N k a : ℕ) : IsPat (Dp N k a) := by
  refine ⟨fun i h => lt_irrefl _ h.1, fun i j l hij hjl => ⟨hij.1.trans hjl.1, fun h => ?_⟩⟩
  have h1 : (i : ℕ) < j := hij.1
  exact hjl.2 ⟨by omega, h.2⟩

theorem Dp_step_iff {N k a : ℕ} (ha : a < k) (hk : k < N) (i j : Fin N) :
    Dp N k a i j ↔ Dp N k (a + 1) i j ∧ ¬ (i = ⟨a, ha.trans hk⟩ ∧ j = ⟨k, hk⟩) := by
  simp only [Dp, Fin.ext_iff, Fin.lt_def]
  omega

theorem wh_Dp_step {N k a : ℕ} (ha : a < k) (hk : k < N) (ψ₀ : AddChar K ℂ) (χ : GL (Fin N) K → ℂ)
    (hψ : ψ₀ ≠ 1) :
    wh (Dp N k a) (cutE K N k) ψ₀ χ = wh (Dp N k (a + 1)) (cutE K N k) ψ₀ χ +
      ∑ t ∈ Finset.univ.erase (0 : K), wh (Dp N k (a + 1))
        (fun i j => cutE K N k i j + if i = ⟨a, ha.trans hk⟩ ∧ j = ⟨k, hk⟩ then t else 0) ψ₀ χ := by
  have hmem : Dp N k (a + 1) ⟨a, ha.trans hk⟩ ⟨k, hk⟩ := by
    simp only [Dp, Fin.lt_def]
    omega
  rw [wh_fourier (isPat_Dp N k (a + 1)) (isPat_Dp N k a) (Dp_step_iff ha hk) hmem (cutE K N k) ψ₀ χ hψ,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : K))]
  congr 1
  simp

def Ea (N k a : ℕ) (t : K) (i j : Fin N) : K :=
  if (i : ℕ) = a ∧ (j : ℕ) = k then t
  else if (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k ∧ (i : ℕ) ≠ a then 1 else 0

theorem one_add_single_mul {N : ℕ} (b k : Fin N) (s : K) (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    ((1 + Matrix.single b k s) * M) i j = M i j + if i = b then s * M k j else 0 := by
  rw [add_mul, one_mul, Matrix.add_apply]
  congr 1
  by_cases h : i = b
  · subst h
    simp [Matrix.single_mul_apply_same]
  · simp [h, Matrix.single_mul_apply_of_ne]

theorem mul_one_add_single {N : ℕ} (b k : Fin N) (s : K) (M : Matrix (Fin N) (Fin N) K) (i j : Fin N) :
    (M * (1 + Matrix.single b k s)) i j = M i j + if j = k then M i b * s else 0 := by
  rw [mul_add, mul_one, Matrix.add_apply]
  congr 1
  by_cases h : j = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · simp [h, Matrix.mul_single_apply_of_ne]

def xs {N : ℕ} (b k : Fin N) (hbk : b ≠ k) (s : K) : GL (Fin N) K where
  val := 1 + Matrix.single b k s
  inv := 1 + Matrix.single b k (-s)
  val_inv := by
    ext i j
    rw [one_add_single_mul]
    by_cases h1 : i = b
    · subst h1
      by_cases h2 : j = k
      · subst h2
        simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hbk, hbk.symm]
      · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hbk.symm, h2, Ne.symm h2]
    · simp [Matrix.add_apply, Matrix.single_apply, h1, Ne.symm h1]
  inv_val := by
    ext i j
    rw [one_add_single_mul]
    by_cases h1 : i = b
    · subst h1
      by_cases h2 : j = k
      · subst h2
        simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hbk, hbk.symm]
      · simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, hbk.symm, h2, Ne.symm h2]
    · simp [Matrix.add_apply, Matrix.single_apply, h1, Ne.symm h1]

theorem xs_neg {N : ℕ} (b k : Fin N) (hbk : b ≠ k) (s : K) : xs b k hbk (-s) = (xs b k hbk s)⁻¹ := by
  apply Units.ext
  change 1 + Matrix.single b k (-s) = 1 + Matrix.single b k (-s)
  rfl

theorem xs_conj_apply {N : ℕ} (b k : Fin N) (hbk : b ≠ k) (s : K) (u : GL (Fin N) K) (i j : Fin N) :
    ((xs b k hbk s * u * (xs b k hbk s)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j =
      ((u : Matrix (Fin N) (Fin N) K) i j + if i = b then s * (u : Matrix (Fin N) (Fin N) K) k j else 0) +
        if j = k then ((u : Matrix (Fin N) (Fin N) K) i b +
          if i = b then s * (u : Matrix (Fin N) (Fin N) K) k b else 0) * (-s) else 0 := by
  have h : ((xs b k hbk s * u * (xs b k hbk s)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      (1 + Matrix.single b k s) * (u : Matrix (Fin N) (Fin N) K) * (1 + Matrix.single b k (-s)) := rfl
  rw [h, mul_one_add_single, one_add_single_mul, one_add_single_mul]

theorem xs_conj_mem {N k a : ℕ} (hb : a + 1 < k) (hk : k < N) (hbk : (⟨a + 1, hb.trans hk⟩ : Fin N) ≠ ⟨k, hk⟩)
    (s : K) (u : GL (Fin N) K) (hu : u ∈ patSet K (Dp N k (a + 1))) :
    xs ⟨a + 1, hb.trans hk⟩ ⟨k, hk⟩ hbk s * u * (xs ⟨a + 1, hb.trans hk⟩ ⟨k, hk⟩ hbk s)⁻¹ ∈
      patSet K (Dp N k (a + 1)) := by
  have hlow : ∀ i j : Fin N, (j : ℕ) < i → (u : Matrix (Fin N) (Fin N) K) i j = 0 := fun i j h =>
    (hu i j).2 (by intro e; subst e; omega) (fun h' => by
      have : (i : ℕ) < j := h'.1
      omega)
  have hdiag : ∀ i : Fin N, (u : Matrix (Fin N) (Fin N) K) i i = 1 := fun i => (hu i i).1 rfl
  have hcol : ∀ i : Fin N, a + 1 ≤ (i : ℕ) → (i : ℕ) < k →
      (u : Matrix (Fin N) (Fin N) K) i ⟨k, hk⟩ = 0 := fun i h1 h2 =>
    (hu i ⟨k, hk⟩).2 (by intro e; rw [e] at h2; simp at h2) (fun h' => h'.2 ⟨h1, rfl⟩)
  have hkb : (u : Matrix (Fin N) (Fin N) K) ⟨k, hk⟩ ⟨a + 1, hb.trans hk⟩ = 0 := hlow _ _ hb
  intro i j
  rw [xs_conj_apply]
  constructor
  · rintro rfl
    by_cases h1 : i = ⟨a + 1, hb.trans hk⟩
    · subst h1
      simp [hdiag, hkb, hbk]
    · by_cases h2 : i = ⟨k, hk⟩
      · subst h2
        simp [hdiag, hkb, h1]
      · simp [hdiag, h1, h2]
  · intro hij hD
    have hcase : (j : ℕ) < i ∨ (a + 1 ≤ (i : ℕ) ∧ (i : ℕ) < k ∧ (j : ℕ) = k) := by
      have hne : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
      simp only [Dp, Fin.lt_def] at hD
      omega
    rcases hcase with h | ⟨h1, h2, h3⟩
    · rw [hlow i j h]
      by_cases hi : i = ⟨a + 1, hb.trans hk⟩
      · subst hi
        have hjk : j ≠ ⟨k, hk⟩ := by
          intro e; rw [e] at h; simp at h; omega
        have hz : (u : Matrix (Fin N) (Fin N) K) ⟨k, hk⟩ j = 0 := hlow _ _ (by simp at h ⊢; omega)
        simp [hz, hjk]
      · by_cases hj : j = ⟨k, hk⟩
        · subst hj
          have hz : (u : Matrix (Fin N) (Fin N) K) i ⟨a + 1, hb.trans hk⟩ = 0 :=
            hlow _ _ (by simp at h ⊢; omega)
          simp [hz, hi]
        · simp [hi, hj]
    · have hj : j = ⟨k, hk⟩ := Fin.ext h3
      subst hj
      rw [hcol i h1 h2]
      by_cases hi : i = ⟨a + 1, hb.trans hk⟩
      · subst hi
        simp [hdiag, hkb]
      · have hz : (u : Matrix (Fin N) (Fin N) K) i ⟨a + 1, hb.trans hk⟩ = 0 := hlow _ _ (by
          have : (i : ℕ) ≠ a + 1 := fun e => hi (Fin.ext e)
          simp only
          omega)
        simp [hz, hi]

theorem patChar_xs_conj {N k a : ℕ} (hb : a + 1 < k) (p b q : Fin N) (hpv : (p : ℕ) = a)
    (hbv : (b : ℕ) = a + 1) (hqv : (q : ℕ) = k) (hbk : b ≠ q) {t : K} (ht : t ≠ 0) (ψ₀ : AddChar K ℂ)
    (u : GL (Fin N) K) (hlow : ∀ i j : Fin N, (j : ℕ) < i → (u : Matrix (Fin N) (Fin N) K) i j = 0) :
    patChar (Ea N k a t) ψ₀ (xs b q hbk (-t⁻¹) * u * (xs b q hbk (-t⁻¹))⁻¹) =
    patChar (fun i j => cutE K N k i j + if i = p ∧ j = q then t else 0) ψ₀ u := by
  have hpb : p ≠ b := fun e => by rw [e] at hpv; omega
  have hpt : ∀ i j : Fin N, Ea N k a t i j *
      ((xs b q hbk (-t⁻¹) * u * (xs b q hbk (-t⁻¹))⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j =
      (cutE K N k i j + if i = p ∧ j = q then t else 0) * (u : Matrix (Fin N) (Fin N) K) i j +
      ((if i = p ∧ j = q then (u : Matrix (Fin N) (Fin N) K) p b else 0) -
        (if i = p ∧ j = b then (u : Matrix (Fin N) (Fin N) K) p b else 0)) := by
    intro i j
    rw [xs_conj_apply]
    by_cases h1 : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := h1
      have hE : Ea N k a t i j = t := by
        simp only [Ea]
        rw [if_pos ⟨hpv, hqv⟩]
      have hF : cutE K N k i j = 0 := by
        simp only [cutE]
        rw [if_neg (by omega)]
      rw [hE, hF]
      simp [hpb, hbk.symm]
      field_simp
    · by_cases h2 : i = p ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h2
        have hE : Ea N k a t i j = 0 := by
          simp only [Ea]
          rw [if_neg (by omega), if_neg (by omega)]
        have hF : cutE K N k i j = 1 := by
          simp only [cutE]
          rw [if_pos (by omega)]
        rw [hE, hF]
        simp [hpb, hbk, hbk.symm]
      · rw [if_neg h1, if_neg h1, if_neg h2]
        have h1' : ¬ ((i : ℕ) = a ∧ (j : ℕ) = k) := fun h =>
          h1 ⟨Fin.ext (h.1.trans hpv.symm), Fin.ext (h.2.trans hqv.symm)⟩
        have h2' : ¬ ((i : ℕ) = a ∧ (j : ℕ) = a + 1) := fun h =>
          h2 ⟨Fin.ext (h.1.trans hpv.symm), Fin.ext (h.2.trans hbv.symm)⟩
        by_cases h3 : (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k ∧ (i : ℕ) ≠ a
        · have hE : Ea N k a t i j = 1 := by
            simp only [Ea]
            rw [if_neg h1', if_pos h3]
          have hF : cutE K N k i j = 1 := by
            simp only [cutE]
            rw [if_pos ⟨h3.1, h3.2.1⟩]
          have hjq : j ≠ q := fun e => h3.2.1 (by rw [e, hqv])
          rw [hE, hF, if_neg hjq]
          by_cases hi : i = b
          · have hz : (u : Matrix (Fin N) (Fin N) K) q j = 0 := hlow _ _ (by
              have h4 := h3.1
              have h5 := h3.2.1
              rw [hi, hbv] at h4
              rw [hqv]
              omega)
            simp [hi, hz]
          · simp [hi]
        · have hE : Ea N k a t i j = 0 := by
            simp only [Ea]
            rw [if_neg h1', if_neg h3]
          have hF : cutE K N k i j = 0 := by
            simp only [cutE]
            rw [if_neg (by omega)]
          rw [hE, hF]
          simp
  unfold patChar
  congr 1
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_sum_ite]
  ring

theorem Ea_ne {N k a : ℕ} {t : K} {i j : Fin N} (h : Ea N k a t i j ≠ 0) :
    ((i : ℕ) = a ∧ (j : ℕ) = k) ∨ ((j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k ∧ (i : ℕ) ≠ a) := by
  unfold Ea at h
  split_ifs at h with h1 h2
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd rfl h

theorem wh_exchange {N k a : ℕ} (ha : a < k) (hk : k < N) {t : K} (ht : t ≠ 0) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin N) K → ℂ) (hψ : ψ₀ ≠ 1) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) :
    wh (Dp N k (a + 1)) (Ea N k a t) ψ₀ χ = wh (rowPat N k a) (Ea N k a t) ψ₀ χ := by
  have e1 : (fun i j : Fin N => i < j ∧ ¬ ((a < (i : ℕ) ∧ (i : ℕ) < k) ∧ j = ⟨k, hk⟩)) = Dp N k (a + 1) := by
    funext i j
    apply propext
    simp only [Dp, Fin.ext_iff, Fin.lt_def]
    omega
  have e2 : (fun i j : Fin N => i < j ∧ ¬ (i = ⟨a, ha.trans hk⟩ ∧ (a < (j : ℕ) ∧ (j : ℕ) < k))) =
      rowPat N k a := by
    funext i j
    apply propext
    simp only [rowPat, Fin.ext_iff, Fin.lt_def]
    omega
  rw [← e1, ← e2]
  refine GlobalTheory.T.root_exchange' K (Fin N) (fun i j => i < j) (Ea N k a t) ψ₀ (fun w => a < (w : ℕ) ∧ (w : ℕ) < k)
    ⟨a, ha.trans hk⟩ ⟨k, hk⟩ χ ⟨fun i => lt_irrefl i, fun i j l => lt_trans⟩ hψ hχ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro w ⟨h1, h2⟩
    exact ⟨h1, h2⟩
  · have : Ea N k a t ⟨a, ha.trans hk⟩ ⟨k, hk⟩ = t := by
      unfold Ea
      exact if_pos ⟨rfl, rfl⟩
    rw [this]
    exact ht
  · intro i j h
    rcases Ea_ne h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · change (i : ℕ) < j
      omega
    · change (i : ℕ) < j
      omega
  · rintro w ⟨h1, h2⟩
    constructor
    · by_contra h
      rcases Ea_ne h with ⟨_, h3⟩ | ⟨_, _, h3⟩
      · omega
      · exact h3 rfl
    · by_contra h
      rcases Ea_ne h with ⟨h3, _⟩ | ⟨_, h3, _⟩
      · omega
      · exact h3 rfl
  · rintro w z ⟨h1, h2⟩ hwz hzq
    have h3 : (w : ℕ) < z := hwz
    have h4 : (z : ℕ) < k := hzq
    exact ⟨by omega, h4⟩
  · rintro w z ⟨h1, h2⟩ hpz hzw
    have h3 : a < (z : ℕ) := hpz
    have h4 : (z : ℕ) < w := hzw
    exact ⟨h3, by omega⟩
  · intro i j l hij hjl h
    have h1 : (i : ℕ) < j := hij
    have h2 : (j : ℕ) < l := hjl
    rcases Ea_ne h with ⟨h3, h4⟩ | ⟨h3, _⟩
    · exact ⟨Fin.ext h3, Fin.ext h4, by omega, by omega⟩
    · omega

def tor {N : ℕ} (a : ℕ) (t : Kˣ) (i : Fin N) : Kˣ := if (i : ℕ) ≤ a then t else 1

theorem Ea_torus {N k a : ℕ} (ha : a < k) (t : Kˣ) :
    (fun i j : Fin N => ((tor a t i : Kˣ) : K) * rowE K N k a i j * (((tor a t j)⁻¹ : Kˣ) : K)) =
      Ea N k a (t : K) := by
  funext i j
  by_cases h1 : (i : ℕ) = a ∧ (j : ℕ) = k
  · have hE : rowE K N k a i j = 1 := by
      simp only [rowE]
      rw [if_pos (Or.inl h1)]
    have hEa : Ea N k a (t : K) i j = t := by
      simp only [Ea]
      rw [if_pos h1]
    have hi : tor a t i = t := by
      simp only [tor]
      rw [if_pos (by omega)]
    have hj : tor a t j = 1 := by
      simp only [tor]
      rw [if_neg (by omega)]
    rw [hE, hEa, hi, hj]
    simp
  · by_cases h2 : (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k ∧ (i : ℕ) ≠ a
    · have hE : rowE K N k a i j = 1 := by
        simp only [rowE]
        rw [if_pos (Or.inr h2)]
      have hEa : Ea N k a (t : K) i j = 1 := by
        simp only [Ea]
        rw [if_neg h1, if_pos h2]
      have hij : tor a t i = tor a t j := by
        simp only [tor]
        by_cases h3 : (i : ℕ) ≤ a
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]
      rw [hE, hEa, hij]
      simp
    · have hE : rowE K N k a i j = 0 := by
        simp only [rowE]
        rw [if_neg fun h => h.elim h1 h2]
      have hEa : Ea N k a (t : K) i j = 0 := by
        simp only [Ea]
        rw [if_neg h1, if_neg h2]
      rw [hE, hEa]
      simp

theorem wh_term {N k a : ℕ} (ha : a < k) (hk : k < N) {t : K} (ht : t ≠ 0) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin N) K → ℂ) (hψ : ψ₀ ≠ 1) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) :
    wh (Dp N k (a + 1))
        (fun i j => cutE K N k i j + if i = ⟨a, ha.trans hk⟩ ∧ j = ⟨k, hk⟩ then t else 0) ψ₀ χ =
      wh (rowPat N k a) (rowE K N k a) ψ₀ χ := by
  have h1 : wh (Dp N k (a + 1))
        (fun i j => cutE K N k i j + if i = ⟨a, ha.trans hk⟩ ∧ j = ⟨k, hk⟩ then t else 0) ψ₀ χ =
      wh (Dp N k (a + 1)) (Ea N k a t) ψ₀ χ := by
    rcases Nat.lt_or_ge (a + 1) k with hb | hb
    · have hbk : (⟨a + 1, hb.trans hk⟩ : Fin N) ≠ ⟨k, hk⟩ := by
        intro e
        have := congrArg Fin.val e
        simp only at this
        omega
      refine wh_conj _ _ _ ψ₀ χ hχ (xs ⟨a + 1, hb.trans hk⟩ ⟨k, hk⟩ hbk (-t⁻¹)) ?_ ?_
      · intro u
        constructor
        · intro h
          have h2 := xs_conj_mem hb hk hbk (-(-t⁻¹)) _ h
          rw [xs_neg _ _ hbk (-t⁻¹)] at h2
          have e : ∀ x : GL (Fin N) K, x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := fun x => by group
          rwa [e] at h2
        · exact xs_conj_mem hb hk hbk _ u
      · intro u hu
        refine patChar_xs_conj hb _ _ _ rfl rfl rfl hbk ht ψ₀ u fun i j h =>
          (hu i j).2 (by intro e; subst e; omega) (fun h' => ?_)
        have : (i : ℕ) < j := h'.1
        omega
    · have hka : k = a + 1 := by omega
      subst hka
      congr 1
      funext i j
      have e : (i = ⟨a, ha.trans hk⟩ ∧ j = ⟨a + 1, hk⟩) ↔ ((i : ℕ) = a ∧ (j : ℕ) = a + 1) := by
        simp [Fin.ext_iff]
      by_cases h1 : (i : ℕ) = a ∧ (j : ℕ) = a + 1
      · rw [if_pos (e.2 h1)]
        simp only [cutE, Ea]
        rw [if_neg (by omega), if_pos h1, zero_add]
      · rw [if_neg (fun h => h1 (e.1 h)), add_zero]
        simp only [cutE, Ea]
        rw [if_neg h1]
        by_cases h2 : (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ a + 1
        · rw [if_pos h2, if_pos ⟨h2.1, h2.2, by omega⟩]
        · rw [if_neg h2, if_neg (by omega)]
  have h2 := Ea_torus (K := K) (N := N) ha (Units.mk0 t ht)
  rw [Units.val_mk0] at h2
  rw [h1, wh_exchange ha hk ht ψ₀ χ hψ hχ, ← h2]
  exact ((GlobalTheory.T.whittaker_symmetry K (Fin N) (Fin N) (rowPat N k a) (rowE K N k a) ψ₀ χ).2 hχ).2
    (tor a (Units.mk0 t ht))

end ColRecProof

open ColRecProof in

theorem colRec : ReciprocityTheory.Ty.Fin.St.ColRec := by
  intro K _ _ _ N k ψ₀ χ hψ hχ hk
  have hsum : ∀ m, m ≤ k → wh (Dp N k 0) (cutE K N k) ψ₀ χ = wh (Dp N k m) (cutE K N k) ψ₀ χ +
      ((Fintype.card K : ℂ) - 1) * ∑ a ∈ Finset.range m, wh (rowPat N k a) (rowE K N k a) ψ₀ χ := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hmk : m < k := by omega
      have hcard : ∑ t ∈ Finset.univ.erase (0 : K), wh (Dp N k (m + 1))
          (fun i j => cutE K N k i j + if i = ⟨m, hmk.trans hk⟩ ∧ j = ⟨k, hk⟩ then t else 0) ψ₀ χ =
          ((Fintype.card K : ℂ) - 1) * wh (rowPat N k m) (rowE K N k m) ψ₀ χ := by
        rw [Finset.sum_congr rfl fun t ht => wh_term hmk hk (Finset.ne_of_mem_erase ht) ψ₀ χ hψ hχ,
          Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          nsmul_eq_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
      rw [ih (by omega), wh_Dp_step hmk hk ψ₀ χ hψ, hcard, Finset.sum_range_succ]
      ring
  have e0 : Dp N k 0 = colPat N k := by
    funext i j
    apply propext
    simp only [Dp, colPat]
    omega
  have eK : Dp N k k = fun i j : Fin N => i < j := by
    funext i j
    apply propext
    simp only [Dp, Fin.lt_def]
    omega
  have h := hsum k le_rfl
  rwa [e0, eK] at h

end GlobalTheory.CompanionTheory.TyFin
