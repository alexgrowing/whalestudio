import Formalism.SubspaceCounting.StatementC
import Formalism.SubspaceCounting.SubspaceCountingProofs.LengthLayers
import Formalism.SubspaceCounting.SubspaceCountingProofs.WalkSharp

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace ManyOrbitsP

theorem add_pow_ge (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (k : ℕ) :
    p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k ≤ (p + q) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpq : 0 ≤ p + q := add_nonneg hp hq
    have h1 := mul_le_mul_of_nonneg_left ih hpq
    have h2 : 0 ≤ ((k : ℝ) + 1) * q ^ 2 * p ^ k := by positivity
    have e : (p + q) * (p ^ (k + 1) + ((k : ℝ) + 1) * q * p ^ k) -
        (p ^ (k + 1 + 1) + (((k : ℝ) + 1) + 1) * q * p ^ (k + 1)) = ((k : ℝ) + 1) * q ^ 2 * p ^ k := by
      ring
    have e2 : (p + q) * (p + q) ^ (k + 1) = (p + q) ^ (k + 1 + 1) := by ring
    push_cast
    linarith

theorem fact_esymm_le (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (n : ℕ) :
    (n.factorial : ℝ) * s.esymm n ≤ s.sum ^ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
      simp
  | cons a t ih =>
    have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ x ∈ t, 0 ≤ x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have hS : 0 ≤ t.sum := Multiset.sum_nonneg ht
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n =>
      have e : (a ::ₘ t).esymm (n + 1) = t.esymm (n + 1) + a * t.esymm n := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      have h1 := ih ht (n + 1)
      have h2 := ih ht n
      have h3 := add_pow_ge t.sum a hS ha n
      have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * a)
      rw [e, Multiset.sum_cons, add_comm a t.sum]
      rw [Nat.factorial_succ] at h1 ⊢
      push_cast at h1 ⊢
      have e5 : ((n : ℝ) + 1) * (n.factorial : ℝ) * (t.esymm (n + 1) + a * t.esymm n) =
          ((n : ℝ) + 1) * (n.factorial : ℝ) * t.esymm (n + 1) + ((n : ℝ) + 1) * a * ((n.factorial : ℝ) * t.esymm n) := by
        ring
      linarith [h1, h3, h4, e5]

theorem esymmR_le {V : ℕ} (κ : Fin V → ℝ) (hκ : ∀ v, 0 ≤ κ v) (m : ℝ) (hm : 0 ≤ m) (k : ℕ) :
    m ^ k * esymmR κ k ≤ (m * ∑ v, κ v) ^ k / k.factorial := by
  unfold esymmR
  have hnn : ∀ x ∈ Finset.univ.val.map κ, 0 ≤ x := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp hx
    exact hκ v
  have hE := fact_esymm_le (Finset.univ.val.map κ) hnn k
  rw [Finset.esymm_map_val] at hE
  have hsum : (Finset.univ.val.map κ).sum = ∑ v, κ v := rfl
  rw [hsum] at hE
  have hk : (0 : ℝ) < k.factorial := by positivity
  have hmk : 0 ≤ m ^ k := pow_nonneg hm k
  rw [le_div_iff₀ hk, mul_pow]
  have h2 := mul_le_mul_of_nonneg_left hE hmk
  calc m ^ k * (∑ B ∈ Finset.powersetCard k Finset.univ, ∏ v ∈ B, κ v) * (k.factorial : ℝ)
      = m ^ k * ((k.factorial : ℝ) * ∑ B ∈ Finset.powersetCard k Finset.univ, ∏ v ∈ B, κ v) := by ring
    _ ≤ m ^ k * (∑ v, κ v) ^ k := h2

section Mod

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

theorem allBut_mono {π : R} {M P : Submodule R X} {g g' E E' : ℕ} (h : AllButLE π M P g E)
    (hg : g ≤ g') (hE : E ≤ E') : AllButLE π M P g' E' := by
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C, hCM, hcard.trans hg, fun x hx => ?_⟩
  have := Submodule.smul_mem _ (π ^ (E' - E)) (hC x hx)
  rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hE] at this

theorem allBut_comap (π : R) (M P : Submodule R X) (g E : ℕ) (h : AllButLE π M P g E) :
    AllButLE π (⊤ : Submodule R M) (P.comap M.subtype) g E := by
  classical
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C.subtype (· ∈ M), fun _ _ => Submodule.mem_top, ?_, fun x _ => ?_⟩
  · exact (Finset.card_subtype _ _).le.trans ((Finset.card_filter_le _ _).trans hcard)
  · obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp (hC x x.2)
    have hspanle : Submodule.span R (↑C : Set X) ≤ M := Submodule.span_le.mpr hCM
    have hcM : c ∈ M := hspanle hc
    have hpM : p ∈ M := by
      have e : p = π ^ E • (x : X) - c := by rw [← hpc]; abel
      rw [e]; exact M.sub_mem (M.smul_mem _ x.2) hcM
    refine Submodule.mem_sup.mpr ⟨⟨p, hpM⟩, hp, ⟨c, hcM⟩, ?_, ?_⟩
    · have hmap : Submodule.map M.subtype (Submodule.span R (↑(C.subtype (· ∈ M)) : Set M)) =
          Submodule.span R (↑C : Set X) := by
        rw [Submodule.map_span]
        congr 1
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa using hz
        · intro hy
          exact ⟨⟨y, hCM hy⟩, by simpa using hy, rfl⟩
      rw [← hmap] at hc
      obtain ⟨y, hy, hyc⟩ := Submodule.mem_map.mp hc
      have hy' : y = ⟨c, hcM⟩ := Subtype.ext hyc
      rwa [← hy']
    · ext
      simp [hpc]

theorem comap_smul_self (I : Ideal R) (M : Submodule R X) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by
  have h := Submodule.map_smul'' I (⊤ : Submodule R M) M.subtype
  rw [Submodule.map_subtype_top] at h
  rw [← h, Submodule.comap_map_eq_of_injective M.injective_subtype]

end Mod

theorem geom_le (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) (n : ℕ) :
    ∑ i ∈ Finset.range n, s ^ i ≤ 2 - 2 * s ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hsn : 0 ≤ s ^ n := pow_nonneg hs0 n
    nlinarith [mul_le_mul_of_nonneg_left hs hsn]

theorem lengthPart {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V β₀ : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β ≤ β₀, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ 2 * d * (s ^ (β + 1) / (β + 1).factorial) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * (τ + 4 * S * s + V * S * (2 * s ^ (β₀ + 1) / (β₀ + 1).factorial)) := by
  classical
  set gβ : ℕ → ℕ := fun β => ⌊(2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial))⌋₊ with hgβ
  have hA : ∀ β ≤ β₀, AllButLE π (⊤ : Submodule R M) (N.comap M.subtype) (gβ β) (τ + β * S) := by
    intro β hβ
    obtain ⟨C, hCM, hCcard, hC⟩ := h1 β hβ
    exact allBut_comap π M N _ _ ⟨C, hCM, Nat.le_floor hCcard, hC⟩
  have hB : AllButLE π (⊤ : Submodule R M) (N.comap M.subtype) 0 (τ + V * S) :=
    allBut_comap π M N 0 (τ + V * S) (allBut_mono h2 le_rfl (by omega))
  have hL := lengthBoundOfLayers (O := R) (M := M) π hπ (N.comap M.subtype) τ S (V * S) β₀ gβ hA hB
  have hq : Submodule.comap M.subtype (N ⊓ (Ideal.span {π ^ τ}) • M) =
      N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule R M) := by
    rw [Submodule.comap_inf, comap_smul_self]
  rw [hd] at hL
  rw [hq]
  have hne : Module.length R (↥M ⧸ (N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule R M))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) hL
  refine ⟨_, (ENat.coe_toNat hne).symm, ?_⟩
  have hnat : (Module.length R (↥M ⧸ (N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule R M)))).toNat ≤
      d * τ + S * ∑ β ∈ Finset.range β₀, gβ β + V * S * gβ β₀ := by
    rw [← ENat.coe_le_coe, ENat.coe_toNat hne]
    exact hL
  have hg_le : ∀ β, (gβ β : ℝ) ≤ 2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial) :=
    fun β => Nat.floor_le (by positivity)
  have hterm : ∀ β, 2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial) ≤ 2 * d * s * s ^ β := by
    intro β
    have hf : (1 : ℝ) ≤ (β + 1).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    calc 2 * (d : ℝ) * (s ^ (β + 1) / (β + 1).factorial) ≤ 2 * d * s ^ (β + 1) :=
          mul_le_mul_of_nonneg_left (div_le_self (pow_nonneg hs0 _) hf) (by positivity)
      _ = 2 * d * s * s ^ β := by ring
  have hsum : (∑ β ∈ Finset.range β₀, (gβ β : ℝ)) ≤ 4 * d * s := by
    calc ∑ β ∈ Finset.range β₀, (gβ β : ℝ) ≤ ∑ β ∈ Finset.range β₀, 2 * (d : ℝ) * s * s ^ β :=
          Finset.sum_le_sum fun β _ => (hg_le β).trans (hterm β)
      _ = 2 * d * s * ∑ β ∈ Finset.range β₀, s ^ β := by rw [Finset.mul_sum]
      _ ≤ 2 * d * s * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [geom_le s hs0 hs β₀, pow_nonneg hs0 β₀]
      _ = 4 * d * s := by ring
  have hcast : ((Module.length R (↥M ⧸ (N.comap M.subtype ⊓ (Ideal.span {π ^ τ}) •
      (⊤ : Submodule R M)))).toNat : ℝ) ≤
      (d : ℝ) * τ + S * ∑ β ∈ Finset.range β₀, (gβ β : ℝ) + V * S * (gβ β₀ : ℝ) := by
    exact_mod_cast hnat
  calc _ ≤ (d : ℝ) * τ + S * ∑ β ∈ Finset.range β₀, (gβ β : ℝ) + V * S * (gβ β₀ : ℝ) := hcast
    _ ≤ (d : ℝ) * τ + S * (4 * d * s) + V * S * (2 * (d : ℝ) * (s ^ (β₀ + 1) / (β₀ + 1).factorial)) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by positivity)))
          (mul_le_mul_of_nonneg_left (hg_le β₀) (by positivity))
    _ = d * (τ + 4 * S * s + V * S * (2 * s ^ (β₀ + 1) / (β₀ + 1).factorial)) := by ring

end ManyOrbitsP

theorem manyOrbits_of (hW : WalkSharp) : ManyOrbits := by
  intro R X _ _ _ _ _ V π hπ L y m β₀ c₀ S d a b c Sv κ G _ _ hd hm hcomm hb1 hb2 hb3 hb4 hb5
    hb6 hG hκ habc hSv hs
  have hprod : ∀ B : Finset (Fin V), 0 ≤ 2 * (∏ v ∈ B, κ v) * (d : ℝ) := fun B =>
    mul_nonneg (mul_nonneg zero_le_two (Finset.prod_nonneg fun v _ => hκ v)) (Nat.cast_nonneg d)
  have ws : ∀ β ≤ β₀ + 1,
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base))
        (∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
          m ^ (β + 1) * ⌊2 * (∏ v ∈ B, κ v) * (d : ℝ)⌋₊)
        (∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S) ∧
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
        (∑ v, Sv v) := by
    intro β hβ
    exact hW V π L y m β c₀ S a b c Sv (fun B => ⌊2 * (∏ v ∈ B, κ v) * (d : ℝ)⌋₊) G hm hcomm
      hb1 hb2 hb3 hb4 hb5 hb6
      (fun B hB => ⟨(hG B (by omega)).1, Nat.le_floor (hG B (by omega)).2.1,
        (hG B (by omega)).2.2⟩) hSv
  have hexp : ∑ v, (a v + b v + (m - 1) * c v + m * c₀) ≤ ∑ v, m * (c v + c₀) := by
    apply Finset.sum_le_sum
    intro v _
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have := habc v
    simp only [Nat.add_sub_cancel]
    nlinarith
  have cl1 : ∀ β ≤ β₀ + 1, ∃ C : Finset X, (↑C : Set X) ⊆ (L fun _ => Slot.base) ∧
      (C.card : ℝ) ≤ 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d ∧
      ∀ x ∈ (L fun _ => Slot.base), π ^ (∑ v, m * (c v + c₀) + β * S) • x ∈
        prodIdealMap π y m Sv (L fun _ => Slot.base) ⊔ Submodule.span R (↑C : Set X) := by
    intro β hβ
    obtain ⟨C, hCM, hcard, hx⟩ :=
      ManyOrbitsP.allBut_mono (ws β hβ).1 le_rfl (Nat.add_le_add_right hexp _)
    refine ⟨C, hCM, ?_, hx⟩
    calc (C.card : ℝ)
        ≤ ((∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
            m ^ (β + 1) * ⌊2 * (∏ v ∈ B, κ v) * (d : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcard
      _ ≤ ∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1),
            (m : ℝ) ^ (β + 1) * (2 * (∏ v ∈ B, κ v) * d) := by
          push_cast
          apply Finset.sum_le_sum
          intro B _
          exact mul_le_mul_of_nonneg_left (Nat.floor_le (hprod B)) (by positivity)
      _ = 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d := by
          unfold esymmR
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro B _
          ring
  have hs0 : 0 ≤ (m : ℝ) * ∑ v, κ v :=
    mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg fun v _ => hκ v)
  have hVS : ∑ v, Sv v ≤ V * S := by
    calc ∑ v, Sv v ≤ ∑ _v : Fin V, S := Finset.sum_le_sum fun v _ => hSv v
      _ = V * S := by simp
  refine ⟨cl1, (ws 0 (by omega)).2, ?_⟩
  refine ManyOrbitsP.lengthPart π hπ (L fun _ => Slot.base)
    (prodIdealMap π y m Sv (L fun _ => Slot.base)) d hd (∑ v, m * (c v + c₀)) S V β₀
    ((m : ℝ) * ∑ v, κ v) hs0 hs ?_ (ManyOrbitsP.allBut_mono (ws 0 (by omega)).2 le_rfl hVS)
  intro β hβ
  obtain ⟨C, hCM, hcard, hx⟩ := cl1 β (by omega)
  refine ⟨C, hCM, ?_, hx⟩
  have hmac := ManyOrbitsP.esymmR_le κ hκ (m : ℝ) (Nat.cast_nonneg m) (β + 1)
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  calc (C.card : ℝ) ≤ 2 * (m : ℝ) ^ (β + 1) * esymmR κ (β + 1) * d := hcard
    _ = 2 * d * ((m : ℝ) ^ (β + 1) * esymmR κ (β + 1)) := by ring
    _ ≤ 2 * d * (((m : ℝ) * ∑ v, κ v) ^ (β + 1) / (β + 1).factorial) :=
        mul_le_mul_of_nonneg_left hmac hd0

theorem many_orbits : ManyOrbits := manyOrbits_of walkSharp_true

end Formalism.G0
