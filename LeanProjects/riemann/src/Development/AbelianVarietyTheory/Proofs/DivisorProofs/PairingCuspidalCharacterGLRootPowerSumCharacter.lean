import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingHarishChandraInductionCharpolyFunctionStatement

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem deg_map_const_fst (m : ℕ) (e : ℕ → ℕ) (L : List ℕ) :
    deg (L.map fun i => (m, e i)) = m * L.length := by
  induction L with
  | nil => simp [deg]
  | cons a L ih =>
    simp only [deg, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem pair_prod_split {F : Type} [Field F] [Fintype F] {a b : ℕ} (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (r : ℕ → F[X] → ℂ) (hr : ∀ j, IsAdditive (r j)) (T : Finset ℕ) :
    ∑ᶠ x : GL (Fin a) F, ∑ᶠ y : GL (Fin b) F, α x * β y *
      star ((fun P => ∏ j ∈ T, r j P) (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) *
        Matrix.charpoly (y : Matrix (Fin b) (Fin b) F))) =
    ∑ U ∈ T.powerset, (∑ᶠ x : GL (Fin a) F, α x * star (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F)))) *
      (∑ᶠ y : GL (Fin b) F, β y * star (chG (fun P => ∏ j ∈ T \ U, r j P) b y)) := by
  simp only [finsum_eq_sum_of_fintype, chG]
  have e1 : ∀ (x : GL (Fin a) F) (y : GL (Fin b) F),
      ∏ j ∈ T, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F) * Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) =
      ∑ U ∈ T.powerset, (∏ j ∈ U, r j (Matrix.charpoly (x : Matrix (Fin a) (Fin a) F))) *
        ∏ j ∈ T \ U, r j (Matrix.charpoly (y : Matrix (Fin b) (Fin b) F)) := by
    intro x y
    rw [← Finset.prod_add]
    exact Finset.prod_congr rfl fun j _ => hr j _ _ (Matrix.charpoly_monic _) (Matrix.charpoly_monic _)
  simp only [e1, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_powerset_single (i : ℕ) (S T : Finset ℕ) (hiS : i ∉ S) (hT : T.card ≤ S.card + 1)
    (f g : Finset ℕ → ℂ) (A B : ℂ) (hf0 : f ∅ = 0) (hf1 : ∀ j ∈ T, f {j} = if i = j then A else 0)
    (hg : ∀ U ∈ T.powerset, U ≠ ∅ → g U = if T \ U = S then B else 0) :
    ∑ U ∈ T.powerset, f U * g U = if T = insert i S then A * B else 0 := by
  have hz : ∀ U ∈ T.powerset, U ≠ {i} → f U * g U = 0 := by
    intro U hU hUi
    by_cases h0 : U = ∅
    · rw [h0, hf0, zero_mul]
    rw [hg U hU h0]
    split_ifs with hc
    · have hsub : U ⊆ T := Finset.mem_powerset.1 hU
      have h1 := Finset.card_sdiff_add_card_eq_card hsub
      rw [hc] at h1
      have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h0)
      have hU1 : U.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hU1
      have hjT : j ∈ T := hsub (Finset.mem_singleton_self j)
      rw [hf1 j hjT, if_neg (fun h => hUi (by rw [h])), zero_mul]
    · rw [mul_zero]
  by_cases hiT : i ∈ T
  · have hmem : {i} ∈ T.powerset := Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hiT)
    rw [Finset.sum_eq_single_of_mem {i} hmem hz, hf1 i hiT, if_pos rfl,
      hg {i} hmem (Finset.singleton_ne_empty i)]
    have hiff : (T \ {i} = S) ↔ T = insert i S := by
      constructor
      · intro h
        rw [← h, Finset.sdiff_singleton_eq_erase, Finset.insert_erase hiT]
      · intro h
        rw [h, Finset.sdiff_singleton_eq_erase, Finset.erase_insert hiS]
    by_cases hc : T = insert i S
    · rw [if_pos (hiff.2 hc), if_pos hc]
    · rw [if_neg (fun h => hc (hiff.1 h)), if_neg hc, mul_zero]
  · rw [Finset.sum_eq_zero fun U hU => hz U hU (fun h => hiT (by
      rw [h] at hU; exact Finset.singleton_subset_iff.1 (Finset.mem_powerset.1 hU)))]
    rw [if_neg (fun h => hiT (by rw [h]; exact Finset.mem_insert_self i S))]

theorem pair_J_prod_rootSum : ∀ (F : Type) [Field F] [Finite F], ∀ (θ : AlgebraicClosure F →* ℂ) (m : ℕ) (e : ℕ → ℕ) (ε : ℤ), (∀ i, ∑ᶠ x, cusp θ m (e i) x = 0) → ∀ N : ℕ, (∀ i j, i < N → j < N → ∑ᶠ x, cusp θ m (e i) x * star (chG (rootSum θ (e j)) m x) = if i = j then (ε : ℂ) * (Nat.card (GL (Fin m) F) : ℂ) else 0) → ∀ (L : List ℕ) (T : Finset ℕ), L.Nodup → (∀ i ∈ L, i < N) → (∀ j ∈ T, j < N) → T.card ≤ L.length → ∀ n, n = m * L.length → ∑ᶠ x, J θ (L.map fun i => (m, e i)) n x * star (chG (fun P => ∏ j ∈ T, rootSum θ (e j) P) n x) = if T = L.toFinset then (ε : ℂ) ^ L.length * (Nat.card (GL (Fin n) F) : ℂ) else 0 := by
  intro F _ _ θ m e ε h1 N h2 L
  induction L with
  | nil =>
    intro T _ _ _ hT n hn
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (by simpa using hT)
    subst hT0
    simp only [List.length_nil, mul_zero] at hn
    subst hn
    haveI : Subsingleton (GL (Fin 0) F) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    haveI : Unique (GL (Fin 0) F) := ⟨⟨1⟩, fun a => Subsingleton.elim _ _⟩
    simp [J_nil, chG, finsum_unique]
  | cons i L ih =>
    intro T hnd hLN hTN hT n hn
    haveI : Fintype F := Fintype.ofFinite F
    have hiS : i ∉ L.toFinset := by simpa using (List.nodup_cons.1 hnd).1
    have hnd' : L.Nodup := (List.nodup_cons.1 hnd).2
    have hb := deg_map_const_fst m e L
    have hn' : n = m + deg (L.map fun i => (m, e i)) := by rw [hn, hb, List.length_cons]; ring
    have hmass := GlobalTheory.T.pairing_harishChandraInduction_charpolyFunction F m (deg (L.map fun i => (m, e i))) n hn' (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i)))) (fun P => ∏ j ∈ T, rootSum θ (e j) P)
    have hs := pair_prod_split (cusp θ m (e i))
      (J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))))
      (fun j => rootSum θ (e j)) (fun j => (rootSum_isAdditive_and_pow_X_sub_one F θ (e j)).1) T
    have hiN : i < N := hLN i (List.mem_cons_self ..)
    have hsum := sum_powerset_single i L.toFinset T hiS
      (by rw [List.toFinset_card_of_nodup hnd']; simpa using hT)
      (fun U => ∑ᶠ x : GL (Fin m) F, cusp θ m (e i) x *
        star (∏ j ∈ U, rootSum θ (e j) (Matrix.charpoly (x : Matrix (Fin m) (Fin m) F))))
      (fun U => ∑ᶠ y : GL (Fin (deg (L.map fun i => (m, e i)))) F,
        J θ (L.map fun i => (m, e i)) (deg (L.map fun i => (m, e i))) y *
          star (chG (fun P => ∏ j ∈ T \ U, rootSum θ (e j) P) (deg (L.map fun i => (m, e i))) y))
      ((ε : ℂ) * Nat.card (GL (Fin m) F))
      ((ε : ℂ) ^ L.length * Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F))
      (by simpa using h1 i)
      (fun j hj => by simpa [chG] using h2 i j hiN (hTN j hj))
      (fun U hU hU0 => by
        have hsub := Finset.mem_powerset.1 hU
        have hc := Finset.card_sdiff_add_card_eq_card hsub
        have hpos : 0 < U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hU0)
        simp only [List.length_cons] at hT
        exact ih (T \ U) hnd' (fun k hk => hLN k (List.mem_cons_of_mem _ hk))
          (fun k hk => hTN k (Finset.mem_sdiff.1 hk).1) (by omega) _ hb)
    beta_reduce at hmass hs hsum
    rw [hs, hsum] at hmass
    have hG : ((Nat.card (GL (Fin m) F) : ℂ) *
        (Nat.card (GL (Fin (deg (L.map fun i => (m, e i)))) F) : ℂ)) ≠ 0 := by
      apply mul_ne_zero <;> exact_mod_cast Nat.card_pos.ne'
    apply mul_left_cancel₀ hG
    refine hmass.trans ?_
    rw [List.toFinset_cons, List.length_cons]
    split_ifs <;> ring

end GlobalTheory.Shin

end
