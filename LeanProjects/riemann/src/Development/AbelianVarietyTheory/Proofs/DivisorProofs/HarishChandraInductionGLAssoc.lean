import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjectionStatement

noncomputable section

namespace GlobalTheory.Shin.HcAssoc

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

def InParM (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → M i j = 0

theorem inPar_eq (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a x ↔ InParM a (x : Matrix (Fin n) (Fin n) F) := Iff.rfl

theorem gal_id (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

theorem inPar_one (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  show (1 : Matrix (Fin n) (Fin n) F) i j = 0
  rw [Matrix.one_apply_ne]
  intro h
  rw [h] at hi
  omega

theorem coe_tlG {a b n : ℕ} (hn : n = a + b) (x : GL (Fin n) F) (hx : InPar a x) :
    ((tlG a x : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = tl a (x : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨H, π, hH, -, hπ, hπ', -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have h := (hπ' ⟨x, (hH x).2 hx⟩).1
  rw [hπ] at h
  exact h

theorem coe_brG {a b n : ℕ} (hn : n = a + b) (x : GL (Fin n) F) (hx : InPar a x) :
    ((brG a b x : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) = br a b (x : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨H, π, hH, -, hπ, hπ', -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  have h := (hπ' ⟨x, (hH x).2 hx⟩).2
  rw [hπ] at h
  exact h

theorem conj_blocks {a b n : ℕ} (hn : n = a + b) (h₁ : GL (Fin a) F) (h₂ : GL (Fin b) F) :
    ∃ s : GL (Fin n) F, ∀ z : GL (Fin n) F, (InPar a (s⁻¹ * z * s) ↔ InPar a z) ∧
      (InPar a z → tlG a (s⁻¹ * z * s) = h₁⁻¹ * tlG a z * h₁ ∧
        brG a b (s⁻¹ * z * s) = h₂⁻¹ * brG a b z * h₂) := by
  obtain ⟨H, π, hH, hsu, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  obtain ⟨s, hs⟩ := hsu (h₁, h₂)
  refine ⟨s.1, fun z => ⟨?_, fun hz => ?_⟩⟩
  · rw [← hH, ← hH]
    constructor
    · intro h
      have := H.mul_mem (H.mul_mem s.2 h) (H.inv_mem s.2)
      rwa [show s.1 * (s.1⁻¹ * z * s.1) * s.1⁻¹ = z by group] at this
    · intro h
      exact H.mul_mem (H.mul_mem (H.inv_mem s.2) h) s.2
  · have hz' : z ∈ H := (hH z).2 hz
    have e := hπ (s⁻¹ * ⟨z, hz'⟩ * s)
    rw [map_mul, map_mul, map_inv, hπ ⟨z, hz'⟩, hs] at e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv, Subgroup.coe_mul,
      Subgroup.coe_inv] at e1 e2
    exact ⟨e1.symm, e2.symm⟩

def hcT [Fintype F] (a b : ℕ) (Φ : GL (Fin a) F → GL (Fin b) F → ℂ) (n : ℕ) (x : GL (Fin n) F) : ℂ :=
  ∑ y : GL (Fin n) F, if InPar a (y⁻¹ * x * y) then
    Φ (tlG a (y⁻¹ * x * y)) (brG a b (y⁻¹ * x * y)) else 0

def blk0 (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) (z : GL (Fin n) F) : ℂ :=
  if InPar a z then α (tlG a z) * β (brG a b z) else 0

theorem hc_eq [Fintype F] (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    hc a b α β n x = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
      hcT a b (fun u v => α u * β v) n x := by
  simp only [hc, hcTw, hcT, gal_id, finsum_eq_sum_of_fintype]

theorem hc_eq' [Fintype F] (a b : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (n : ℕ) (x : GL (Fin n) F) :
    hc a b α β n x = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
      ∑ y : GL (Fin n) F, blk0 a b α β n (y⁻¹ * x * y) :=
  hc_eq a b α β n x

theorem hcT_conj [Fintype F] {a b n : ℕ} (hn : n = a + b) (Φ : GL (Fin a) F → GL (Fin b) F → ℂ)
    (h₁ : GL (Fin a) F) (h₂ : GL (Fin b) F) (x : GL (Fin n) F) :
    hcT a b (fun u v => Φ (h₁⁻¹ * u * h₁) (h₂⁻¹ * v * h₂)) n x = hcT a b Φ n x := by
  obtain ⟨s, hs⟩ := conj_blocks hn h₁ h₂
  unfold hcT
  refine Fintype.sum_equiv (Equiv.mulRight s) _ _ fun y => ?_
  have e : (y * s)⁻¹ * x * (y * s) = s⁻¹ * (y⁻¹ * x * y) * s := by group
  simp only [Equiv.coe_mulRight, e]
  by_cases hz : InPar a (y⁻¹ * x * y)
  · rw [if_pos hz, if_pos ((hs _).1.2 hz), ((hs _).2 hz).1, ((hs _).2 hz).2]
  · rw [if_neg hz, if_neg (fun h => hz ((hs _).1.1 h))]

theorem hcT_sum [Fintype F] {a b n : ℕ} {ι : Type} [Fintype ι] (Φ : ι → GL (Fin a) F → GL (Fin b) F → ℂ)
    (x : GL (Fin n) F) : hcT a b (fun u v => ∑ i, Φ i u v) n x = ∑ i, hcT a b (Φ i) n x := by
  unfold hcT
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem hcT_smul [Fintype F] {a b n : ℕ} (k : ℂ) (Φ : GL (Fin a) F → GL (Fin b) F → ℂ) (x : GL (Fin n) F) :
    hcT a b (fun u v => k * Φ u v) n x = k * hcT a b Φ n x := by
  unfold hcT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem stage_left [Fintype F] {m c n : ℕ} (hn : n = m + c) (k : ℂ) (φ Fm : GL (Fin m) F → ℂ)
    (γ : GL (Fin c) F → ℂ) (hF : ∀ u, Fm u = k * ∑ h : GL (Fin m) F, φ (h⁻¹ * u * h)) (x : GL (Fin n) F) :
    hcT m c (fun u v => Fm u * γ v) n x =
      k * (Nat.card (GL (Fin m) F) : ℂ) * hcT m c (fun u v => φ u * γ v) n x := by
  have e : (fun (u : GL (Fin m) F) (v : GL (Fin c) F) => Fm u * γ v) =
      fun u v => ∑ h : GL (Fin m) F, k * (φ (h⁻¹ * u * h) * γ ((1 : GL (Fin c) F)⁻¹ * v * 1)) := by
    funext u v
    rw [hF]
    simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [e, hcT_sum]
  rw [Finset.sum_congr rfl fun h _ =>
    (show hcT m c (fun u v => k * (φ (h⁻¹ * u * h) * γ ((1 : GL (Fin c) F)⁻¹ * v * 1))) n x =
      k * hcT m c (fun u v => φ u * γ v) n x from
      (hcT_smul k _ x).trans (congrArg _ (hcT_conj hn (fun u v => φ u * γ v) h 1 x)))]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

theorem stage_right [Fintype F] {a m n : ℕ} (hn : n = a + m) (k : ℂ) (φ Fm : GL (Fin m) F → ℂ)
    (α : GL (Fin a) F → ℂ) (hF : ∀ u, Fm u = k * ∑ h : GL (Fin m) F, φ (h⁻¹ * u * h)) (x : GL (Fin n) F) :
    hcT a m (fun u v => α u * Fm v) n x =
      k * (Nat.card (GL (Fin m) F) : ℂ) * hcT a m (fun u v => α u * φ v) n x := by
  have e : (fun (u : GL (Fin a) F) (v : GL (Fin m) F) => α u * Fm v) =
      fun u v => ∑ h : GL (Fin m) F, k * (α ((1 : GL (Fin a) F)⁻¹ * u * 1) * φ (h⁻¹ * v * h)) := by
    funext u v
    rw [hF]
    simp [Finset.mul_sum, Finset.sum_mul, mul_left_comm]
  rw [e, hcT_sum]
  rw [Finset.sum_congr rfl fun h _ =>
    (show hcT a m (fun u v => k * (α ((1 : GL (Fin a) F)⁻¹ * u * 1) * φ (h⁻¹ * v * h))) n x =
      k * hcT a m (fun u v => α u * φ v) n x from
      (hcT_smul k _ x).trans (congrArg _ (hcT_conj hn (fun u v => α u * φ v) 1 h x)))]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

theorem ent_tl {m n : ℕ} (M : Matrix (Fin n) (Fin n) F) {i j : ℕ} (hi : i < m) (hj : j < m) :
    ent (tl m M) i j = ent M i j := by
  unfold ent
  rw [dif_pos ⟨hi, hj⟩]
  rfl

theorem ent_br {a m n : ℕ} (M : Matrix (Fin n) (Fin n) F) {i j : ℕ} (hi : i < m) (hj : j < m) :
    ent (br a m M) i j = ent M (a + i) (a + j) := by
  unfold ent
  rw [dif_pos ⟨hi, hj⟩]
  rfl

theorem inParM_iff {a n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    InParM a M ↔ ∀ i j : ℕ, i < n → j < a → a ≤ i → ent M i j = 0 := by
  constructor
  · intro h i j hi hj ha
    unfold ent
    rw [dif_pos ⟨hi, by omega⟩]
    exact h _ _ hj ha
  · intro h i j hj ha
    have := h i j i.2 hj ha
    unfold ent at this
    rw [dif_pos ⟨i.2, j.2⟩] at this
    exact this

theorem par_par {a b c n : ℕ} (hn : n = a + b + c) (M : Matrix (Fin n) (Fin n) F) :
    (InParM (a + b) M ∧ InParM a (tl (a + b) M)) ↔ (InParM a M ∧ InParM b (br a (b + c) M)) := by
  simp only [inParM_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hi hj ha => ?_, fun i j hi hj ha => ?_⟩
    · by_cases h : i < a + b
      · rw [← ent_tl M h (by omega : j < a + b)]
        exact h2 i j h hj ha
      · exact h1 i j hi (by omega) (by omega)
    · rw [ent_br M hi (by omega)]
      exact h1 _ _ (by omega) (by omega) (by omega)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hi hj ha => ?_, fun i j hi hj ha => ?_⟩
    · by_cases h : j < a
      · exact h1 i j hi h (by omega)
      · have := h2 (i - a) (j - a) (by omega) (by omega) (by omega)
        rw [ent_br M (by omega) (by omega)] at this
        rwa [show a + (i - a) = i by omega, show a + (j - a) = j by omega] at this
    · rw [ent_tl M hi (by omega)]
      exact h1 _ _ (by omega) hj ha

theorem par_parG {a b c n : ℕ} (hn : n = a + b + c) (z : GL (Fin n) F) :
    (InPar (a + b) z ∧ InPar a (tlG (a + b) z)) ↔ (InPar a z ∧ InPar b (brG a (b + c) z)) := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [inPar_eq, coe_tlG hn z h1] at h2
    obtain ⟨h3, h4⟩ := (par_par hn (z : Matrix (Fin n) (Fin n) F)).1 ⟨h1, h2⟩
    refine ⟨h3, ?_⟩
    rw [inPar_eq, coe_brG (by omega : n = a + (b + c)) z h3]
    exact h4
  · rintro ⟨h3, h4⟩
    rw [inPar_eq, coe_brG (by omega : n = a + (b + c)) z h3] at h4
    obtain ⟨h1, h2⟩ := (par_par hn (z : Matrix (Fin n) (Fin n) F)).2 ⟨h3, h4⟩
    refine ⟨h1, ?_⟩
    rw [inPar_eq, coe_tlG hn z h1]
    exact h2

theorem parabolicDiagonalBlocksProduct_assoc {a b c n : ℕ} (hn : n = a + b + c) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ)
    (γ : GL (Fin c) F → ℂ) (z : GL (Fin n) F) :
    blk0 (a + b) c (blk0 a b α β (a + b)) γ n z = blk0 a (b + c) α (blk0 b c β γ (b + c)) n z := by
  have hn' : n = a + (b + c) := by omega
  have pp := par_parG hn z
  have t1 : tl a (tl (a + b) (z : Matrix (Fin n) (Fin n) F)) = tl a (z : Matrix (Fin n) (Fin n) F) := by
    funext i j
    exact ent_tl _ (by omega) (by omega)
  have t2 : br a b (tl (a + b) (z : Matrix (Fin n) (Fin n) F)) =
      tl b (br a (b + c) (z : Matrix (Fin n) (Fin n) F)) := by
    funext i j
    exact (ent_tl _ (by omega) (by omega)).trans (ent_br _ (by omega) (by omega)).symm
  have t3 : br b c (br a (b + c) (z : Matrix (Fin n) (Fin n) F)) = br (a + b) c (z : Matrix (Fin n) (Fin n) F) := by
    funext i j
    refine (ent_br _ (by omega) (by omega)).trans ?_
    rw [← add_assoc, ← add_assoc]
    rfl
  unfold blk0
  by_cases h1 : InPar (a + b) z
  · rw [if_pos h1]
    by_cases h2 : InPar a (tlG (a + b) z)
    · obtain ⟨h3, h4⟩ := pp.1 ⟨h1, h2⟩
      have e1 : tlG a (tlG (a + b) z) = tlG a z := by
        show toG (tl a ((tlG (a + b) z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)) =
          toG (tl a ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        rw [coe_tlG hn z h1, t1]
      have e2 : brG a b (tlG (a + b) z) = tlG b (brG a (b + c) z) := by
        show toG (br a b ((tlG (a + b) z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F)) =
          toG (tl b ((brG a (b + c) z : GL (Fin (b + c)) F) : Matrix (Fin (b + c)) (Fin (b + c)) F))
        rw [coe_tlG hn z h1, coe_brG hn' z h3, t2]
      have e3 : brG b c (brG a (b + c) z) = brG (a + b) c z := by
        show toG (br b c ((brG a (b + c) z : GL (Fin (b + c)) F) : Matrix (Fin (b + c)) (Fin (b + c)) F)) =
          toG (br (a + b) c ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        rw [coe_brG hn' z h3, t3]
      rw [if_pos h2, if_pos h3, if_pos h4, e1, e2, e3, mul_assoc]
    · rw [if_neg h2, zero_mul]
      by_cases h3 : InPar a z
      · rw [if_pos h3, if_neg (fun h4 => h2 (pp.2 ⟨h3, h4⟩).2), mul_zero]
      · rw [if_neg h3]
  · rw [if_neg h1]
    by_cases h3 : InPar a z
    · rw [if_pos h3, if_neg (fun h4 => h1 (pp.2 ⟨h3, h4⟩).1), mul_zero]
    · rw [if_neg h3]

theorem card_comap {H L : Type} [Group H] [Group L] (π : H →* L) (hπ : Function.Surjective π)
    (M : Subgroup L) : Nat.card (M.comap π) * Nat.card L = Nat.card M * Nat.card H := by
  have h1 := Subgroup.card_mul_index (M.comap π)
  have h2 := Subgroup.card_mul_index M
  rw [Subgroup.index_comap_of_surjective M hπ] at h1
  rw [← h1, ← h2]
  ring

theorem card_left [Finite F] {a b c n : ℕ} (hn : n = a + b + c) :
    Nat.card {x : GL (Fin n) F // InPar (a + b) x ∧ InPar a (tlG (a + b) x)} * Nat.card (GL (Fin (a + b)) F) =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} * Nat.card {p : GL (Fin n) F // InPar (a + b) p} := by
  obtain ⟨H, π, hH, hsu, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F (a + b) c n hn
  obtain ⟨H', -, hH', -, -, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b (a + b) rfl
  have k := card_comap π hsu (H'.prod ⊤)
  have mem : ∀ p : H, p ∈ (H'.prod ⊤).comap π ↔ InPar a (tlG (a + b) p.1) := by
    intro p
    rw [Subgroup.mem_comap, Subgroup.mem_prod, hπ]
    simp [hH']
  have e1 : Nat.card ((H'.prod ⊤).comap π) =
      Nat.card {x : GL (Fin n) F // InPar (a + b) x ∧ InPar a (tlG (a + b) x)} :=
    Nat.card_congr ⟨fun p => ⟨p.1.1, (hH _).1 p.1.2, (mem p.1).1 p.2⟩,
      fun x => ⟨⟨x.1, (hH _).2 x.2.1⟩, (mem _).2 x.2.2⟩, fun p => rfl, fun x => rfl⟩
  have e2 : Nat.card (H'.prod (⊤ : Subgroup (GL (Fin c) F))) =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} * Nat.card (GL (Fin c) F) := by
    rw [Nat.card_congr (Subgroup.prodEquiv H' ⊤).toEquiv, Nat.card_prod, Subgroup.card_top,
      Nat.card_congr (Equiv.subtypeEquivRight hH')]
  have e3 : Nat.card H = Nat.card {p : GL (Fin n) F // InPar (a + b) p} :=
    Nat.card_congr (Equiv.subtypeEquivRight hH)
  rw [e1, e2, e3, Nat.card_prod] at k
  have hc : 0 < Nat.card (GL (Fin c) F) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hc
  rw [mul_assoc, k]
  ring

theorem card_right [Finite F] {a b c n : ℕ} (hn : n = a + b + c) :
    Nat.card {x : GL (Fin n) F // InPar a x ∧ InPar b (brG a (b + c) x)} * Nat.card (GL (Fin (b + c)) F) =
      Nat.card {p : GL (Fin (b + c)) F // InPar b p} * Nat.card {p : GL (Fin n) F // InPar a p} := by
  obtain ⟨H, π, hH, hsu, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a (b + c) n (by omega)
  obtain ⟨H', -, hH', -, -, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F b c (b + c) rfl
  have k := card_comap π hsu ((⊤ : Subgroup (GL (Fin a) F)).prod H')
  have mem : ∀ p : H, p ∈ ((⊤ : Subgroup (GL (Fin a) F)).prod H').comap π ↔ InPar b (brG a (b + c) p.1) := by
    intro p
    rw [Subgroup.mem_comap, Subgroup.mem_prod, hπ]
    simp [hH']
  have e1 : Nat.card (((⊤ : Subgroup (GL (Fin a) F)).prod H').comap π) =
      Nat.card {x : GL (Fin n) F // InPar a x ∧ InPar b (brG a (b + c) x)} :=
    Nat.card_congr ⟨fun p => ⟨p.1.1, (hH _).1 p.1.2, (mem p.1).1 p.2⟩,
      fun x => ⟨⟨x.1, (hH _).2 x.2.1⟩, (mem _).2 x.2.2⟩, fun p => rfl, fun x => rfl⟩
  have e2 : Nat.card ((⊤ : Subgroup (GL (Fin a) F)).prod H') =
      Nat.card (GL (Fin a) F) * Nat.card {p : GL (Fin (b + c)) F // InPar b p} := by
    rw [Nat.card_congr (Subgroup.prodEquiv ⊤ H').toEquiv, Nat.card_prod, Subgroup.card_top,
      Nat.card_congr (Equiv.subtypeEquivRight hH')]
  have e3 : Nat.card H = Nat.card {p : GL (Fin n) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight hH)
  rw [e1, e2, e3, Nat.card_prod] at k
  have ha : 0 < Nat.card (GL (Fin a) F) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left ha
  rw [show Nat.card (GL (Fin a) F) * (Nat.card {x : GL (Fin n) F // InPar a x ∧ InPar b (brG a (b + c) x)} *
    Nat.card (GL (Fin (b + c)) F)) = Nat.card {x : GL (Fin n) F // InPar a x ∧ InPar b (brG a (b + c) x)} *
    (Nat.card (GL (Fin a) F) * Nat.card (GL (Fin (b + c)) F)) by ring, k]
  ring

theorem const_eq [Finite F] {a b c n : ℕ} (hn : n = a + b + c) (S : ℂ) :
    (Nat.card {p : GL (Fin n) F // InPar (a + b) p} : ℂ)⁻¹ *
      ((Nat.card {p : GL (Fin (a + b)) F // InPar a p} : ℂ)⁻¹ * (Nat.card (GL (Fin (a + b)) F) : ℂ) * S) =
    (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ *
      ((Nat.card {p : GL (Fin (b + c)) F // InPar b p} : ℂ)⁻¹ * (Nat.card (GL (Fin (b + c)) F) : ℂ) * S) := by
  have hq1 := card_left (F := F) hn
  have hq2 := card_right (F := F) hn
  rw [Nat.card_congr (Equiv.subtypeEquivRight (par_parG hn))] at hq1
  set Q := Nat.card {x : GL (Fin n) F // InPar a x ∧ InPar b (brG a (b + c) x)}
  set A := Nat.card {p : GL (Fin n) F // InPar (a + b) p}
  set B := Nat.card {p : GL (Fin (a + b)) F // InPar a p}
  set C := Nat.card {p : GL (Fin n) F // InPar a p}
  set D := Nat.card {p : GL (Fin (b + c)) F // InPar b p}
  set X := Nat.card (GL (Fin (a + b)) F)
  set Y := Nat.card (GL (Fin (b + c)) F)
  have hA : 0 < A := @Nat.card_pos _ ⟨⟨1, inPar_one _ _⟩⟩ _
  have hB : 0 < B := @Nat.card_pos _ ⟨⟨1, inPar_one _ _⟩⟩ _
  have hC : 0 < C := @Nat.card_pos _ ⟨⟨1, inPar_one _ _⟩⟩ _
  have hD : 0 < D := @Nat.card_pos _ ⟨⟨1, inPar_one _ _⟩⟩ _
  have hQ : 0 < Q := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hq2
    exact (Nat.mul_pos hD hC).ne' hq2.symm
  have hXY : X * C * D = Y * A * B := by
    apply Nat.eq_of_mul_eq_mul_left hQ
    rw [show Q * (X * C * D) = (Q * X) * (C * D) by ring, hq1,
      show Q * (Y * A * B) = (Q * Y) * (A * B) by ring, hq2]
    ring
  have hXYc : (X : ℂ) * C * D = Y * A * B := by exact_mod_cast hXY
  have hA' : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hA.ne'
  have hB' : (B : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hB.ne'
  have hC' : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hC.ne'
  have hD' : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  field_simp
  linear_combination S * hXYc

theorem hc_assoc : ∀ (F : Type) [Field F] [Finite F], ∀ (a b c n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (γ : GL (Fin c) F → ℂ), IsCl α → IsCl β → IsCl γ → n = a + b + c →
      hc (a + b) c (hc a b α β (a + b)) γ n = hc a (b + c) α (hc b c β γ (b + c)) n := by
  intro F _ _ a b c n α β γ _ _ _ hn
  have := Fintype.ofFinite F
  funext x
  rw [hc_eq (a + b) c, hc_eq a (b + c),
    stage_left hn _ (blk0 a b α β (a + b)) _ γ (hc_eq' a b α β (a + b)) x,
    stage_right (by omega : n = a + (b + c)) _ (blk0 b c β γ (b + c)) _ α (hc_eq' b c β γ (b + c)) x]
  have hs : hcT (a + b) c (fun u v => blk0 a b α β (a + b) u * γ v) n x =
      hcT a (b + c) (fun u v => α u * blk0 b c β γ (b + c) v) n x := by
    show ∑ y : GL (Fin n) F, blk0 (a + b) c (blk0 a b α β (a + b)) γ n (y⁻¹ * x * y) =
      ∑ y : GL (Fin n) F, blk0 a (b + c) α (blk0 b c β γ (b + c)) n (y⁻¹ * x * y)
    exact Finset.sum_congr rfl fun y _ => parabolicDiagonalBlocksProduct_assoc hn α β γ _
  rw [hs]
  exact const_eq hn _

end GlobalTheory.Shin.HcAssoc
