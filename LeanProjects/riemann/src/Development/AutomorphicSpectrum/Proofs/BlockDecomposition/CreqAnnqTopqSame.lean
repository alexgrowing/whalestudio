import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient

open Finset
open scoped InnerProductSpace
open GlobalTheory.CompanionTheory.PairMult
open Formalism.REAL (GlRel KHighest)
open CompanionTheory.D.LK (Pos)
open CompanionTheory.RgExh.U (adC)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

noncomputable section

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

theorem sgL_erase (l : Lt n) (B : Finset (Lt n)) : sgL l (B.erase l) = sgL l B := by
  unfold sgL
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sgL_sq (l : Lt n) (B : Finset (Lt n)) : sgL l B * sgL l B = 1 := by
  unfold sgL; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem creq_annq (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l (annq l x) B = if l ∈ B then x B else 0 := by
  rw [creq_app]
  split_ifs with h
  · rw [annq_app, if_neg (notMem_erase l B), insert_erase h, sgL_erase, smul_smul, sgL_sq, one_smul]
  · rfl

theorem mem_omQ {lev : Fin n → ℕ} {l : Lt n} : l ∈ omQ lev ↔ l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omQ]

theorem topq_app (lev : Fin n → ℕ) (x : V) (B : Finset (Lt n)) :
    topq lev x B = if B = omQ lev then x else 0 := by
  unfold topq
  by_cases h : B = omQ lev
  · subst h; simp
  · rw [if_neg h, Pi.single_eq_of_ne h]

theorem topq_smul (lev : Fin n → ℕ) (c : ℂ) (x : V) : topq lev (c • x) = c • topq lev x := by
  funext B
  rw [Pi.smul_apply, topq_app, topq_app]
  split_ifs <;> simp

theorem topq_zero (lev : Fin n → ℕ) : topq lev (0 : V) = 0 := by
  funext B
  rw [topq_app]
  split_ifs <;> rfl

theorem liftq_topq (lev : Fin n → ℕ) (T : Module.End ℂ V) (x : V) :
    (liftq n T : Module.End ℂ (Cq n V)) (topq lev x) = topq lev (T x) := by
  funext B
  show T (topq lev x B) = _
  rw [topq_app, topq_app]
  split_ifs <;> simp

theorem annq_topq_of_notMem {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∉ omQ lev) :
    annq l (topq lev x) = 0 := by
  funext A
  rw [annq_app, topq_app]
  have hne : insert l A ≠ omQ lev := fun e => h (e ▸ mem_insert_self l A)
  rw [if_neg hne]
  simp

theorem creq_annq_topq_same {lev : Fin n → ℕ} {l : Lt n} (x : V) (h : l ∈ omQ lev) :
    creq l (annq l (topq lev x)) = topq lev x := by
  funext B
  rw [creq_annq]
  split_ifs with hB
  · rfl
  · have hne : B ≠ omQ lev := fun e => hB (e ▸ h)
    rw [topq_app, if_neg hne]

theorem creq_annq_topq_ne {lev : Fin n → ℕ} {l m : Lt n} (x : V) (hm : m ∈ omQ lev) (hne : m ≠ l) :
    creq m (annq l (topq lev x)) = 0 := by
  funext B
  rw [creq_app]
  split_ifs with hB
  · rw [annq_app]
    split_ifs with h2
    · simp
    · have hi : insert l (B.erase m) ≠ omQ lev := fun e => by
        have hm' : m ∈ insert l (B.erase m) := e ▸ hm
        rcases mem_insert.1 hm' with h | h
        · exact hne h
        · exact notMem_erase _ _ h
      rw [topq_app, if_neg hi]
      simp
  · rfl

theorem lev_of_adC_ne {lev : Fin n → ℕ} {p q : Fin n} {i k : Pos n} (hpq : lev p = lev q)
    (hi : lev i.1.1 < lev i.1.2) (h : adC p q i k ≠ 0) : lev k.1.1 < lev k.1.2 := by
  by_cases h1 : q = i.1.1 ∧ k.1 = (p, i.1.2)
  · obtain ⟨e1, e2⟩ := h1
    rw [e2]
    show lev p < lev i.1.2
    rw [hpq, e1]
    exact hi
  · by_cases h2 : i.1.2 = p ∧ k.1 = (i.1.1, q)
    · obtain ⟨e1, e2⟩ := h2
      rw [e2]
      show lev i.1.1 < lev q
      rw [← hpq, ← e1]
      exact hi
    · exact absurd (by simp [adC, h1, h2]) h

theorem adC_diag_ne {p q : Fin n} (h : p ≠ q) (i : Pos n) : adC p q i i = 0 := by
  have h1 : ¬(q = i.1.1 ∧ i.1 = (p, i.1.2)) := fun e => h (by
    have := congrArg Prod.fst e.2
    exact (this.symm.trans e.1.symm))
  have h2 : ¬(i.1.2 = p ∧ i.1 = (i.1.1, q)) := fun e => h (by
    have := congrArg Prod.snd e.2
    exact e.1.symm.trans this)
  simp [adC, h1, h2]

theorem adC_diag_self (p : Fin n) (i : Pos n) :
    adC p p i i = (if i.1.1 = p then 1 else 0) - (if i.1.2 = p then 1 else 0) := by
  have e1 : (p = i.1.1 ∧ i.1 = (p, i.1.2)) ↔ i.1.1 = p :=
    ⟨fun h => h.1.symm, fun h => ⟨h.symm, Prod.ext h rfl⟩⟩
  have e2 : (i.1.2 = p ∧ i.1 = (i.1.1, p)) ↔ i.1.2 = p :=
    ⟨fun h => h.1, fun h => ⟨h, Prod.ext rfl h⟩⟩
  simp only [adC, e1, e2]

theorem adLq_topq {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) (x : V) :
    adLq true p q (topq lev x) =
      (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p q i i else 0) • topq lev x := by
  have hf : ∀ i : Pos n, ((false, i) : Lt n) ∉ omQ lev := fun i h => by simpa using (mem_omQ.1 h).1
  unfold adLq
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  rw [Fintype.sum_bool]
  have h0 : (∑ i : Pos n, ∑ k : Pos n, adC p q i k • creq ((true == false), k) (annq (false, i) (topq lev x))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    rw [annq_topq_of_notMem x (hf i), map_zero, smul_zero]
  rw [h0, add_zero, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : lev i.1.1 < lev i.1.2
  · rw [if_pos hi, Finset.sum_eq_single i]
    · exact congrArg _ (creq_annq_topq_same x (mem_omQ.2 ⟨rfl, hi⟩))
    · intro k _ hk
      by_cases hc : adC p q i k = 0
      · rw [hc, zero_smul]
      · have hk' : ((true, k) : Lt n) ≠ (true, i) := fun e => hk (congrArg Prod.snd e)
        have := creq_annq_topq_ne (lev := lev) x (mem_omQ.2 ⟨rfl, lev_of_adC_ne hpq hi hc⟩) hk'
        show adC p q i k • creq (true, k) (annq (true, i) (topq lev x)) = 0
        rw [this, smul_zero]
    · simp
  · have hn : ((true, i) : Lt n) ∉ omQ lev := fun h => hi (mem_omQ.1 h).2
    rw [if_neg hi, zero_smul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [annq_topq_of_notMem x hn, map_zero, smul_zero]

theorem sum_diag {lev : Fin n → ℕ} (hm : Monotone lev) (p : Fin n) :
    (∑ i : Pos n, if lev i.1.1 < lev i.1.2 then adC p p i i else 0) = ((2 * rhoU lev p : ℝ) : ℂ) := by
  have hs : ∀ i : Pos n, (if lev i.1.1 < lev i.1.2 then adC p p i i else 0) =
      (if lev i.1.1 < lev i.1.2 ∧ i.1.1 = p then (1 : ℂ) else 0) -
        (if lev i.1.1 < lev i.1.2 ∧ i.1.2 = p then (1 : ℂ) else 0) := by
    intro i
    rw [adC_diag_self]
    by_cases h : lev i.1.1 < lev i.1.2 <;> simp [h]
  have c1 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.1 = p).card =
      (univ.filter fun b => lev p < lev b).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) e)
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(p, b), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  have c2 : (univ.filter fun i : Pos n => lev i.1.1 < lev i.1.2 ∧ i.1.2 = p).card =
      (univ.filter fun b => lev b < lev p).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      obtain ⟨h1, h2⟩ := (mem_filter.1 hi).2
      exact mem_filter.2 ⟨mem_univ _, h2 ▸ h1⟩
    · intro i hi j hj e
      have h1 := (mem_filter.1 hi).2.2
      have h2 := (mem_filter.1 hj).2.2
      exact Subtype.ext (Prod.ext e (h1.trans h2.symm))
    · intro b hb
      have hb' := (mem_filter.1 hb).2
      exact ⟨⟨(b, p), hm.reflect_lt hb'⟩, mem_filter.2 ⟨mem_univ _, hb', rfl⟩, rfl⟩
  rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole, c1, c2]
  simp only [rhoU]
  push_cast
  ring

end GlobalTheory.CompanionTheory.PairMult.TopK

namespace GlobalTheory.CompanionTheory.PairMult.TopK

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem rhoU_eq {lev : Fin n → ℕ} {a b : Fin n} (h : lev a = lev b) : rhoU lev a = rhoU lev b := by
  simp only [rhoU, h]

theorem kF_bracket {E1 E2 : Fin n → Fin n → Module.End ℂ V} (g1 : GlRel E1) (g2 : GlRel E2)
    (hc : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b) (p q : Fin n) :
    kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p = kF E1 E2 q q - kF E1 E2 p p := by
  have h1 := g1 q p p q
  have h2 := g2 q p p q
  simp only [if_true] at h1 h2
  have e : kF E1 E2 q p * kF E1 E2 p q - kF E1 E2 p q * kF E1 E2 q p =
      (E1 q p * E1 p q - E1 p q * E1 q p) + (E2 q p * E2 p q - E2 p q * E2 q p) := by
    simp only [kF, add_mul, mul_add, hc q p p q, hc p q q p]
    abel
  rw [e, h1, h2]
  simp only [kF]
  abel

theorem K_act {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hl : IsLev lam lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hA : AdmFor lam lev E1 E2) {x : V} (hx : x ∈ hwSp E1 E2 (muQ lam lev)) {p q : Fin n} (hpq : lev p = lev q) :
    kF E1 E2 p q x = if p = q then ((muQ lam lev p : ℝ) : ℂ) • x else 0 := by
  have hK : KHighest (fun _ => true) (kF E1 E2) (muQ lam lev) x := hx
  rcases lt_trichotomy p q with h | rfl | h
  · rw [if_neg h.ne, hK.2 p q h rfl]
  · rw [if_pos rfl, hK.1 p]
  · rw [if_neg h.ne']
    have hmu : muQ lam lev q = muQ lam lev p := by
      simp only [muQ, rhoU_eq hpq.symm, hl.2 q p hpq.symm]
    have hb := LinearMap.congr_fun (kF_bracket hA.gl1 hA.gl2 hA.comm p q) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hK.2 q p h rfl, map_zero, sub_zero, hK.1 q, hK.1 p, hmu,
      sub_self] at hb
    have hn : ⟪kF E1 E2 p q x, kF E1 E2 p q x⟫_ℂ = 0 := by
      rw [hA.unitK p q x, hb, inner_zero_right]
    exact inner_self_eq_zero.1 hn

theorem klChar : KlChar := by
  intro n lam lev hl V _ _ E1 E2 hA x hx p q hpq
  have hT : Ts E1 E2 true p q = kF E1 E2 p q := rfl
  simp only [lFq, LinearMap.add_apply]
  rw [liftq_topq, hT, K_act hl hA hx hpq, adLq_topq hpq]
  by_cases h : p = q
  · subst h
    rw [if_pos rfl, if_pos rfl, sum_diag hl.1, topq_smul, ← add_smul]
    push_cast
    rfl
  · rw [if_neg h, if_neg h, topq_zero, zero_add, Finset.sum_eq_zero, zero_smul]
    intro i _
    rw [adC_diag_ne h]
    simp

end GlobalTheory.CompanionTheory.PairMult.TopK
