import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.SubquotientExact

variable {κ : Type} [LinearOrder κ] {d : ℕ}

private def eps (e : Fin d ↪o κ) (b : Finset κ) (j : Fin d) : ℤ := (-1) ^ (b.filter (· < e j)).card

private def psi (e : Fin d ↪o κ) (b : Finset κ) (L : Finset (Fin d)) : ℤ := ∏ j ∈ L, eps e b j

private def emb (e : Fin d ↪o κ) (b : Finset κ) (L : Finset (Fin d)) : Finset κ := b ∪ L.map e.toEmbedding

private def pre (e : Fin d ↪o κ) (s : Finset κ) : Finset (Fin d) := Finset.univ.filter fun j => e j ∈ s

private lemma eps_sq (e : Fin d ↪o κ) (b : Finset κ) (j : Fin d) : eps e b j * eps e b j = 1 := by
  simp [eps, ← mul_pow]

private lemma psi_sq (e : Fin d ↪o κ) (b : Finset κ) (L : Finset (Fin d)) : psi e b L * psi e b L = 1 := by
  rw [psi, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => eps_sq e b j

private lemma psi_erase (e : Fin d ↪o κ) (b : Finset κ) {L : Finset (Fin d)} {j : Fin d} (h : j ∈ L) :
    psi e b L = eps e b j * psi e b (L.erase j) :=
  (Finset.mul_prod_erase L _ h).symm

private lemma mem_img (e : Fin d ↪o κ) (x : κ) : x ∈ img e ↔ ∃ j, e j = x := by
  simp [img]

private lemma disj (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    Disjoint b (L.map e.toEmbedding) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hx'
  exact hb j hx

private lemma sign_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) (j : Fin d) :
    GlobalTheory.cubeSign (emb e b L) (e j) = eps e b j * GlobalTheory.cubeSign L j := by
  have h1 : (emb e b L).filter (· < e j) = b.filter (· < e j) ∪ (L.filter (· < j)).map e.toEmbedding := by
    ext x
    simp only [emb, Finset.mem_filter, Finset.mem_union, Finset.mem_map]
    constructor
    · rintro ⟨h | ⟨i, hi, rfl⟩, hlt⟩
      · exact Or.inl ⟨h, hlt⟩
      · exact Or.inr ⟨i, ⟨hi, e.lt_iff_lt.1 hlt⟩, rfl⟩
    · rintro (⟨h, hlt⟩ | ⟨i, ⟨hi, hlt⟩, rfl⟩)
      · exact ⟨Or.inl h, hlt⟩
      · exact ⟨Or.inr ⟨i, hi, rfl⟩, e.lt_iff_lt.2 hlt⟩
  have h2 : Disjoint (b.filter (· < e j)) ((L.filter (· < j)).map e.toEmbedding) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (disj e hb _)
  rw [GlobalTheory.cubeSign, h1, Finset.card_union_of_disjoint h2, Finset.card_map, pow_add, eps, GlobalTheory.cubeSign]

private lemma erase_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) (j : Fin d) :
    (emb e b L).erase (e j) = emb e b (L.erase j) := by
  ext x
  simp only [emb, Finset.mem_erase, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro ⟨hne, h | ⟨i, hi, rfl⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, ⟨fun h => hne (by simp [h]), hi⟩, rfl⟩
  · rintro (h | ⟨i, ⟨hne, hi⟩, rfl⟩)
    · exact ⟨fun h' => hb j (h' ▸ h), Or.inl h⟩
    · exact ⟨fun h => hne (e.injective h), Or.inr ⟨i, hi, rfl⟩⟩

private lemma wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (w : ι → Module.End ℂ E)
    (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma key {E : Type} [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E) (e : Fin d ↪o κ)
    {b : Finset κ} (hb : ∀ j, e j ∉ b) (f : Finset κ → E) (L : Finset (Fin d)) :
    wd (fun j => w (e j)) (fun L' => psi e b L' • f (emb e b L')) L =
      psi e b L • wd (wOn (img e) w) f (emb e b L) := by
  have hz : ∑ i ∈ b, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (img e) w i (f ((emb e b L).erase i)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have : i ∉ img e := by
      rw [mem_img]
      rintro ⟨j, rfl⟩
      exact hb j hi
    simp [wOn, this]
  rw [wd_apply', wd_apply']
  conv_rhs => rw [show ∑ i ∈ emb e b L, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (img e) w i (f ((emb e b L).erase i)) =
      ∑ i ∈ b, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (img e) w i (f ((emb e b L).erase i)) +
      ∑ i ∈ L.map e.toEmbedding, (GlobalTheory.cubeSign (emb e b L) i : ℤ) • wOn (img e) w i (f ((emb e b L).erase i)) from
        Finset.sum_union (disj e hb L)]
  rw [hz, zero_add, Finset.sum_map, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hm : e j ∈ img e := (mem_img e _).2 ⟨j, rfl⟩
  simp only [RelEmbedding.coe_toEmbedding, wOn, hm, if_true]
  rw [sign_emb e hb, erase_emb e hb, map_zsmul, smul_smul, smul_smul, psi_erase e b hj]
  congr 1
  have := eps_sq e b j
  linear_combination (-(psi e b (L.erase j) * GlobalTheory.cubeSign L j)) * this

private lemma emb_pre (e : Fin d ↪o κ) (s : Finset κ) : emb e (s \ img e) (pre e s) = s := by
  ext x
  simp only [emb, pre, Finset.mem_union, Finset.mem_sdiff, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_img, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact h.1
    · exact hj
  · intro h
    by_cases hx : ∃ j, e j = x
    · obtain ⟨j, rfl⟩ := hx
      exact Or.inr ⟨j, h, rfl⟩
    · exact Or.inl ⟨h, hx⟩

private lemma sdiff_ok (e : Fin d ↪o κ) (s : Finset κ) (j : Fin d) : e j ∉ s \ img e := by
  simp [mem_img]

private lemma sdiff_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    emb e b L \ img e = b := by
  ext x
  simp only [emb, Finset.mem_sdiff, Finset.mem_union, Finset.mem_map, mem_img, RelEmbedding.coe_toEmbedding]
  constructor
  · rintro ⟨h | ⟨j, _, rfl⟩, hn⟩
    · exact h
    · exact absurd ⟨j, rfl⟩ hn
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro ⟨j, rfl⟩
    exact hb j h

private lemma pre_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    pre e (emb e b L) = L := by
  ext j
  simp only [emb, pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  constructor
  · rintro (h | ⟨i, hi, h⟩)
    · exact absurd h (hb j)
    · exact e.injective h ▸ hi
  · exact fun h => Or.inr ⟨j, h, rfl⟩

private lemma card_emb (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    (emb e b L).card = b.card + L.card := by
  rw [emb, Finset.card_union_of_disjoint (disj e hb L), Finset.card_map]

private lemma card_inter (e : Fin d ↪o κ) {b : Finset κ} (hb : ∀ j, e j ∉ b) (L : Finset (Fin d)) :
    (emb e b L ∩ img e).card = L.card := by
  have : emb e b L ∩ img e = L.map e.toEmbedding := by
    ext x
    simp only [emb, Finset.mem_inter, Finset.mem_union, Finset.mem_map, mem_img, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨h | h, ⟨j, rfl⟩⟩
      · exact absurd h (hb j)
      · exact h
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Or.inr ⟨j, hj, rfl⟩, j, rfl⟩
  rw [this, Finset.card_map]

private lemma mem_C {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (A : Finset ι → Submodule ℂ E)
    (w : ι → Module.End ℂ E) (n : ℤ) (c : Finset ι → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) := by
  simp [acx, Submodule.mem_pi]

end UpperTheory.Gal.productCup_of_system.SubquotientExact

open UpperTheory.Gal.productCup_of_system.SubquotientExact in
theorem UpperTheory.Gal.productCup_of_system.subQEx_of :
    RS → WdBasic → SubQEx := by
  intro _ _ S E _ _ _ _ act κ _ _ M r d e hK n m hm c hc hL hz
  have hcs : ∀ s, (s.card : ℤ) ≠ n → c s = 0 := fun s hs => by
    have := (mem_C _ _ _ _).1 hc s
    simpa [hs] using this
  have hcM : ∀ s, c s ∈ M := fun s => by
    have := (mem_C _ _ _ _).1 hc s
    split_ifs at this with h
    · exact this
    · rw [(Submodule.mem_bot ℂ).1 this]; exact M.zero_mem

  have hex : ∀ b : Finset κ, ∃ Y ∈ (kos act M fun j => r (e j)).C (m - 1), (∀ j, e j ∉ b) →
      wd (fun j => act (r (e j))) Y = fun L => psi e b L • c (emb e b L) := by
    intro b
    by_cases hb : ∀ j, e j ∉ b
    · have hcol : (fun L => psi e b L • c (emb e b L)) ∈ (kos act M fun j => r (e j)).Z m := by
        refine ⟨(mem_C _ _ _ _).2 fun L => ?_, ?_⟩
        · by_cases hLm : (L.card : ℤ) = m
          · simp only [hLm, if_true]
            exact zsmul_mem (hcM _) _
          · have : c (emb e b L) = 0 := hL _ (by rwa [card_inter e hb])
            simp [this]
        · have : wd (fun j => act (r (e j))) (fun L => psi e b L • c (emb e b L)) = 0 := by
            funext L
            rw [key (fun l => act (r l)) e hb c L, hz]
            simp
          exact this
      obtain ⟨Y, hY, hYd⟩ := hK m hm hcol
      exact ⟨Y, hY, fun _ => hYd⟩
    · exact ⟨0, Submodule.zero_mem _, fun h => absurd h hb⟩
  choose Y hYC hYd using hex
  have hYz : ∀ b L, (L.card : ℤ) ≠ m - 1 → Y b L = 0 := fun b L hLm => by
    have := (mem_C _ _ _ _).1 (hYC b) L
    simpa [hLm] using this
  have hYM : ∀ b L, Y b L ∈ M := fun b L => by
    have := (mem_C _ _ _ _).1 (hYC b) L
    split_ifs at this with h
    · exact this
    · rw [(Submodule.mem_bot ℂ).1 this]; exact M.zero_mem
  let y : Finset κ → E := fun s =>
    if ((s \ img e).card : ℤ) = n - m then psi e (s \ img e) (pre e s) • Y (s \ img e) (pre e s) else 0
  have hy : ∀ b (hb : ∀ j, e j ∉ b) L, y (emb e b L) = if (b.card : ℤ) = n - m then psi e b L • Y b L else 0 := by
    intro b hb L
    simp only [y, sdiff_emb e hb, pre_emb e hb]
  refine ⟨y, (mem_C _ _ _ _).2 fun s => ?_, fun s hs => ?_, ?_⟩
  · rw [← emb_pre e s]
    have hb := sdiff_ok e s
    rw [hy _ hb, card_emb e hb]
    split_ifs with h1 h2 h2
    · exact zsmul_mem (hYM _ _) _
    · exact M.zero_mem
    · have : ((pre e s).card : ℤ) ≠ m - 1 := by
        intro h; apply h1; push_cast; omega
      simp [hYz _ _ this]
    · exact Submodule.zero_mem _
  · rw [← emb_pre e s] at hs ⊢
    have hb := sdiff_ok e s
    rw [card_inter e hb] at hs
    rw [hy _ hb, hYz _ _ hs]
    simp
  · funext s
    obtain ⟨b, L, hb, rfl⟩ : ∃ b L, (∀ j, e j ∉ b) ∧ s = emb e b L :=
      ⟨_, _, sdiff_ok e s, (emb_pre e s).symm⟩
    have hk : wd (fun j => act (r (e j))) (fun L' => psi e b L' • y (emb e b L')) L =
        psi e b L • wd (wOn (img e) fun l => act (r l)) y (emb e b L) := key (fun l => act (r l)) e hb y L
    have hcancel : ∀ (L' : Finset (Fin d)) (v : E), psi e b L' • psi e b L' • v = v := fun L' v => by
      rw [smul_smul, psi_sq, one_smul]
    by_cases hn : (b.card : ℤ) = n - m
    · have h1 : (fun L' => psi e b L' • y (emb e b L')) = Y b := by
        funext L'
        rw [hy b hb, if_pos hn, hcancel]
      rw [h1, hYd b hb] at hk
      calc wd (wOn (img e) fun l => act (r l)) y (emb e b L)
          = psi e b L • psi e b L • wd (wOn (img e) fun l => act (r l)) y (emb e b L) := (hcancel _ _).symm
        _ = psi e b L • psi e b L • c (emb e b L) := by rw [← hk]
        _ = c (emb e b L) := hcancel _ _
    · have h1 : (fun L' => psi e b L' • y (emb e b L')) = 0 := by
        funext L'
        rw [hy b hb, if_neg hn]
        simp
      rw [h1, map_zero] at hk
      have h2 : wd (wOn (img e) fun l => act (r l)) y (emb e b L) = 0 := by
        rw [← hcancel L (wd (wOn (img e) fun l => act (r l)) y (emb e b L)), ← hk]
        simp
      rw [h2]
      by_cases hcard : ((emb e b L).card : ℤ) = n
      · have hLm : ¬ (((emb e b L) ∩ img e).card : ℤ) = m := by
          rw [card_inter e hb]
          rw [card_emb e hb] at hcard
          intro h
          apply hn
          push_cast at hcard
          omega
        exact (hL _ hLm).symm
      · exact (hcs _ hcard).symm
