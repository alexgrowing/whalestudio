import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma inter_inr_card {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (_i : DecidableEq (β ⊕ₗ κ))
    (b : Finset β) (L : Finset κ) :
    (uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = L.card := by
  have h : uni b L ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding =
      L.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
    ext t
    obtain ⟨t, rfl⟩ := toLex.surjective t
    rcases t with i | l <;> simp [uni, inrE]
  rw [h, Finset.card_map]

private lemma inl_not_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (i : β) :
    (inlE i : β ⊕ₗ κ) ∉ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp [inlE, inrE]

private lemma inr_mem {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ] (l : κ) :
    (inrE l : β ⊕ₗ κ) ∈ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding := by
  simp

theorem UpperTheory.Gal.productCup_of_system.localOne_of_gl1 :
    FiltrationBoundaryCriterion → ColQEx → WdUni → L1 := by
  intro hG hC hU β κ E _ _ _ _ _ _ A w d n hW hK c hc hd hB
  have e : ∀ s : Finset (β ⊕ₗ κ), uni (lft s) (rgt s) = s := (hU β κ E w c ∅ ∅).2.2.2.2
  have eL : ∀ (b : Finset β) (L : Finset κ), lft (uni b L) = b := fun b L => (hU β κ E w c b L).2.1
  have eR : ∀ (b : Finset β) (L : Finset κ), rgt (uni b L) = L := fun b L => (hU β κ E w c b L).2.2.1
  have eC : ∀ s : Finset (β ⊕ₗ κ), s.card = (lft s).card + (rgt s).card := fun s => by
    have := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rwa [e s] at this
  have hS : ∀ (_i : DecidableEq (β ⊕ₗ κ)) (s : Finset (β ⊕ₗ κ)),
      (s ∩ Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding).card = (rgt s).card := fun i s => by
    have := inter_inr_card i (lft s) (rgt s)
    rwa [e s] at this
  have hy : ∀ b : Finset β, (b.card : ℤ) = n - d →
      ∃ y ∈ (colA A w b).C (d - 1), (colA A w b).D y = col c b := fun b hb => by
    obtain ⟨y, hy, h⟩ := hB b hb
    exact ⟨y, hy, h⟩
  let yb : Finset β → Finset κ → E := fun b => if h : (b.card : ℤ) = n - d then (hy b h).choose else 0
  have hyb : ∀ b, (b.card : ℤ) = n - d → yb b ∈ (colA A w b).C (d - 1) ∧ (colA A w b).D (yb b) = col c b := by
    intro b hb
    simp only [yb, dif_pos hb]
    exact (hy b hb).choose_spec
  have hy0 : ∀ b, ¬ (b.card : ℤ) = n - d → yb b = 0 := by
    intro b hb
    simp only [yb, dif_neg hb]
  let y : Finset (β ⊕ₗ κ) → E := fun s => ((-1 : ℤ) ^ (lft s).card) • yb (lft s) (rgt s)
  have hmem : ∀ b, (b.card : ℤ) = n - d → ∀ L, yb b L ∈ (if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := by
    intro b hb L
    have h : yb b ∈ Submodule.pi Set.univ
      (fun L : Finset κ => if (L.card : ℤ) = d - 1 then A (uni b L) else ⊥) := (hyb b hb).1
    exact (Submodule.mem_pi.1 h) L (Set.mem_univ _)
  have hz : ∀ s, ¬ (((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1) → y s = 0 := by
    intro s hs
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have hL : ¬ ((rgt s).card : ℤ) = d - 1 := fun h => hs ⟨hb, h⟩
      have h1 := hmem _ hb (rgt s)
      rw [if_neg hL, Submodule.mem_bot] at h1
      simp only [y, h1, smul_zero]
    · simp only [y, hy0 _ hb, Pi.zero_apply, smul_zero]
  have hcC : ∀ s : Finset (β ⊕ₗ κ), ¬ (s.card : ℤ) = n → c s = 0 := by
    intro s hs
    have h : c ∈ Submodule.pi Set.univ
      (fun s : Finset (β ⊕ₗ κ) => if (s.card : ℤ) = n then A s else ⊥) := hc.1
    have h1 := (Submodule.mem_pi.1 h) s (Set.mem_univ _)
    rwa [if_neg hs, Submodule.mem_bot] at h1
  refine hG (β ⊕ₗ κ) E A w (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) d n hW
    (hC β κ E A w d hK) c hc ?_ ⟨y, ?_, ?_, ?_⟩
  · intro s hs
    have hs' : d < ((rgt s).card : ℤ) := by
      rw [hS _ s] at hs
      exact not_le.1 hs
    have := hd (lft s) (rgt s) hs'
    rwa [e s] at this
  · refine Submodule.mem_pi.2 fun s _ => ?_
    by_cases h : ((lft s).card : ℤ) = n - d ∧ ((rgt s).card : ℤ) = d - 1
    · have hcard : (s.card : ℤ) = n - 1 := by
        rw [eC s]; push_cast; omega
      have h1 := hmem _ h.1 (rgt s)
      rw [if_pos h.2, e s] at h1
      show y s ∈ (if (s.card : ℤ) = n - 1 then A s else ⊥)
      rw [if_pos hcard]
      exact zsmul_mem h1 _
    · rw [hz s h]
      exact zero_mem _
  · intro s hs
    rw [hS _ s] at hs
    exact hz s fun h => hs h.2
  · intro s hs
    rw [hS _ s] at hs
    conv_lhs => rw [← e s]
    rw [(hU β κ E _ y (lft s) (rgt s)).1]
    have h0 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun i : β => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inlE i)) = fun _ => 0 := by
      intro _i
      funext i
      simp only [wOn, if_neg (inl_not_mem i)]
    have h1 : ∀ _i : DecidableEq (β ⊕ₗ κ),
        (fun l : κ => wOn (Finset.univ.map (inrE : κ ↪o β ⊕ₗ κ).toEmbedding) w (inrE l)) = fun l => w (inrE l) := by
      intro _i
      funext l
      simp only [wOn, if_pos (inr_mem l)]
    have h2 : (fun L' : Finset κ => y (uni (lft s) L')) = ((-1 : ℤ) ^ (lft s).card) • yb (lft s) := by
      funext L'
      simp only [y, eL, eR, Pi.smul_apply]
    have h3 : wd (fun _ : β => (0 : Module.End ℂ E)) (fun b' => y (uni b' (rgt s))) (lft s) = 0 := by
      simp [wd]
    rw [h0 _, h1 _, h3, zero_add, h2, map_zsmul, Pi.smul_apply, smul_smul, ← mul_pow]
    by_cases hb : ((lft s).card : ℤ) = n - d
    · have h4 := congrFun (hyb _ hb).2 (rgt s)
      have h5 : wd (fun l : κ => w (inrE l)) (yb (lft s)) (rgt s) = c s := by
        have : col c (lft s) (rgt s) = c s := by
          show c (uni (lft s) (rgt s)) = c s
          rw [e s]
        rw [← this]
        exact h4
      rw [h5]
      simp
    · rw [hy0 _ hb, hcC s (by rw [eC s]; push_cast; omega)]
      simp
