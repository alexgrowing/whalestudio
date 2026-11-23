import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto

theorem exists_invol {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → Eˣ),
      (∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum → σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a) ∧
      (∀ a b, a < (bs.map (fun b => (b.2 : ℕ))).sum → b < (bs.map (fun b => (b.2 : ℕ))).sum →
        ptEntryL bs a b = if b = σ a then (t a : E) else 0) ∧
      (∀ c, c + 1 < (bs.map (fun b => (b.2 : ℕ))).sum →
        (σ c = σ (c + 1) + 1 ∧ t (c + 1) = t c) ∨ σ c < σ (c + 1)) := by
  induction bs with
  | nil => exact ⟨id, 1, by simp, by simp, by simp⟩
  | cons p bs ih =>
    obtain ⟨u, s⟩ := p
    obtain ⟨σ, t, h1, h2, h3⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = m at h1 h2 h3 ⊢
    refine ⟨fun a => if a < s then s - 1 - a else s + σ (a - s),
      fun a => if a < s then u else t (a - s), fun a ha => ?_, fun a b ha hb => ?_, fun c hc => ?_⟩
    · by_cases h : a < s
      · have h' : (s : ℕ) - 1 - a < s := by omega
        simp only [if_pos h, if_pos h']
        omega
      · obtain ⟨h4, h5⟩ := h1 (a - s) (by omega)
        have h' : ¬ (s : ℕ) + σ (a - s) < s := by omega
        simp only [if_neg h, if_neg h', Nat.add_sub_cancel_left, h5]
        omega
    · simp only [ptEntryL]
      by_cases h : a < s
      · simp only [if_pos h]
        by_cases h' : b < s
        · rw [if_pos ⟨h, h'⟩]
          exact if_congr (by omega) rfl rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · simp only [if_neg h]
        rw [if_neg (by omega)]
        by_cases h' : b < s
        · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_pos (by omega), h2 _ _ (by omega) (by omega)]
          exact if_congr (by omega) rfl rfl
    · by_cases h : c + 1 < s
      · have h' : c < s := by omega
        simp only [if_pos h, if_pos h']
        exact Or.inl ⟨by omega, trivial⟩
      · by_cases h' : c < s
        · simp only [if_neg h, if_pos h']
          exact Or.inr (by omega)
        · simp only [if_neg h, if_neg h']
          have e : c + 1 - s = c - s + 1 := by omega
          rw [e]
          rcases h3 (c - s) (by omega) with ⟨h4, h5⟩ | h4
          · exact Or.inl ⟨by omega, h5⟩
          · exact Or.inr (by omega)

theorem simple_sum {E : Type} [CommRing E] {r : ℕ} (w : Pt E (r + 1))
    (Z A C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ (r - (b : ℕ)))
    (hA : ∀ i j, i < j → A i j = 0) (hC : ∀ i j, j < i → C i j = 0)
    (h : ∀ a b, ∑ i, A a i * Z i b = ∑ i, Z a i * C i b) :
    ∑ j : Fin r, A j.succ j.castSucc = -∑ j : Fin r, C j.castSucc j.succ := by
  obtain ⟨σ₀, t, h1, h2, h3⟩ := exists_invol w.blocks
  rw [w.size] at h1 h2 h3
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ₀ a, (h1 a a.2).1⟩
  have hinv : Function.Involutive σ' := fun a => Fin.ext (h1 a a.2).2
  let σ : Fin (r + 1) ≃ Fin (r + 1) := hinv.toPerm
  have hσ : ∀ a, (σ a : ℕ) = σ₀ a := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := hinv
  let z : Fin (r + 1) → Eˣ := fun a => t a * (-1) ^ (r - (σ a : ℕ))
  have hZ' : ∀ a b, Z a b = if b = σ a then (z a : E) else 0 := by
    intro a b
    rw [hZ, Pt.mat, h2 _ _ a.2 b.2]
    by_cases hb : b = σ a
    · rw [if_pos hb, if_pos (by rw [hb, hσ]), hb]; simp [z]
    · rw [if_neg hb, if_neg (fun e : (b : ℕ) = σ₀ a => hb (Fin.ext e)), zero_mul]
  have key : ∀ a c, A a c * z c = z a * C (σ a) (σ c) := by
    intro a c
    have := h a (σ c)
    simpa [hZ'] using this
  have term : ∀ a c : Fin (r + 1), (if (a : ℕ) = c + 1 then A a c else 0) =
      -(if (σ c : ℕ) = σ a + 1 then C (σ a) (σ c) else 0) := by
    intro a c
    by_cases hac : (a : ℕ) = c + 1
    · rw [if_pos hac]
      rcases h3 c (hac ▸ a.2) with ⟨h4, h5⟩ | h4
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [← hac] at h5
        rw [if_pos h4]
        have hz : z a = -z c := by
          have := (σ c).2
          have e : r - (σ a : ℕ) = r - (σ c : ℕ) + 1 := by omega
          simp only [z, e, h5, pow_succ]
          simp
        have := key a c
        rw [hz, Units.val_neg, mul_comm, neg_mul, ← mul_neg] at this
        exact (Units.mul_right_inj _).1 this
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [if_neg (by omega), neg_zero]
        have := key a c
        rw [hC _ _ h4, mul_zero] at this
        exact (Units.mul_left_eq_zero _).1 this
    · rw [if_neg hac]
      by_cases h4 : (σ c : ℕ) = σ a + 1
      · rw [if_pos h4]
        have h5 := h3 (σ a) (h4 ▸ (σ c).2)
        rw [← h4, ← hσ, ← hσ, hσσ, hσσ] at h5
        have h6 : a < c := by
          rcases h5 with ⟨h5, -⟩ | h5
          · exact absurd h5 hac
          · exact h5
        have := key a c
        rw [hA _ _ h6, zero_mul] at this
        rw [(Units.mul_right_eq_zero _).1 this.symm, neg_zero]
      · rw [if_neg h4, neg_zero]
  have hs : ∀ M : Fin (r + 1) → Fin (r + 1) → E,
      ∑ a : Fin (r + 1), ∑ c : Fin (r + 1), (if (a : ℕ) = c + 1 then M a c else 0) =
        ∑ j : Fin r, M j.succ j.castSucc := by
    intro M
    rw [Fin.sum_univ_succ]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun (c : Fin (r + 1)) _ =>
      if_neg (show ¬ ((0 : Fin (r + 1)) : ℕ) = c + 1 by simp)), zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j.castSucc]
    · simp
    · intro b _ hb
      exact if_neg fun e => hb (Fin.ext (Nat.add_right_cancel e).symm)
    · simp
  rw [← hs A, ← hs (fun a c => C c a)]
  simp only [term, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm, ← σ.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← σ.sum_comp]
  simp only [hσσ]

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem hf_sum_l {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm (∑ i, c i • v i) y = ∑ i, c i * hf L S.Hm (v i) y := by
  classical
  refine Finset.induction_on Finset.univ (by simp [hf]) fun i s hi ih => ?_
  rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, hf_smul_l, ih]

theorem hf_sum_r {ι : Type} [Fintype ι] (c : ι → E) (v : ι → S.V) (y : S.V) :
    hf L S.Hm y (∑ i, c i • v i) = ∑ i, L.cj (c i) * hf L S.Hm y (v i) := by
  rw [← hf_cj L S.herm.1, hf_sum_l, map_sum]
  simp only [map_mul, hf_cj L S.herm.1]

theorem coef_eq (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
    (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) (n : S.GLV)
    (s : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hs : ∀ j, n (g j) = ∑ i, s i j • g i) (j : Fin r) :
    S.coef g gs n j = s j.castSucc j.succ := by
  simp [Frames.coef, Frames.h, hs, hf_sum_l, dual]

end

theorem psi_eq_psi' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.St, S.psi h = S.psi' h := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh
  obtain ⟨s, ⟨hs0, -⟩, hs⟩ := exists_matrix S S.f S.T S.gram h hh.1
  obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := exists_matrix S S.f' S.T' S.gram' h hh.2
  obtain ⟨C, ⟨hC0, hC1⟩, hC⟩ := exists_matrix S S.f' S.T' S.gram' h⁻¹ (inv_mem hh.2)
  have hiso : ∀ x y, hf L S.Hm (h x) (h y) = hf L S.Hm x y := hh.1.1.1
  have hcan : ∀ x, h (h⁻¹ x) = x := fun x => h.apply_symm_apply x
  have hneg : ∀ j : Fin r, s' j.castSucc j.succ = -C j.castSucc j.succ := by
    intro j
    have e : hf L S.Hm (h (h⁻¹ (S.f' j.succ))) (S.es' j) = 0 := by
      rw [hcan, S.dual', if_neg (Fin.castSucc_lt_succ (i := j)).ne']
    rw [hC, map_sum] at e
    simp only [map_smul, hf_sum_l] at e
    simp only [hs', hf_sum_l, S.dual', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at e
    rw [Finset.sum_eq_add j.castSucc j.succ (Fin.castSucc_lt_succ (i := j)).ne, hs1', hC1] at e
    · linear_combination e
    · rintro i - ⟨h1, h2⟩
      by_cases hi : i < j.castSucc
      · rw [hs0' _ _ hi, mul_zero]
      · rw [hC0, zero_mul]
        have h1' : (i : ℕ) ≠ j := fun e => h1 (Fin.ext e)
        have h2' : (i : ℕ) ≠ j + 1 := fun e => h2 (Fin.ext e)
        have h3' : ¬ (i : ℕ) < j := hi
        change (j : ℕ) + 1 < i
        omega
    · simp
    · simp
  have main := simple_sum S.w S.Zh (cT L s) C S.relevant
    (fun i j hij => by rw [cT, hs0 _ _ hij, map_zero]) hC0 (fun a b => by
      have e := hiso (h⁻¹ (S.f' b)) (S.f a)
      rw [hcan, hs, hC, hf_sum_l, hf_sum_r] at e
      simpa [cT, Frames.Zh, Frames.h, mul_comm] using e)
  have e : ∑ j, S.coef S.f' S.es' h j = L.cj (∑ j, S.coef S.f S.es h j) := by
    simp only [coef_eq S _ _ S.dual h s hs, coef_eq S _ _ S.dual' h s' hs', hneg, map_sum,
      Finset.sum_neg_distrib]
    exact main.symm
  simp only [Frames.psi, Frames.psi', Frames.psiOf]
  rw [e, ← L.local_additive_char_conj, map_mul, AlgEquiv.commutes]

end GlobalTheory.HL.CharAgree
