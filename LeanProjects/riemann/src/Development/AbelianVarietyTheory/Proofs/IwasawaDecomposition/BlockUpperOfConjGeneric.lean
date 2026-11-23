import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperOfGenericCharacter

namespace GlobalTheory
namespace GenericCharBlockConj

open Matrix GlobalTheory.GenericCharBlock

variable {K : Type} [Field K]

theorem block_upper_of_conj_generic {A : Type} [CommGroup A] (r t : ℕ) (hr : 2 ≤ r)
    (hc : ∃ c : K, c ≠ 0 ∧ c ≠ 1) (b : GL (Fin (r + t)) K) (H : Subgroup (GL (Fin (r + t)) K))
    (χ : H →* A)
    (hU : ∀ g : GL (Fin (r + t)) K, (∀ i j : Fin (r + t), (r ≤ i.val → j.val < r → g.val i j = 0) ∧
      (i.val < r → j.val < i.val → g.val i j = 0) ∧ (i.val < r → i = j → g.val i j = 1)) →
        g ∈ H ∧ b * g * b⁻¹ ∈ H)
    (hgen : ∀ i j : Fin (r + t), i.val + 1 = j.val → j.val < r →
      ∃ (x : K) (h : H), h.val.val = b.val * Matrix.transvection i j x * b⁻¹.val ∧ χ h ≠ 1) :
    ∀ i j : Fin (r + t), r ≤ i.val → j.val < r → b.val i j = 0 := by
  obtain ⟨c, hc0, hc1⟩ := hc
  have hU' : ∀ g : GL (Fin (r + t)) K, (∀ a e : Fin (r + t), e.val < r → e.val ≤ a.val →
      g.val a e = (1 : Matrix (Fin (r + t)) (Fin (r + t)) K) a e) → g ∈ H ∧ b * g * b⁻¹ ∈ H := by
    intro g hg
    apply hU
    intro a e
    refine ⟨fun ha he => ?_, fun ha he => ?_, fun ha hae => ?_⟩
    · rw [hg a e he (by omega), one_apply_ne]
      intro h; subst h; omega
    · rw [hg a e (by omega) (by omega), one_apply_ne]
      intro h; subst h; omega
    · subst hae; rw [hg a a ha le_rfl, one_apply_eq]
  have hbi : b⁻¹.val * b.val = 1 := b.inv_mul
  have hib : b.val * b⁻¹.val = 1 := b.mul_inv
  have chiEq : ∀ g g' : H, g.val.val = g'.val.val → χ g = χ g' := by
    intro g g' h; congr 1; exact Subtype.ext (Units.ext h)
  have transv : ∀ i j : Fin (r + t), i.val + 1 = j.val → j.val < r →
      single i j (1 : K) * single i j 1 = 0 ∧
      ∀ y : K, ∀ a e : Fin (r + t), e.val < r → e.val ≤ a.val →
        (1 + y • single i j (1 : K)) a e = (1 : Matrix (Fin (r + t)) (Fin (r + t)) K) a e := by
    intro i j hij hj
    refine ⟨single_mul_single_of_ne (1 : K) i j i (fun h => by subst h; omega) 1,
      fun y a e he hea => ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, single_apply_of_ne, smul_zero, add_zero]
    rintro ⟨rfl, rfl⟩; omega

  have step1 : ∀ i j : Fin (r + t), i.val + 1 = j.val → j.val < r →
      ∀ k : Fin (r + t), r ≤ k.val → b.val k i = 0 := by
    intro i j hij hj k hk
    by_contra hbk
    have hji : j ≠ i := fun h => by subst h; omega
    obtain ⟨hEE, hEU⟩ := transv i j hij hj
    obtain ⟨x, g, hg, hχ⟩ := hgen i j hij hj
    obtain ⟨P, hPdef⟩ : ∃ P, P = b.val * single i j (1 : K) * b⁻¹.val := ⟨_, rfl⟩
    have hPP : P * P = 0 := by
      rw [hPdef, conj_mul_conj _ _ _ _ hbi, hEE, Matrix.mul_zero, Matrix.zero_mul]
    have hmem : ∀ y : K, ∃ g : GL (Fin (r + t)) K, g ∈ H ∧ g.val = 1 + y • P := by
      intro y
      refine ⟨b * unip _ hEE y * b⁻¹, (hU' _ (hEU y)).2, ?_⟩
      simp only [Units.val_mul, unip_val]
      rw [hPdef]; exact conj_one_add _ _ _ hib y
    obtain ⟨Q, hQdef⟩ : ∃ Q, Q = b.val * single i k (1 : K) := ⟨_, rfl⟩
    have hQQ : Q * Q = b.val k i • Q := by
      calc Q * Q = b.val * (single i k (1 : K) * b.val * single i k 1) := by
              simp only [hQdef, Matrix.mul_assoc]
        _ = b.val k i • Q := by
              rw [single_mul_mul_single, one_mul, mul_one, single_eq_smul, Matrix.mul_smul, hQdef]
    have hQP : Q * P = b.val k i • P := by
      calc Q * P = b.val * (single i k (1 : K) * b.val * single i j 1) * b⁻¹.val := by
              simp only [hQdef, hPdef, Matrix.mul_assoc]
        _ = b.val k i • P := by
              rw [single_mul_mul_single, one_mul, mul_one, single_eq_smul, Matrix.mul_smul,
                Matrix.smul_mul, hPdef]
    have hPQ : P * Q = 0 := by
      calc P * Q = b.val * single i j (1 : K) * (b⁻¹.val * b.val) * single i k 1 := by
              simp only [hQdef, hPdef, Matrix.mul_assoc]
        _ = 0 := by
              rw [hbi, Matrix.mul_one, Matrix.mul_assoc, single_mul_single_of_ne _ _ _ _ hji,
                Matrix.mul_zero]
    obtain ⟨μ, hμdef⟩ : ∃ μ : K, μ = (c - 1) / b.val k i := ⟨_, rfl⟩
    have hμc : 1 + μ * b.val k i = c := by rw [hμdef]; field_simp; ring
    have hμne : 1 + μ * b.val k i ≠ 0 := by rw [hμc]; exact hc0
    have hsH : rankOneUnit Q (b.val k i) μ hQQ hμne ∈ H := by
      refine (hU' _ (fun a e he hea => ?_)).1
      rw [rankOneUnit_val, Matrix.add_apply, Matrix.smul_apply, hQdef,
        mul_single_apply_of_ne _ _ _ _ _ (fun h => by subst h; omega), smul_zero, add_zero]
    have hsc : (rankOneUnit Q (b.val k i) μ hQQ hμne).val * P
        = c • (P * (rankOneUnit Q (b.val k i) μ hQQ hμne).val) := by
      rw [rankOneUnit_val, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hQP, Matrix.mul_add,
        Matrix.mul_one, Matrix.mul_smul, hPQ, smul_zero, add_zero, smul_smul, ← hμc, add_smul,
        one_smul]
    have hgx : g.val.val = 1 + x • P := by
      rw [hg, Matrix.transvection, single_eq_smul, conj_one_add _ _ _ hib, hPdef]
    exact hχ (chi_trivial_of_scaled H χ P hPP hmem _ hsH c hc1 hsc g.val g.prop x hgx)

  have step2 : ∀ i0 j0 : Fin (r + t), i0.val + 1 = j0.val → j0.val + 1 = r →
      ∀ k : Fin (r + t), r ≤ k.val → b.val k j0 = 0 := by
    intro i0 j0 hij hjr k hk
    by_contra hbk
    have hji : j0 ≠ i0 := fun h => by subst h; omega
    have hcol : ∀ a : Fin (r + t), r ≤ a.val → b.val a i0 = 0 :=
      fun a ha => step1 i0 j0 hij (by omega) a ha
    have hrow : ∀ e : Fin (r + t), e.val < j0.val → b.val k e = 0 := fun e he =>
      step1 e ⟨e.val + 1, by omega⟩ rfl (by show e.val + 1 < r; omega) k hk
    have hSb : ∀ a e, (single i0 k (1 : K) * b.val) a e = if a = i0 then b.val k e else 0 := by
      intro a e; by_cases ha : a = i0
      · subst ha; rw [single_mul_apply_same, one_mul, if_pos rfl]
      · rw [single_mul_apply_of_ne _ _ _ _ _ ha, if_neg ha]
    obtain ⟨hE0E0, hE0U⟩ := transv i0 j0 hij (by omega)

    obtain ⟨f, hfdef⟩ : ∃ f : Fin (r + t) → K, f = fun a => if a.val < r then 1 else c⁻¹ :=
      ⟨_, rfl⟩
    have hf0 : ∀ a, f a ≠ 0 := by
      intro a; rw [hfdef]; dsimp only
      split_ifs
      · exact one_ne_zero
      · exact inv_ne_zero hc0
    have hflow : ∀ a : Fin (r + t), a.val < r → f a = 1 := by
      intro a ha; rw [hfdef]; dsimp only; rw [if_pos ha]
    have hfhigh : ∀ a : Fin (r + t), r ≤ a.val → f a = c⁻¹ := by
      intro a ha; rw [hfdef]; dsimp only; rw [if_neg (by omega)]
    have hdU := hU' (diagUnit f hf0) (fun a e he hea => by
      rw [diagUnit_val]
      by_cases hae : a = e
      · subst hae; rw [diagonal_apply_eq, one_apply_eq, hflow a he]
      · rw [diagonal_apply_ne _ hae, one_apply_ne hae])

    obtain ⟨P2, hP2⟩ : ∃ P, P = b.val * single i0 k (1 : K) := ⟨_, rfl⟩
    have hP2e : ∀ a e, P2 a e = if e = k then b.val a i0 else 0 := by
      intro a e; rw [hP2]; by_cases he : e = k
      · subst he; rw [mul_single_apply_same, mul_one, if_pos rfl]
      · rw [mul_single_apply_of_ne _ _ _ _ _ he, if_neg he]
    have hP2P2 : P2 * P2 = 0 := by
      rw [hP2, Matrix.mul_assoc, ← Matrix.mul_assoc (single i0 k 1), single_mul_mul_single,
        hcol k hk]
      simp
    have hP2U : ∀ y : K, ∀ a e : Fin (r + t), e.val < r → e.val ≤ a.val →
        (1 + y • P2) a e = (1 : Matrix (Fin (r + t)) (Fin (r + t)) K) a e := by
      intro y a e he hea
      rw [Matrix.add_apply, Matrix.smul_apply, hP2e, if_neg (fun h => by subst h; omega), smul_zero, add_zero]
    have hmem2 : ∀ y : K, ∃ g : GL (Fin (r + t)) K, g ∈ H ∧ g.val = 1 + y • P2 :=
      fun y => ⟨unip P2 hP2P2 y, (hU' _ (hP2U y)).1, rfl⟩
    have hsc2 : (diagUnit f hf0).val * P2 = c • (P2 * (diagUnit f hf0).val) := by
      ext a e
      rw [diagUnit_val, Matrix.smul_apply, diagonal_mul, mul_diagonal, hP2e, smul_eq_mul]
      by_cases he : e = k
      · subst he
        try simp only [if_pos rfl, ite_true]
        rw [hfhigh e hk]
        by_cases ha : a.val < r
        · rw [hflow a ha]; field_simp
        · rw [hcol a (by omega)]; simp
      · rw [if_neg he]; simp

    obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin (r + t)) (Fin (r + t)) K,
        F = Matrix.of fun a e => if a = i0 ∧ r ≤ e.val then b.val k e else 0 := ⟨_, rfl⟩
    have hFe : ∀ a e, F a e = if a = i0 ∧ r ≤ e.val then b.val k e else 0 := by
      intro a e; rw [hF]; rfl
    have hFF : F * F = 0 := by
      ext a e
      rw [Matrix.mul_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro m _
      rw [hFe a m, hFe m e]
      by_cases hm : m = i0
      · rw [if_neg (fun h => by have := h.2; rw [hm] at this; omega), zero_mul]
      · rw [if_neg (show ¬ (m = i0 ∧ r ≤ e.val) from fun h => hm h.1), mul_zero]
    have hFU : ∀ y : K, ∀ a e : Fin (r + t), e.val < r → e.val ≤ a.val →
        (1 + y • F) a e = (1 : Matrix (Fin (r + t)) (Fin (r + t)) K) a e := by
      intro y a e he hea
      rw [Matrix.add_apply, Matrix.smul_apply, hFe, if_neg (fun h => by have := h.2; omega), smul_zero, add_zero]
    have hdF : diagonal f * F = c • (F * diagonal f) := by
      ext a e
      rw [Matrix.smul_apply, diagonal_mul, mul_diagonal, hFe, smul_eq_mul]
      by_cases h : a = i0 ∧ r ≤ e.val
      · rw [if_pos h, h.1, hflow i0 (by omega), hfhigh e h.2]; field_simp
      · rw [if_neg h]; simp
    have hP3 : (b.val * F * b⁻¹.val) * (b.val * F * b⁻¹.val) = 0 := by
      rw [conj_mul_conj _ _ _ _ hbi, hFF, Matrix.mul_zero, Matrix.zero_mul]
    have hmem3 : ∀ y : K, ∃ g : GL (Fin (r + t)) K, g ∈ H ∧ g.val = 1 + y • (b.val * F * b⁻¹.val) :=
      fun y => ⟨b * unip F hFF y * b⁻¹, (hU' _ (hFU y)).2, by
        simp only [Units.val_mul, unip_val]; exact conj_one_add _ _ _ hib y⟩
    have hsc3 : (b * diagUnit f hf0 * b⁻¹).val * (b.val * F * b⁻¹.val)
        = c • ((b.val * F * b⁻¹.val) * (b * diagUnit f hf0 * b⁻¹).val) := by
      simp only [Units.val_mul, diagUnit_val]
      rw [conj_mul_conj _ _ _ _ hbi, conj_mul_conj _ _ _ _ hbi, hdF, Matrix.mul_smul,
        Matrix.smul_mul]

    have hE0F : single i0 j0 (1 : K) * F = 0 := by
      ext a e
      rw [Matrix.zero_apply]
      by_cases ha : a = i0
      · subst ha; rw [single_mul_apply_same, hFe, if_neg (fun h => hji h.1), mul_zero]
      · rw [single_mul_apply_of_ne _ _ _ _ _ ha]
    have hprod : ∀ y : K, (1 + (y * b.val k j0) • single i0 j0 (1 : K)) * (1 + y • F)
        = 1 + y • (single i0 k (1 : K) * b.val) := by
      intro y
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, hE0F, smul_zero, smul_zero, add_zero]
      ext a e
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hSb, hFe, single_apply]
      by_cases ha : a = i0
      · subst ha
        by_cases he1 : r ≤ e.val
        · have : ¬ j0 = e := fun h => by subst h; omega
          simp [he1, this]
        · by_cases he2 : j0 = e
          · subst he2; simp [he1]
          · have : b.val k e = 0 := hrow e (by
              have : e.val ≠ j0.val := fun h => he2 (Fin.ext h).symm
              omega)
            simp [he1, he2, this]
      · have ha' : ¬ i0 = a := fun h => ha h.symm
        simp [ha, ha']
    have hrel : ∀ y : K, (unip P2 hP2P2 y).val
        = (b * unip _ hE0E0 (y * b.val k j0) * b⁻¹ * (b * unip F hFF y * b⁻¹)).val := by
      intro y
      simp only [Units.val_mul, unip_val]
      rw [conj_mul_conj _ _ _ _ hbi, hprod y, conj_one_add _ _ _ hib, hP2]
      simp only [Matrix.mul_assoc, hib, Matrix.mul_one]
    have hχE : ∀ y : K, χ ⟨b * unip _ hE0E0 y * b⁻¹, (hU' _ (hE0U y)).2⟩ = 1 := by
      intro y
      have hbk' : b.val k j0 ≠ 0 := hbk
      have h2 := chi_trivial_of_scaled H χ P2 hP2P2 hmem2 (diagUnit f hf0) hdU.1 c hc1 hsc2
        (unip P2 hP2P2 (y / b.val k j0)) (hU' _ (hP2U _)).1 (y / b.val k j0) rfl
      have h3 := chi_trivial_of_scaled H χ (b.val * F * b⁻¹.val) hP3 hmem3
        (b * diagUnit f hf0 * b⁻¹) hdU.2 c hc1 hsc3 (b * unip F hFF (y / b.val k j0) * b⁻¹)
        (hU' _ (hFU _)).2 (y / b.val k j0)
        (by simp only [Units.val_mul, unip_val]; exact conj_one_add _ _ _ hib _)
      have hmul : (⟨unip P2 hP2P2 (y / b.val k j0), (hU' _ (hP2U _)).1⟩ : H)
          = ⟨b * unip _ hE0E0 (y / b.val k j0 * b.val k j0) * b⁻¹, (hU' _ (hE0U _)).2⟩
            * ⟨b * unip F hFF (y / b.val k j0) * b⁻¹, (hU' _ (hFU _)).2⟩ :=
        Subtype.ext (Units.ext (hrel _))
      rw [hmul, map_mul, h3, mul_one] at h2
      have hy : y / b.val k j0 * b.val k j0 = y := by field_simp
      rw [← h2]
      apply chiEq
      show (b * unip _ hE0E0 y * b⁻¹).val = (b * unip _ hE0E0 (y / b.val k j0 * b.val k j0) * b⁻¹).val
      rw [hy]
    obtain ⟨x, g, hg, hχ⟩ := hgen i0 j0 hij (by omega)
    apply hχ
    rw [← hχE x]
    apply chiEq
    rw [hg]
    show b.val * Matrix.transvection i0 j0 x * b⁻¹.val = (b * unip _ hE0E0 x * b⁻¹).val
    simp only [Units.val_mul, unip_val]
    rw [Matrix.transvection, single_eq_smul]
  intro i j hi hj
  by_cases h : j.val + 1 < r
  · exact step1 j ⟨j.val + 1, by omega⟩ rfl h i hi
  · exact step2 ⟨j.val - 1, by omega⟩ j (by show j.val - 1 + 1 = j.val; omega) (by omega) i hi

end GenericCharBlockConj
end GlobalTheory
