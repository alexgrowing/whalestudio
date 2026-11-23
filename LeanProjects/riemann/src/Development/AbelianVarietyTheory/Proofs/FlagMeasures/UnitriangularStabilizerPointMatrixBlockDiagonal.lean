import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

namespace GlobalTheory.PointStab

open Formalism.MainNotions.S

theorem ptEntry_monomial {K : Type} [Field K] (bs : List (K × ℕ)) (hbs : ∀ b ∈ bs, b.1 ≠ 0) :
    ∃ (σ : ℕ → ℕ) (t : ℕ → K), ∀ a, a < (bs.map Prod.snd).sum →
      σ a < (bs.map Prod.snd).sum ∧ σ (σ a) = a ∧
      Formalism.L2.SG.RealObj.blkOf bs (σ a) = Formalism.L2.SG.RealObj.blkOf bs a ∧ t a ≠ 0 ∧
      ∀ b, b < (bs.map Prod.snd).sum →
        (a ≤ b → Formalism.L2.SG.RealObj.blkOf bs a ≤ Formalism.L2.SG.RealObj.blkOf bs b) ∧
        (Formalism.L2.SG.RealObj.blkOf bs a = Formalism.L2.SG.RealObj.blkOf bs b → a + σ a = b + σ b) ∧
        ptEntry bs a b = if b = σ a then t a else 0 := by
  induction bs with
  | nil => exact ⟨id, fun _ => 1, fun a ha => by simp at ha⟩
  | cons x bs ih =>
    obtain ⟨t0, m⟩ := x
    have ht0 : t0 ≠ 0 := hbs _ (List.mem_cons_self ..)
    obtain ⟨σ, t, h⟩ := ih (fun b hb => hbs b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map Prod.snd).sum = N at h ⊢
    refine ⟨fun a => if a < m then m - 1 - a else σ (a - m) + m,
      fun a => if a < m then t0 else t (a - m), fun a ha => ?_⟩
    simp only [Formalism.L2.SG.RealObj.blkOf, ptEntry]
    by_cases h1 : a < m
    · have h2 : m - 1 - a < m := by omega
      simp only [h1, h2, if_true]
      refine ⟨by omega, by omega, trivial, ht0, fun b hb => ?_⟩
      by_cases h3 : b < m
      · simp only [h3, if_true, and_self]
        refine ⟨fun _ => le_refl _, fun _ => by omega, ?_⟩
        have : a + b + 1 = m ↔ b = m - 1 - a := by omega
        simp [this]
      · have h4 : ¬ m ≤ a := by omega
        have h5 : ¬ b = m - 1 - a := by omega
        simp [h3, h4, h5]
    · obtain ⟨e1, e2, e3, e0, e4⟩ := h (a - m) (by omega)
      have h2 : ¬ σ (a - m) + m < m := by omega
      have h4 : m ≤ a := by omega
      simp only [h1, h2, if_false, Nat.add_sub_cancel, e2, e3]
      refine ⟨by omega, by omega, trivial, e0, fun b hb => ?_⟩
      by_cases h3 : b < m
      · have h5 : ¬ m ≤ b := by omega
        have h6 : ¬ b = σ (a - m) + m := by omega
        have h7 : ¬ a ≤ b := by omega
        simp [h3, h5, h6, h7]
      · obtain ⟨f1, f2, f3⟩ := e4 (b - m) (by omega)
        have h5 : m ≤ b := by omega
        have h6 : b = σ (a - m) + m ↔ b - m = σ (a - m) := by omega
        simp only [h3, h5, h4, if_false, h6, f3, and_self, and_false, and_true]
        refine ⟨fun hab => ?_, fun hab => ?_, by simp⟩
        · have := f1 (by omega); omega
        · have := f2 (by omega); omega

theorem mul_mono {E : Type} [CommRing E] {n : ℕ} (σ : Fin n → Fin n) (hσ : ∀ a, σ (σ a) = a) (c : Fin n → E)
    (Z : Matrix (Fin n) (Fin n) E) (hZ : ∀ a b, Z a b = if b = σ a then c a else 0)
    (X Y : Matrix (Fin n) (Fin n) E) :
    X * Z = Z * Y ↔ ∀ i a, X i a * c a = c i * Y (σ i) (σ a) := by
  have h1 : ∀ i a, (X * Z) i (σ a) = X i a * c a := by
    intro i a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · simp [hZ]
    · intro k _ hk
      have : ¬ σ a = σ k := fun h => hk (by rw [← hσ k, ← h, hσ])
      simp [hZ, this]
    · simp
  have h2 : ∀ i j, (Z * Y) i j = c i * Y (σ i) j := by
    intro i j
    simp [Matrix.mul_apply, hZ]
  constructor
  · intro h i a; rw [← h1, h, h2]
  · intro h; ext i j; rw [← hσ j, h1, h2, h]

end GlobalTheory.PointStab

namespace GlobalTheory.PointStab

open Formalism.MainNotions.S

theorem stab_blockDiag : ∀ {K : Type} [Field K] (sig : K →+* K), (∀ x, sig (sig x) = x) → ∀ (r : ℕ) (w : Formalism.MainNotions.S.Point K (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K), Formalism.MainNotions.S.ZhatOM Z = Formalism.MainNotions.S.ptMat w → (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s → Formalism.MainNotions.S.IsUpUni s' → (s.map sig).transpose * Z * s' = Z → ∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) ∧ ∀ s' : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s' → (∀ a b : Fin (r + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → s' a b = 0) → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, Formalism.MainNotions.S.IsUpUni s ∧ (s.map sig).transpose * Z * s' = Z := by
  intro K _ sig hsig r w Z hZ
  obtain ⟨σ, t, h⟩ := ptEntry_monomial w.1 (fun b hb => (w.2.1 b hb).1)
  rw [w.2.2] at h
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ a, (h a a.2).1⟩
  let β : Fin (r + 1) → ℕ := fun a => Formalism.L2.SG.RealObj.blkOf w.1 a.1
  let c : Fin (r + 1) → K := fun a => (-1) ^ (r - σ a) * t a
  have hc : ∀ a, c a ≠ 0 := fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h a a.2).2.2.2.1
  have hσ : ∀ a, σ' (σ' a) = a := fun a => Fin.ext (h a a.2).2.1
  have hβσ : ∀ a, β (σ' a) = β a := fun a => (h a a.2).2.2.1
  have hlt : ∀ a b, β a < β b → a < b := fun a b hab => by
    by_contra h'
    exact absurd (((h b b.2).2.2.2.2 a a.2).1 (not_lt.1 h')) (not_le.2 hab)
  have hrev : ∀ a b, β a = β b → a < b → σ' b < σ' a := fun a b hab hl => by
    have h1 := ((h a a.2).2.2.2.2 b b.2).2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  have hZ' : ∀ a b, Z a b = if b = σ' a then c a else 0 := by
    intro a b
    have e0 := congrFun (congrFun hZ a) b
    simp only [ZhatOM, ptMat] at e0
    have e : Z a b = (-1) ^ (r - b.val) * ptEntry w.1 a b := by
      rw [← e0, ← mul_assoc, ← mul_pow]; simp
    rw [e, ((h a a.2).2.2.2.2 b b.2).2.2]
    by_cases hb : b = σ' a
    · subst hb; simp [σ', c]
    · have h3 : ¬ (b : ℕ) = σ a := fun h' => hb (Fin.ext h')
      simp [hb, h3]
  have hmm := mul_mono σ' hσ c Z hZ'
  have hLapp : ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ∀ i a, (s.map sig).transpose i a = sig (s a i) :=
    fun s i a => rfl
  refine ⟨fun s s' hs hs' hE a b hab => ?_, fun s' hs' hbd => ?_⟩
  · generalize hLdef : (s.map sig).transpose = L at hE
    have hLapp' : ∀ i a, L i a = sig (s a i) := fun i a => by rw [← hLdef]; rfl
    have hLT : L.BlockTriangular OrderDual.toDual := fun i j hij => by
      have hij' : i < j := OrderDual.toDual_lt_toDual.1 hij
      rw [hLapp', (hs j i).1 hij', map_zero]
    have hdet : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L hLT]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hLapp', (hs i i).2 rfl, map_one]
    have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
    letI : Invertible L := Matrix.invertibleOfIsUnitDet L hu
    have hBT := Matrix.blockTriangular_inv_of_blockTriangular hLT
    have e : L⁻¹ * Z = Z * s' := by
      calc L⁻¹ * Z = L⁻¹ * (L * Z * s') := by rw [hE]
        _ = Z * s' := by
          rw [Matrix.mul_assoc L, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [hmm] at e
    rcases lt_or_gt_of_ne hab with h1 | h1
    · have h2 : σ' a < σ' b := hlt _ _ (by rw [hβσ, hβσ]; exact h1)
      have h3 := e (σ' a) (σ' b)
      rw [hσ, hσ, hBT (OrderDual.toDual_lt_toDual.2 h2), zero_mul, eq_comm] at h3
      exact (mul_eq_zero.1 h3).resolve_left (hc _)
    · exact (hs' a b).1 (hlt _ _ h1)
  · have hs'T : s'.BlockTriangular id := fun i j hij => (hs' i j).1 hij
    have hdet : s'.det = 1 := by
      rw [Matrix.det_of_upperTriangular hs'T]
      exact Finset.prod_eq_one fun i _ => (hs' i i).2 rfl
    have hu : IsUnit s'.det := by rw [hdet]; exact isUnit_one
    letI : Invertible s' := Matrix.invertibleOfIsUnitDet s' hu
    have hUup := Matrix.blockTriangular_inv_of_blockTriangular hs'T
    have hs'β : s'.BlockTriangular (OrderDual.toDual ∘ β) := fun i j hij =>
      hbd i j (ne_of_lt (OrderDual.toDual_lt_toDual.1 hij))
    have hUβ := Matrix.blockTriangular_inv_of_blockTriangular hs'β
    have hsU : s' * s'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    have hUs : s'⁻¹ * s' = 1 := Matrix.nonsing_inv_mul _ hu
    generalize s'⁻¹ = U at hUup hUβ hsU hUs
    have hUdiag : ∀ i, U i i = 1 := by
      intro i
      have h1 : (s' * U) i i = 1 := by rw [hsU]; simp
      rw [Matrix.mul_apply, Finset.sum_eq_single i, (hs' i i).2 rfl, one_mul] at h1
      · exact h1
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [(hs' i k).1 h, zero_mul]
        · rw [hUup (show id i < id k from h), mul_zero]
      · simp
    let s : Matrix (Fin (r + 1)) (Fin (r + 1)) K := fun a i => sig (c i * U (σ' i) (σ' a) / c a)
    have hs : IsUpUni s := by
      intro a i
      refine ⟨fun hia => ?_, fun hai => ?_⟩
      · have h0 : U (σ' i) (σ' a) = 0 := by
          rcases lt_trichotomy (β i) (β a) with h1 | h1 | h1
          · exact hUβ (OrderDual.toDual_lt_toDual.2 (by rw [hβσ, hβσ]; exact h1))
          · exact hUup (show id (σ' a) < id (σ' i) from hrev _ _ h1 hia)
          · exact absurd (hlt _ _ h1) (not_lt.2 hia.le)
        simp [s, h0]
      · subst hai
        simp [s, hUdiag, hc a]
    refine ⟨s, hs, ?_⟩
    have e : (s.map sig).transpose * Z = Z * U := by
      rw [hmm]
      intro i a
      rw [hLapp]
      simp only [s, hsig]
      exact div_mul_cancel₀ _ (hc a)
    rw [e, Matrix.mul_assoc, hUs, Matrix.mul_one]

end GlobalTheory.PointStab
