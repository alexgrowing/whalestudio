import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BlockStab

theorem exists_monomial {E : Type} [CommRing E] (bs : List (Eˣ × ℕ+)) :
    ∃ (σ β : ℕ → ℕ) (t : ℕ → Eˣ), ∀ a, a < (bs.map (fun b => (b.2 : ℕ))).sum →
      σ a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ σ (σ a) = a ∧ β (σ a) = β a ∧
      ∀ b, b < (bs.map (fun b => (b.2 : ℕ))).sum →
        (sameBlock bs a b = true ↔ β a = β b) ∧ (a ≤ b → β a ≤ β b) ∧
        (β a = β b → a + σ a = b + σ b) ∧
        ptEntryL bs a b = if b = σ a then (t (β a) : E) else 0 := by
  induction bs with
  | nil => exact ⟨id, id, fun _ => 1, by simp⟩
  | cons x bs ih =>
    obtain ⟨t0, s⟩ := x
    obtain ⟨σ, β, t, h⟩ := ih
    simp only [List.map_cons, List.sum_cons]
    generalize (bs.map (fun b => (b.2 : ℕ))).sum = N at h ⊢
    refine ⟨fun a => if a < (s : ℕ) then s - 1 - a else σ (a - s) + s,
      fun a => if a < (s : ℕ) then 0 else β (a - s) + 1,
      fun k => if k = 0 then t0 else t (k - 1), fun a ha => ?_⟩
    simp only [sameBlock, ptEntryL]
    generalize (s : ℕ) = m at *
    by_cases h1 : a < m
    · have h2 : m - 1 - a < m := by omega
      simp only [h1, h2, if_true]
      refine ⟨by omega, by omega, trivial, fun b hb => ?_⟩
      by_cases h3 : b < m
      · simp only [h3, if_true]
        refine ⟨by simp, by simp, fun _ => by omega, ?_⟩
        have : a + b + 1 = m ↔ b = m - 1 - a := by omega
        simp [this]
      · have h4 : ¬ m ≤ a := by omega
        have h5 : ¬ b = m - 1 - a := by omega
        simp [h3, h4, h5]
    · obtain ⟨e1, e2, e3, e4⟩ := h (a - m) (by omega)
      have h2 : ¬ σ (a - m) + m < m := by omega
      have h4 : m ≤ a := by omega
      simp only [h1, h2, if_false, Nat.add_sub_cancel, e2, e3]
      refine ⟨by omega, by omega, trivial, fun b hb => ?_⟩
      by_cases h3 : b < m
      · have h5 : ¬ m ≤ b := by omega
        have h6 : ¬ b = σ (a - m) + m := by omega
        have h7 : ¬ a ≤ b := by omega
        simp [h3, h5, h6, h7]
      · obtain ⟨f1, f2, f3, f4⟩ := e4 (b - m) (by omega)
        have h5 : m ≤ b := by omega
        have h6 : b = σ (a - m) + m ↔ b - m = σ (a - m) := by omega
        simp only [h3, h4, h5, if_false, h6, f4]
        refine ⟨by simp [f1], fun hab => ?_, fun hab => ?_, by simp⟩
        · have := f2 (by omega); omega
        · have := f3 (by omega); omega

section
variable {E : Type} [CommRing E] {n : ℕ}

theorem inv_facts (A : Matrix (Fin n) (Fin n) E) (hA : IsUni A) :
    ∃ B : Matrix (Fin n) (Fin n) E, A * B = 1 ∧ B * A = 1 ∧ IsUni B ∧
      (∀ O : Subring E, (∀ i j, A i j ∈ O) → ∀ i j, B i j ∈ O) ∧
      ∀ β : Fin n → ℕ, (∀ i j, β i < β j → A i j = 0) → ∀ i j, β i < β j → B i j = 0 := by
  have hT : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by rw [Matrix.det_of_upperTriangular hT]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hu
  have hT' := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨A⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, ⟨fun i j h => hT' h, fun i => ?_⟩,
    fun O hO i j => ?_, fun β hβ i j h => ?_⟩
  · have h1 : (A * A⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hT' (show id i < id k from h), mul_zero]
    · simp
  · have h1 : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, hO i j⟩ : O)) := by
      ext i j; simp
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, h1, ← RingHom.map_adjugate]
    simp
  · have h1 : A.BlockTriangular (OrderDual.toDual ∘ β) := fun i j h => hβ i j h
    exact Matrix.blockTriangular_inv_of_blockTriangular h1 (i := i) (j := j) h

theorem mul_mono (σ : Fin n → Fin n) (hσ : ∀ a, σ (σ a) = a) (c : Fin n → E)
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

end

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {n : ℕ}

theorem cj_mem_iff (L : LocE F E) {x : E} : L.cj x ∈ L.O ↔ x ∈ L.O := by
  have h : ∀ x, x ∈ L.O → L.cj x ∈ L.O := fun x hx => by
    rw [L.O_def] at hx ⊢
    exact hx.map (L.cj.toAlgHom.restrictScalars 𝒪[F])
  exact ⟨fun hx => by simpa [L.cj_cj] using h _ hx, h x⟩

theorem cT_mul_eq_one (L : LocE F E) (A B : Matrix (Fin n) (Fin n) E) (h : A * B = 1) :
    cT L B * cT L A = 1 := by
  ext i j
  have h1 := congrArg L.cj (congrFun (congrFun h j) i)
  simp only [Matrix.mul_apply, map_sum, map_mul] at h1
  simp only [Matrix.mul_apply, cT]
  rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply, hij, Ne.symm hij]

theorem stab_monomial (L : LocE F E) (σ : Fin n → Fin n) (β : Fin n → ℕ) (c : Fin n → Eˣ)
    (Z : Matrix (Fin n) (Fin n) E) (hσ : ∀ a, σ (σ a) = a) (hβ : ∀ a, β (σ a) = β a)
    (hm : ∀ a b, a ≤ b → β a ≤ β b) (hr : ∀ a b, β a = β b → a < b → σ b < σ a)
    (hc : ∀ a b, β a = β b → c a = c b ∨ c a = - c b)
    (hZ : ∀ a b, Z a b = if b = σ a then (c a : E) else 0) :
    (∀ s s' : Matrix (Fin n) (Fin n) E, IsUni s → IsUni s' → cT L s * Z * s' = Z →
      (∀ i j, β i ≠ β j → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧
    ∀ s : Matrix (Fin n) (Fin n) E, IsUni s → (∀ i j, β i ≠ β j → s i j = 0) →
      ∃ s', IsUni s' ∧ cT L s * Z * s' = Z := by
  have hlt : ∀ a b, β a < β b → a < b := fun a b h => by
    by_contra h'
    exact absurd (hm b a (not_lt.1 h')) (not_le.2 h)
  have key : ∀ X Y : Matrix (Fin n) (Fin n) E, IsUni X → IsUni Y → cT L X * Z = Z * Y →
      (∀ i j, β i ≠ β j → X i j = 0 ∧ Y i j = 0) ∧ (IsIntM L X ↔ IsIntM L Y) := by
    intro X Y hX hY h
    rw [mul_mono σ hσ (fun a => (c a : E)) Z hZ] at h
    simp only [cT] at h
    have hz : ∀ i j, β i ≠ β j → X i j = 0 ∧ Y i j = 0 := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with h1 | h1
      · constructor
        · have h2 := h j i
          rw [hY.1 _ _ (hlt _ _ (by rwa [hβ, hβ])), mul_zero, Units.mul_left_eq_zero] at h2
          simpa using h2
        · have h2 := h (σ i) (σ j)
          rw [hX.1 _ _ (hlt _ _ (by rwa [hβ, hβ])), map_zero, zero_mul, hσ, hσ, eq_comm,
            Units.mul_right_eq_zero] at h2
          exact h2
      · exact ⟨hX.1 _ _ (hlt _ _ h1), hY.1 _ _ (hlt _ _ h1)⟩
    have he : ∀ i a, X a i ∈ L.O ↔ Y (σ i) (σ a) ∈ L.O := by
      intro i a
      by_cases hia : β a = β i
      · have h2 := h i a
        rw [← cj_mem_iff L]
        rcases hc a i hia with h3 | h3
        · rw [h3, mul_comm, Units.mul_right_inj] at h2
          rw [h2]
        · rw [h3, Units.val_neg, mul_neg, ← neg_mul, mul_comm, Units.mul_right_inj] at h2
          rw [← h2, neg_mem_iff]
      · rw [(hz a i hia).1, (hz (σ i) (σ a) (by rw [hβ, hβ]; exact Ne.symm hia)).2]
    refine ⟨hz, fun hi p q => ?_, fun hi p q => (he q p).2 (hi _ _)⟩
    have := (he (σ p) (σ q)).1 (hi _ _)
    rwa [hσ, hσ] at this
  refine ⟨fun s s' hs hs' h => ?_, fun s hs hb => ?_⟩
  · obtain ⟨B, b1, b2, b3, b4, -⟩ := inv_facts s hs
    obtain ⟨U, u1, u2, u3, u4, -⟩ := inv_facts s' hs'
    have e1 : cT L s * Z = Z * U := by
      conv_rhs => rw [← h, Matrix.mul_assoc, u1, Matrix.mul_one]
    have e2 : cT L B * Z = Z * s' := by
      conv_lhs => rw [← h, Matrix.mul_assoc, ← Matrix.mul_assoc, cT_mul_eq_one L _ _ b1, Matrix.one_mul]
    obtain ⟨k1, k2⟩ := key s U hs u3 e1
    obtain ⟨k3, k4⟩ := key B s' b3 hs' e2
    exact ⟨fun i j hij => ⟨(k1 i j hij).1, (k3 i j hij).2⟩,
      fun hi => k4.1 (b4 L.O hi), fun hi => k2.2 (u4 L.O hi)⟩
  · let U : Matrix (Fin n) (Fin n) E := fun p q =>
      ((c (σ p))⁻¹ : Eˣ) * (L.cj (s (σ q) (σ p)) * c (σ q))
    have hU : IsUni U := by
      refine ⟨fun p q hpq => ?_, fun p => ?_⟩
      · have : s (σ q) (σ p) = 0 := by
          by_cases h1 : β q = β p
          · exact hs.1 _ _ (hr _ _ h1 hpq)
          · exact hb _ _ (by rwa [hβ, hβ])
        simp [U, this]
      · simp [U, hs.2]
    have e1 : cT L s * Z = Z * U := by
      rw [mul_mono σ hσ (fun a => (c a : E)) Z hZ]
      intro i a
      simp [U, hσ, cT]
    obtain ⟨V, u1, u2, u3, -⟩ := inv_facts U hU
    exact ⟨V, u3, by rw [e1, Matrix.mul_assoc, u1, Matrix.mul_one]⟩

end

theorem stabiliser_blockDiag : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨σ, β, t, h⟩ := exists_monomial S.w.blocks
  rw [S.w.size] at h
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ a, (h a a.2).1⟩
  have hsb : ∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false ↔ β i ≠ β j := fun i j => by
    rw [Ne, ← ((h i i.2).2.2.2 j j.2).1]; simp
  simp only [hsb]
  refine stab_monomial L σ' (fun a => β a) (fun a => t (β a) * (-1) ^ (r - σ a)) S.Zh
    (fun a => Fin.ext (h a a.2).2.1) (fun a => (h a a.2).2.2.1)
    (fun a b hab => ((h a a.2).2.2.2 b b.2).2.1 hab) (fun a b hab hl => ?_) (fun a b hab => ?_)
    (fun a b => ?_)
  · have h1 := ((h a a.2).2.2.2 b b.2).2.2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  · simp only [hab]
    rcases neg_one_pow_eq_or Eˣ (r - σ a) with h1 | h1 <;>
      rcases neg_one_pow_eq_or Eˣ (r - σ b) with h2 | h2 <;> simp [h1, h2]
  · have h1 : S.Zh a b = S.w.mat a b * (-1) ^ (r - (b : ℕ)) := S.relevant a b
    rw [h1, Pt.mat, ((h a a.2).2.2.2 b b.2).2.2.2]
    by_cases h2 : b = σ' a
    · subst h2; simp [σ']
    · have h3 : ¬ (b : ℕ) = σ a := fun h => h2 (Fin.ext h)
      simp [h2, h3]

end GlobalTheory.HL.BlockStab
