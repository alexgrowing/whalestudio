import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.PosEntries

section Shape
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem shape_inr {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (i : Fin c) (s : n ⊕ Fin c)
    (hs : M (Sum.inr i) s ≠ 0) : s = Sum.inr i := by
  rcases s with x | j
  · exfalso
    by_cases h : i.val + 1 < p
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · by_cases hij : j = i
    · rw [hij]
    exfalso
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
    · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))

theorem shape_inl {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hp : 1 ≤ p)
    (h1 : M.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : M.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (j : Fin c)
    (hs : M (Sum.inl x) (Sum.inr j) ≠ 0) : j.val + 1 = p := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hs (h1 (by simp only [Sum.elim_inl, Sum.elim_inr]; omega))
  · exact hs (h2 (by simp only [lev, Sum.elim_inl, Sum.elim_inr, OrderDual.toDual_lt_toDual]; omega))

end Shape

section Trans
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem mulD_inr (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (l : Fin (c + 1)) :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inr l) =
      x r (Sum.inr l) * (ϖ : k) ^ (l.val + 1) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem mulD_inl (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ϖ : kˣ) (r : n ⊕ Fin c) (y : n') :
    (x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) r (Sum.inl y) =
      x r (Sum.inl y) := by
  simp [embA, Matrix.mul_apply, Fintype.sum_sum_type, one_apply]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem opE_translate_free (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (hz : ∀ r s, ¬ Free p (r, s) → z r s = 0) (hΨ : ∀ x, Ψ (x + z) = Ψ x) (x₀ : Matrix n n' k) :
    opE ψ ν p Ψ x₀ = (ψ (-ch z) : ℂ) * opE ψ ν p Ψ x₀ := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ez : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k := fun rs => z rs.1.1 rs.1.2
  have hpt : ∀ e, affPt p x₀ (e + ez) = affPt p x₀ e + z := by
    intro e; ext r s
    simp only [affPt, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
    split_ifs with h
    · simp only [ez]; ring
    · simp [hz r s h]
  unfold opE
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ ez]
  congr 1; ext e
  rw [hpt, hΨ, ch_add, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem exists_affPt_ne_zero (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k} (h : opE ψ ν p Ψ x₀ ≠ 0) :
    ∃ e, Ψ (affPt p x₀ e) ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply h
  simp [opE, hn]

end Trans

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem entries_core (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : HasConductor ψ 1)
    (ϖ : kˣ) (hϖ : valuation k (ϖ : k) < 1) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (c p : ℕ) (hp1 : 1 ≤ p) (A : GL (n ⊕ Fin c) k)
    (hA1 : A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hA2 : A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (hB1 : (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (hB2 : (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)))
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (hInt : ∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val))
    (hMax : ∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) →
      Ψ (x + z) = Ψ x)
    (hE : opE ψ ν p Ψ ≠ 0) :
    (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧
      (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧
    ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  classical
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hE
  obtain ⟨e, he⟩ := exists_affPt_ne_zero ψ ν p hx₀
  have hI := hInt _ he
  have hx_diag : ∀ i : Fin c, affPt p x₀ e (Sum.inr i) (Sum.inr i.castSucc) = 1 := by
    intro i; simp [affPt, basePt, Free]
  have hx_X : ∀ (y : n) (q : Fin c), q.val + 1 = p → affPt p x₀ e (Sum.inl y) (Sum.inr q.castSucc) = 0 := by
    intro y q hq; subst hq; simp [affPt, basePt, Free]
  have hAB : ∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (A⁻¹).val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun (Units.mul_inv A) (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
  · have h := hI (Sum.inr i) (Sum.inr i.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i), hx_diag] at h
    · simpa using h
    · intro s _ hs
      by_cases h0 : A.val (Sum.inr i) s = 0
      · simp [h0]
      · exact absurd (shape_inr hA1 hA2 i s h0) hs
    · simp
  · have hb0 : (A⁻¹).val (Sum.inr i) (Sum.inr i) ≠ 0 := right_ne_zero_of_mul_eq_one (hAB i)
    have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
    have key : ∀ y : k, valuation k y ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) →
        ψ y = 1 := by
      intro y hy
      let ζ := y * ((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹
      let E : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
        Matrix.of fun u s => if u = Sum.inr i ∧ s = Sum.inr i.succ then ζ else 0
      let z := (A⁻¹).val * E
      have hAz : A.val * z = E := by simp only [z, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      have hzent : ∀ r s, z r s = if s = Sum.inr i.succ then (A⁻¹).val r (Sum.inr i) * ζ else 0 := by
        intro r s
        simp only [z, E, Matrix.mul_apply, Matrix.of_apply]
        split_ifs with hs
        · rw [Finset.sum_eq_single (Sum.inr i)] <;> simp_all
        · simp [hs]
      have hval : valuation k (ζ * (ϖ : k) ^ (i.val + 2)) < 1 := by
        have h1 : (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ *
            (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) = ϖ := by
          field_simp; ring
        calc valuation k (ζ * (ϖ : k) ^ (i.val + 2))
            = valuation k y * valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by
              rw [← map_mul, mul_assoc]
          _ ≤ valuation k ((A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹) *
              valuation k (((A⁻¹).val (Sum.inr i) (Sum.inr i))⁻¹ * (ϖ : k) ^ (i.val + 2)) := by gcongr
          _ = valuation k (ϖ : k) := by rw [← map_mul, h1]
          _ < 1 := hϖ
      have hmax : MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) := by
        intro r s
        rw [hAz]
        rcases s with y' | l
        · rw [mulD_inl]; simp [E]
        · rw [mulD_inr]
          simp only [E, Matrix.of_apply]
          split_ifs with h
          · obtain ⟨rfl, hl⟩ := h
            obtain rfl : l = i.succ := Sum.inr_injective hl
            rw [show (i.succ : Fin (c + 1)).val + 1 = i.val + 2 by simp [Fin.val_succ]]
            exact hval
          · simp
      have hfree : ∀ r s, ¬ Free p (r, s) → z r s = 0 := by
        intro r s hns
        rw [hzent]
        split_ifs with hs
        · subst hs
          by_cases h0 : (A⁻¹).val r (Sum.inr i) = 0
          · simp [h0]
          · exfalso; apply hns
            rcases r with y' | j
            · have := shape_inl hp1 hB1 hB2 y' i h0
              simp [Free, Fin.val_succ]; omega
            · obtain ⟨⟩ := shape_inr hB1 hB2 j (Sum.inr i) h0
              simp [Free, Fin.val_succ]
        · rfl
      have htr := opE_translate_free ψ ν p hfree (fun x' => hMax x' z hmax) x₀
      have hch : ch z = y := by
        simp only [ch, hzent]
        rw [Finset.sum_eq_single i]
        · simp only [if_true, ζ]; field_simp
        · intro j _ hj; simp [Fin.succ_inj, hj]
        · simp
      have h1 : (ψ (-ch z) : ℂ) = 1 := by
        have : ((ψ (-ch z) : ℂ) - 1) * opE ψ ν p Ψ x₀ = 0 := by rw [sub_mul, ← htr]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hx₀
      have h2 : ψ (-ch z) = 1 := Circle.ext (by simpa using h1)
      rw [AddChar.map_neg_eq_inv, inv_eq_one, hch] at h2
      exact h2
    have hle := (hψ _).mp key
    simp only [Units.val_one, map_one] at hle
    exact hle
  · intro q hq y
    have h := hI (Sum.inl y) (Sum.inr q.castSucc)
    rw [mulD_inr, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr q)] at h
    · rw [hx_diag] at h; simpa using h
    · intro s _ hs
      rcases s with z | j
      · simp [hx_X z q hq]
      · by_cases h0 : A.val (Sum.inl y) (Sum.inr j) = 0
        · simp [h0]
        · have := shape_inl hp1 hA1 hA2 y j h0
          exact absurd (by congr 1; exact Fin.ext (by omega)) hs
    · simp

end Main

theorem entries : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], HasConductor ψ 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (A : GL (n ⊕ Fin c) k), A.val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → A.val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → (A⁻¹).val.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))) → (A⁻¹).val.BlockTriangular (fun r => OrderDual.toDual (lev p r)) → ∀ (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), (∀ x, Ψ x ≠ 0 → IntM (A.val * x * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val)) → (∀ x z, MaxM (A.val * z * (embA n' (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => ϖ ^ (i.val + 1))).val) → Ψ (x + z) = Ψ x) → opE ψ ν p Ψ ≠ 0 → (∀ i : Fin c, A.val (Sum.inr i) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] ∧ (A⁻¹).val (Sum.inr i) (Sum.inr i) * ((ϖ : k) ^ (i.val + 1))⁻¹ ∈ 𝒪[k]) ∧ ∀ i : Fin c, i.val + 1 = p → ∀ x : n, A.val (Sum.inl x) (Sum.inr i) * (ϖ : k) ^ (i.val + 1) ∈ 𝒪[k] := by
  intro k _ _ _ _ _ _ ψ ν _ hψ ϖ hϖ n n' _ _ _ _ c p hp1 _ A hA1 hA2 hB1 hB2 Ψ hInt hMax hE
  exact entries_core ψ ν hψ ϖ hϖ n n' c p hp1 A hA1 hA2 hB1 hB2 Ψ hInt hMax hE

end GlobalTheory.PosEntries
