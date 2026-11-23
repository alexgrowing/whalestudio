import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodClass

section Mat
variable {E : Type} [CommRing E] {n : ℕ}

def UpU (s : Matrix (Fin n) (Fin n) E) : Prop := (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1

def UnitIn (O : Subring E) (x : E) : Prop := x ∈ O ∧ ∃ y ∈ O, x * y = 1

theorem UpU.mul {s t : Matrix (Fin n) (Fin n) E} (hs : UpU s) (ht : UpU t) : UpU (s * t) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c i with h1 | h1
    · rw [hs.1 i c h1, zero_mul]
    · rw [ht.1 c j (lt_of_lt_of_le h h1), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i, hs.2, ht.2, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h1 | h1
      · rw [hs.1 i c h1, zero_mul]
      · rw [ht.1 c i h1, mul_zero]
    · simp

theorem UpU.det {s : Matrix (Fin n) (Fin n) E} (hs : UpU s) : s.det = 1 := by
  rw [Matrix.det_of_upperTriangular (M := s) (fun i j h => hs.1 i j h)]
  simp [hs.2]

theorem UpU.inv {s : Matrix (Fin n) (Fin n) E} (hs : UpU s) :
    ∃ t : Matrix (Fin n) (Fin n) E, UpU t ∧ t * s = 1 := by
  have hd : IsUnit s.det := by rw [hs.det]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet s hd
  have hb : s.BlockTriangular id := fun i j h => hs.1 i j h
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have h1 : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul s hd
  refine ⟨s⁻¹, ⟨fun i j h => hi h, fun i => ?_⟩, h1⟩
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hs.2, mul_one, Matrix.one_apply_eq] at h2
  · exact h2
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h1 | h1
    · rw [hi (show id c < id i from h1), zero_mul]
    · rw [hs.1 c i h1, mul_zero]
  · simp

theorem int_of_mul (O : Subring E) (M U : Matrix (Fin n) (Fin n) E) (hU : UpU U)
    (hM : ∀ m, ∃ i, UnitIn O (M i m) ∧ ∀ m', m < m' → M i m' = 0)
    (hZ : ∀ i j, (M * U) i j ∈ O) (m : Fin n) : (∀ i, M i m ∈ O) ∧ ∀ j, U m j ∈ O := by
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  have key : ∀ i j, (∀ c, m < c → M i c * U c j = 0) → M i m * U m j ∈ O := by
    intro i j h
    have h1 := hZ i j
    rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at h1
    have h2 : ∑ c ∈ Finset.univ.erase m, M i c * U c j ∈ O := by
      refine O.sum_mem fun c hc => ?_
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with h3 | h3
      · exact O.mul_mem ((ih c h3).1 i) ((ih c h3).2 j)
      · rw [h c h3]; exact O.zero_mem
    simpa using O.sub_mem h1 h2
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := key i m fun c hc => by rw [hU.1 c m hc, mul_zero]
    rwa [hU.2, mul_one] at this
  · obtain ⟨i, ⟨_, y, hy, hy1⟩, h0⟩ := hM m
    have := O.mul_mem hy (key i j fun c hc => by rw [h0 c hc, zero_mul])
    rwa [← mul_assoc, mul_comm y, hy1, one_mul] at this

theorem decomp (O : Subring E) (W : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (hσ : ∀ a, σ (σ a) = a) (hmono : ∀ a b : Fin n, a ≤ b → (a : ℕ) + σ a ≤ b + σ b)
    (h0 : ∀ a b, b ≠ σ a → W a b = 0) (hu : ∀ a, UnitIn O (W a (σ a)))
    (L U : Matrix (Fin n) (Fin n) E) (hL : UpU L.transpose) (hU : UpU U)
    (hZ : ∀ i j, (L * W * U) i j ∈ O) :
    ∃ D L₁ V U₁ : Matrix (Fin n) (Fin n) E, UpU D.transpose ∧ UpU L₁.transpose ∧ UpU V ∧ UpU U₁ ∧
      (∀ i j, L₁ i j ∈ O) ∧ (∀ i j, U₁ i j ∈ O) ∧ L = L₁ * D ∧ U = V * U₁ ∧ D * W * V = W := by
  choose e he using fun a => (hu a).2
  let β : Fin n → ℕ := fun a => (a : ℕ) + σ a
  have hβ : ∀ a, β (σ a) = β a := fun a => by simp only [β, hσ]; omega
  have hWl : ∀ (X : Matrix (Fin n) (Fin n) E) a b, (W * X) a b = W a (σ a) * X (σ a) b := by
    intro X a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · intro c _ hc; rw [h0 a c hc, zero_mul]
    · simp
  have hWr : ∀ (X : Matrix (Fin n) (Fin n) E) a b, (X * W) a b = X a (σ b) * W (σ b) b := by
    intro X a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ b)]
    · intro c _ hc; rw [h0 c b (fun h => hc (by rw [h, hσ])), mul_zero]
    · simp
  let D : Matrix (Fin n) (Fin n) E := fun a b => if β a = β b then L a b else 0
  have hD : UpU D.transpose := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · have := hL.1 i j h
      simp only [Matrix.transpose_apply] at this ⊢
      simp [D, this]
    · have := hL.2 i
      simp only [Matrix.transpose_apply] at this ⊢
      simp [D, this]
  have hd : IsUnit D.det := by rw [← Matrix.det_transpose, hD.det]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet D hd
  have hb : D.BlockTriangular (OrderDual.toDual ∘ β) := by
    intro i j h
    have h' : β i < β j := h
    simp [D, h'.ne]
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have hL1 : ∀ a b, β a ≤ β b → (L * D⁻¹) a b = (1 : Matrix (Fin n) (Fin n) E) a b := by
    intro a b hab
    rw [← Matrix.mul_nonsing_inv D hd, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases lt_trichotomy (β a) (β c) with h | h | h
    · have h3 : a < c := by
        by_contra h4
        exact absurd (hmono c a (not_lt.1 h4)) (not_le.2 h)
      have := hL.1 c a h3
      simp only [Matrix.transpose_apply] at this
      simp [D, this]
    · simp [D, h]
    · have h' : β c < β b := lt_of_lt_of_le h hab
      rw [hi (show (OrderDual.toDual ∘ β) b < (OrderDual.toDual ∘ β) c from h'), mul_zero, mul_zero]
  let V : Matrix (Fin n) (Fin n) E := fun a b => e (σ a) * D (σ a) (σ b) * W (σ b) b
  have hV : UpU V := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · by_cases h1 : β (σ i) = β (σ j)
      · have h2 : σ i < σ j := by
          simp only [β, hσ] at h1
          rw [Fin.lt_def] at h ⊢
          omega
        have := hD.1 _ _ h2
        simp only [Matrix.transpose_apply] at this
        simp only [V, this, mul_zero, zero_mul]
      · simp [V, D, h1]
    · have h1 := hD.2 (σ i)
      have h2 := (he (σ i)).2
      simp only [Matrix.transpose_apply] at h1
      rw [hσ] at h2
      simp only [V, h1, mul_one]
      rw [mul_comm, h2]
  have hDW : D * W = W * V := by
    ext a b
    rw [hWl, hWr]
    simp only [V, hσ]
    linear_combination (-(D a (σ b) * W (σ b) b)) * (he a).2
  obtain ⟨V', hV', hVV⟩ := hV.inv
  have hLD : L = L * D⁻¹ * D := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul D hd, Matrix.mul_one]
  have hint := int_of_mul O (L * D⁻¹ * W) (V * U) (hV.mul hU) (fun m => ⟨σ m, by
      rw [hWr, hL1 _ _ le_rfl, Matrix.one_apply_eq, one_mul]
      have := hu (σ m)
      rwa [hσ] at this, fun m' hm => by
      rw [hWr, hL1 _ _ (by rw [hβ, hβ]; exact hmono _ _ hm.le), Matrix.one_apply_ne, zero_mul]
      intro h
      exact hm.ne (by rw [← hσ m, h, hσ])⟩) (by
      have : L * D⁻¹ * W * (V * U) = L * W * U := by
        conv_rhs => rw [hLD]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc W, ← hDW, Matrix.mul_assoc]
      rwa [this])
  refine ⟨D, L * D⁻¹, V', V * U, hD, ⟨fun i j h => ?_, fun i => ?_⟩, hV', hV.mul hU, fun i j => ?_,
    fun i j => (hint i).2 j, hLD, ?_, ?_⟩
  · rw [Matrix.transpose_apply, hL1 _ _ (hmono _ _ h.le), Matrix.one_apply_ne h.ne]
  · rw [Matrix.transpose_apply, hL1 _ _ le_rfl, Matrix.one_apply_eq]
  · have := O.mul_mem ((hint (σ j)).1 i) (he j).1
    rwa [hWr, hσ, mul_assoc, (he j).2, mul_one] at this
  · rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  · rw [hDW, Matrix.mul_assoc, mul_eq_one_comm.1 hVV, Matrix.mul_one]

end Mat

section Blocks
open GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]

theorem UnitIn.mul {O : Subring E} {x y : E} (hx : UnitIn O x) (hy : UnitIn O y) : UnitIn O (x * y) := by
  obtain ⟨h1, a, ha, ha1⟩ := hx
  obtain ⟨h2, b, hb, hb1⟩ := hy
  exact ⟨O.mul_mem h1 h2, a * b, O.mul_mem ha hb, by linear_combination (y * b) * ha1 + hb1⟩

theorem UnitIn.cancel {O : Subring E} {x y : E} (hx : UnitIn O x) (hy : UnitIn O (x * y)) :
    UnitIn O y := by
  obtain ⟨h1, a, ha, ha1⟩ := hx
  obtain ⟨h2, b, hb, hb1⟩ := hy
  refine ⟨?_, x * b, O.mul_mem h1 hb, by linear_combination hb1⟩
  have := O.mul_mem ha h2
  rwa [← mul_assoc, mul_comm a, ha1, one_mul] at this

theorem unitIn_sign (O : Subring E) (m : ℕ) : UnitIn O ((-1) ^ m) :=
  ⟨O.pow_mem (O.neg_mem O.one_mem) m, (-1) ^ m, O.pow_mem (O.neg_mem O.one_mem) m, by
    rw [← mul_pow]; simp⟩

theorem unitIn_prod (O : Subring E) {ι : Type} (s : Finset ι) (g : ι → E) (h : ∀ i ∈ s, UnitIn O (g i)) :
    UnitIn O (∏ i ∈ s, g i) :=
  Finset.prod_induction g (UnitIn O) (fun _ _ => UnitIn.mul) ⟨O.one_mem, 1, O.one_mem, one_mul 1⟩ h

theorem sig_mono : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), a ≤ b → a + sig bs a ≤ b + sig bs b
  | [], a, b, h => by change a + a ≤ b + b; omega
  | (t, s) :: bs, a, b, h => by
    have := sig_mono bs (a - s) (b - s) (by omega)
    simp only [sig_cons]
    split_ifs <;> omega

theorem unit_entries (O : Subring E) (hO : ∀ (x : E) (s : ℕ), 0 < s → x ^ s ∈ O → x ∈ O) :
    ∀ bs : List (Eˣ × ℕ+), (∀ l ≤ (bs.map (fun b => (b.2 : ℕ))).sum, (∀ a < l, sig bs a < l) →
      UnitIn O (∏ a ∈ Finset.range l, ptEntryL bs a (sig bs a))) →
      ∀ a < (bs.map (fun b => (b.2 : ℕ))).sum, UnitIn O (ptEntryL bs a (sig bs a))
  | [], _, a, h => by simp at h
  | (t, s) :: bs, H, a, h => by
    simp only [List.map_cons, List.sum_cons] at h H
    have e1 : ∀ c < (s : ℕ), ptEntryL ((t, s) :: bs) c (sig ((t, s) :: bs) c) = t := by
      intro c hc
      simp only [sig_cons, ptEntryL, hc, if_true]
      rw [if_pos ⟨trivial, by omega⟩, if_pos (by omega)]
    have e2 : ∀ c, ptEntryL ((t, s) :: bs) (s + c) (sig ((t, s) :: bs) (s + c)) =
        ptEntryL bs c (sig bs c) := by
      intro c
      have hc : ¬ ((s : ℕ) + c < s) := by omega
      simp only [sig_cons, ptEntryL, hc, if_false, false_and, Nat.add_sub_cancel_left]
      rw [if_pos ⟨by omega, by omega⟩]
    have h1 := H s (by omega) (fun c hc => by simp only [sig_cons, hc, if_true]; omega)
    by_cases ha : a < s
    · rw [Finset.prod_congr rfl (fun c hc => e1 c (Finset.mem_range.1 hc)), Finset.prod_const,
        Finset.card_range] at h1
      obtain ⟨h2, y, hy, hy1⟩ := h1
      rw [e1 a ha]
      refine ⟨hO _ _ s.pos h2, ((t⁻¹ : Eˣ) : E), hO _ _ s.pos ?_, t.mul_inv⟩
      have : ((t⁻¹ : Eˣ) : E) ^ (s : ℕ) = y := by
        rw [← mul_one (_ ^ _), ← hy1, ← mul_assoc, ← mul_pow, t.inv_mul, one_pow, one_mul]
      rwa [this]
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 ha)
      rw [e2]
      refine unit_entries O hO bs (fun l hl hs => ?_) c (by omega)
      have h2 := H (s + l) (by omega) (fun c hc => by
        simp only [sig_cons]
        split_ifs with h3
        · omega
        · have := hs (c - s) (by omega); omega)
      rw [Finset.prod_range_add] at h2
      simp only [e2] at h2
      exact h1.cancel h2

theorem unit_of_lead [Nontrivial E] (O : Subring E) (hO : ∀ (x : E) (s : ℕ), 0 < s → x ^ s ∈ O → x ∈ O)
    {n : ℕ} (w : Pt E n) (ε : Fin n → ℕ) (Z : Matrix (Fin n) (Fin n) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ ε b) (h : ∀ l, lead Z l ≠ 0 → UnitIn O (lead Z l)) :
    ∃ σ : Fin n → Fin n, (∀ a, σ (σ a) = a) ∧ (∀ a b : Fin n, a ≤ b → (a : ℕ) + σ a ≤ b + σ b) ∧
      (∀ a b, b ≠ σ a → Z a b = 0) ∧ ∀ a, UnitIn O (Z a (σ a)) := by
  have hs : ∀ a : Fin n, sig w.blocks a < n := fun a => by
    have := (entry_unit w.blocks a (by rw [w.size]; omega)).1
    rwa [w.size] at this
  refine ⟨fun a => ⟨_, hs a⟩, fun a => Fin.ext (sig_sig _ _), fun a b hab => sig_mono _ _ _ hab,
    fun a b hb => ?_, fun a => ?_⟩
  · rw [hZ, Pt.mat, entry_zero, zero_mul]
    exact fun h => hb (Fin.ext h)
  · rw [hZ]
    refine UnitIn.mul ?_ (unitIn_sign O _)
    refine unit_entries O hO w.blocks (fun l hl hsl => ?_) a (by rw [w.size]; exact a.2)
    rw [w.size] at hl
    let τ : Fin l → Fin l := fun a => ⟨_, hsl a a.2⟩
    have hτ : Function.Injective τ := by
      intro a b hab
      have h1 : sig w.blocks a = sig w.blocks b := congrArg Fin.val hab
      apply Fin.ext
      rw [← sig_sig w.blocks a, h1, sig_sig]
    have h1 : lead Z ⟨l, Nat.lt_succ_of_le hl⟩ = _ :=
      det_mono (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) τ (fun a b hb => by
        rw [Matrix.submatrix_apply, hZ, Pt.mat, entry_zero, zero_mul]
        exact fun h => hb (Fin.ext h))
    have h2 : UnitIn O ((1 : Matrix (Fin l) (Fin l) E).submatrix τ id).det := by
      have hb := Finite.injective_iff_bijective.1 hτ
      have := Matrix.det_permute (Equiv.ofBijective τ hb) (1 : Matrix (Fin l) (Fin l) E)
      rw [Equiv.coe_ofBijective] at this
      rw [this, Matrix.det_one, mul_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective τ hb)) with h3 | h3
      · rw [h3]; simpa using unitIn_sign O 0
      · rw [h3]; simpa using unitIn_sign O 1
    have h3 : ∏ a, Z.submatrix (Fin.castLE hl) (Fin.castLE hl) a (τ a) =
        (∏ a : Fin l, (-1 : E) ^ ε (Fin.castLE hl (τ a))) *
          ∏ a ∈ Finset.range l, ptEntryL w.blocks a (sig w.blocks a) := by
      rw [Finset.prod_range, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Matrix.submatrix_apply, hZ, mul_comm]; rfl
    have h4 := unitIn_prod O Finset.univ (fun a : Fin l => (-1 : E) ^ ε (Fin.castLE hl (τ a)))
      fun a _ => unitIn_sign O _
    rw [h3, mul_comm, ← mul_assoc] at h1
    have h5 := h2.mul h4
    refine h5.cancel (h1 ▸ h _ ?_)
    rw [h1]
    refine IsUnit.ne_zero (IsUnit.mul ?_ ?_)
    · obtain ⟨_, y, _, hy⟩ := h5
      exact IsUnit.of_mul_eq_one y hy
    · rw [IsUnit.prod_iff]
      intro a ha
      exact (entry_unit w.blocks a (by rw [w.size]; have := Finset.mem_range.1 ha; omega)).2

end Blocks

section Main
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem pair_comb {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    S.h (∑ i, A' i b • S.f' i) (∑ i, A i a • S.f i) = (cT L A * S.Zh * A') a b := by
  have key : ∀ (α : Fin (r + 1) → E) (g : Fin (r + 1) → S.V) (y : S.V),
      hf L S.Hm (∑ i, α i • g i) y = ∑ i, α i * hf L S.Hm (g i) y := fun α g y => by
    change GlobalTheory.FrameBasic.hfL L S.Hm y _ = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  simp only [Frames.h, Matrix.mul_apply, Frames.Zh, Matrix.of_apply, cT]
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FrameBasic.hf_conj L S.herm.1, key, map_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← GlobalTheory.FrameBasic.hf_conj L S.herm.1]

theorem comb_mul {V ι : Type} [AddCommGroup V] [Module E V] [Fintype ι] (g : ι → V)
    (s A : Matrix ι ι E) (j : ι) :
    ∑ i, A i j • ∑ c, s c i • g c = ∑ c, (s * A) c j • g c := by
  simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem int_mul {L : LocE F E} {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : IsIntM L A)
    (hB : IsIntM L B) : IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact L.O.sum_mem fun c _ => L.O.mul_mem (hA i c) (hB c j)

theorem up_cT (L : LocE F E) {n : ℕ} {A : Matrix (Fin n) (Fin n) E} (hA : UpU A.transpose) :
    UpU (cT L A) :=
  ⟨fun i j h => by have := hA.1 i j h; rw [Matrix.transpose_apply] at this; simp [cT, this],
    fun i => by have := hA.2 i; rw [Matrix.transpose_apply] at this; simp [cT, this]⟩

theorem cT_cT (L : LocE F E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : cT L (cT L A) = A := by
  ext i j; simp [cT, L.cj_cj]

theorem cT_mul (L : LocE F E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext i j; simp [cT, Matrix.mul_apply, mul_comm]

theorem mem_cls {L : LocE F E} {r k : ℕ} (S : Frames L r k) (hg : S.gg = false)
    (g g' : Fin (r + 1) → S.V) (p : S.FrP) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hA : UpU A) (hA' : UpU A') (iA : IsIntM L A) (iA' : IsIntM L A')
    (h : ∀ j, p.1 j = ∑ i, A i j • g i) (h' : ∀ j, p.2 j = ∑ i, A' i j • g' i) :
    p ∈ S.frameCls g g' :=
  ⟨A, A', iA, iA', fun i j hij => ⟨hA.1 i j hij, hA'.1 i j hij⟩, fun i => ⟨hA.2 i, hA'.2 i⟩,
    fun i j => ⟨_, L.O.sub_mem (iA' i j) (iA i j), by simp [Frames.th, hg]⟩, h, h'⟩

theorem smul_span_le {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) (h : S.GLV)
    {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (iA : IsIntM L A) (hA : ∀ j, h (g j) = ∑ i, A i j • g i) :
    h • Submodule.span L.O (Set.range g) ≤ Submodule.span L.O (Set.range g) := by
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  change h (g j) ∈ Submodule.span L.O (Set.range g)
  rw [hA]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (⟨A i j, iA i j⟩ : L.O) (Submodule.subset_span ⟨i, rfl⟩)

theorem int_of_stab {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : LinearIndependent E g) (h : S.GLV)
    (hh : h • Submodule.span L.O (Set.range g) = Submodule.span L.O (Set.range g))
    {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hA : ∀ j, h (g j) = ∑ i, A i j • g i) : IsIntM L A := by
  intro i j
  have h1 : h • g j ∈ Submodule.span L.O (Set.range g) := by
    rw [← hh]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
  have h2 : ∑ i, (c i : E) • g i = ∑ i, A i j • g i := by rw [← hA]; exact hc
  rw [← Fintype.linearIndependent_iffₛ.1 hg _ _ h2 i]
  exact (c i).2

theorem one_class {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hg : S.gg = false)
    (hD : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1) :
    S.IsIntCls (S.frameCls S.f S.f') ∧ S.wC (S.frameCls S.f S.f') = 1 ∧
      ∀ C, S.IsIntCls C → ∃ h ∈ S.St, C = h • S.frameCls S.f S.f' := by
  have : Nontrivial E := by
    have := L.free
    exact Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx =>
    ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 x hx).1
  have icT : ∀ {A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}, IsIntM L A → IsIntM L (cT L A) :=
    fun hA i j => hcj _ (hA j i)
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  obtain ⟨hN, hN', -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto L r k S
  have hli := (GlobalTheory.FrameBasic.main L r k S).1
  have hli1 : LinearIndependent E S.f := hli.comp Sum.inl Sum.inl_injective
  have hli2 : LinearIndependent E S.f' := hli.comp Sum.inr Sum.inr_injective
  obtain ⟨σ, hσ, hmono, h0, hu⟩ := unit_of_lead L.O
    (fun x s hs hx => (L.O_def x).2 (IsIntegral.of_pow hs ((L.O_def _).1 hx))) S.w
    (fun b => r - (b : ℕ)) S.Zh (fun a b => S.relevant a b) hD
  have iZ : IsIntM L S.Zh := fun a b => by
    by_cases hb : b = σ a
    · rw [hb]; exact (hu a).1
    · rw [h0 a b hb]; exact L.O.zero_mem
  refine ⟨⟨⟨1, one_mem _, 1, one_mem _, rfl⟩, ?_⟩, ?_, ?_⟩
  · rintro p ⟨A, A', iA, iA', -, -, -, h1, h2⟩ a b
    rw [h1, h2, pair_comb]
    exact int_mul (int_mul (icT iA) iZ) iA' a b
  · have : S.St ⊓ MulAction.stabilizer S.GLV (S.frameCls S.f S.f') = S.K0 := by
      have key : ∀ h ∈ MulAction.stabilizer S.GLV (S.frameCls S.f S.f'),
          h • Submodule.span L.O (Set.range S.f) ≤ Submodule.span L.O (Set.range S.f) ∧
          h • Submodule.span L.O (Set.range S.f') ≤ Submodule.span L.O (Set.range S.f') := by
        intro h hh
        have h1 := (hcls (fun b => h (S.f b)) (fun b => h (S.f' b))).1
        rw [← (hcls S.f S.f').2.2 h, MulAction.mem_stabilizer_iff.1 hh] at h1
        obtain ⟨A, A', iA, iA', -, -, -, h1, h2⟩ := h1
        exact ⟨smul_span_le S _ h iA h1, smul_span_le S _ h iA' h2⟩
      ext h
      simp only [Frames.K0, Subgroup.mem_inf]
      constructor
      · rintro ⟨h1, h2⟩
        have k1 := key h h2
        have k2 := key h⁻¹ (inv_mem h2)
        have k3 := smul_mono_right h k2.1
        have k4 := smul_mono_right h k2.2
        rw [smul_inv_smul] at k3 k4
        exact ⟨⟨h1, le_antisymm k1.1 k3⟩, le_antisymm k1.2 k4⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        obtain ⟨s, hs, es⟩ := hN h h1.1
        obtain ⟨s', hs', es'⟩ := hN' h h1.2
        rw [MulAction.mem_stabilizer_iff, (hcls S.f S.f').2.2 h]
        exact ((hcls S.f S.f').2.1 (fun b => h (S.f b), fun b => h (S.f' b))
          (mem_cls S hg _ _ _ hs hs' (int_of_stab S _ hli1 h h2 es) (int_of_stab S _ hli2 h h3 es')
            es es')).1
    rw [Frames.wC, this, invVol, Subgroup.relIndex_self]
    simp
  · rintro C ⟨⟨n, hn, n', hn', rfl⟩, hC⟩
    obtain ⟨u, hu1, eu⟩ := hN n hn
    obtain ⟨u', hu1', eu'⟩ := hN' n' hn'
    obtain ⟨D, L₁, V, U₁, hD1, hL₁, hV, hU₁, iL, iU, e1, e2, e3⟩ :=
      decomp L.O S.Zh σ hσ hmono h0 hu (cT L u) u'
        ⟨fun i j h => by simp [cT, hu1.1 i j h], fun i => by simp [cT, hu1.2 i]⟩ hu1' (fun a b => by
          have := hC _ (hcls _ _).1 a b
          simp only [eu, eu'] at this
          rwa [pair_comb] at this)
    obtain ⟨h, hh, eh, eh'⟩ := ((GlobalTheory.HL.FrameStab.stab_eq L r k S).2 (cT L D) V (up_cT L hD1) hV).1
      (by rw [cT_cT, e3])
    refine ⟨h, hh, ?_⟩
    rw [(hcls S.f S.f').2.2 h]
    refine ((hcls _ _).2.1 (fun b => n (S.f b), fun b => n' (S.f' b))
      (mem_cls S hg _ _ _ (up_cT L hL₁) hU₁ (icT iL) iU (fun j => ?_) (fun j => ?_))).1
    · simp only [eh, eu]
      rw [comb_mul, ← cT_mul, ← e1, cT_cT]
    · simp only [eh', eu']
      rw [comb_mul, ← e2]

end Main

end GlobalTheory.HL.GoodClass
