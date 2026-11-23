import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame

noncomputable section

open Matrix MeasureTheory Formalism.L2.SG.HidaSetting Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open scoped InnerProductSpace

set_option linter.unusedSimpArgs false

namespace Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

section Rev
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem Qm_mulVec_mem_span {p : ℕ} (hp : p ≤ r) (y : Fin (2 * r + k + 1) → ℂ)
    (hy : ∀ i : Fin (2 * r + k + 1), p ≤ i.val → y i = 0) :
    Qm e f wf z0 *ᵥ y ∈ Submodule.span ℂ (e '' {b | b.1 < p}) := by
  have hy' : y = ∑ i, y i • bvec i := by
    ext j; simp [bvec, Pi.single_apply, Finset.sum_apply]
  rw [hy', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.mulVec_smul, Qm_mulVec_bvec]
  by_cases hi : i.val < p
  · have : colQ e f wf z0 i = e ⟨i.val, by omega⟩ := by
      unfold colQ; rw [dif_pos (by omega)]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, by omega⟩, by simp only [Set.mem_setOf_eq]; exact hi, rfl⟩)
  · rw [hy i (by omega), zero_smul]; exact Submodule.zero_mem _

theorem rev_UW (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zB = z)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r zB) :
    (∀ a, (Qm e f wf z0 * h * Qi ε e f wf z0) *ᵥ e a = e a) ∧
    (∀ a, (Qm e f wf z0 * h * Qi ε e f wf z0) *ᵥ f a = f a) ∧
    (Qm e f wf z0 * h * Qi ε e f wf z0) *ᵥ z = z := by
  obtain ⟨-, hfix, hzB⟩ := hh
  have hQz : Qi ε e f wf z0 *ᵥ z = zB := by rw [← hz, Matrix.mulVec_mulVec, Qi_mul_Qm hF, Matrix.one_mulVec]
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qi_e hF, (hfix a).1, Qm_mulVec_bvec, colQ_eI]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qi_f hF, (hfix a).2, Qm_mulVec_bvec, colQ_esI]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQz, hzB, hz]

theorem rev_N (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zB = z)
    (hzB : ∀ i : Fin (2 * r + k + 1), i.val < r ∨ r + k < i.val → zB i = 0)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) :
    InN ε e z (Qm e f wf z0 * m * Qi ε e f wf z0) := by
  obtain ⟨-, hcol, hW⟩ := hm
  have hQz : Qi ε e f wf z0 *ᵥ z = zB := by rw [← hz, Matrix.mulVec_mulVec, Qi_mul_Qm hF, Matrix.one_mulVec]
  have key : ∀ y : Fin (2 * r + k + 1) → ℂ,
      (Qm e f wf z0 * m * Qi ε e f wf z0 - 1) *ᵥ y = Qm e f wf z0 *ᵥ ((m - 1) *ᵥ (Qi ε e f wf z0 *ᵥ y)) := by
    intro y
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Qm_mul_Qi hF, Matrix.one_mulVec]

  have hcolX : ∀ (b : Fin r) (j : Fin (2 * r + k + 1)), b.val ≤ j.val → (m - 1) j (eI k r b) = 0 := by
    intro b j hj
    rw [Matrix.sub_apply, hcol b j hj, Matrix.one_apply]; split_ifs <;> simp
  have hcolW : ∀ i j : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → r ≤ j.val → (m - 1) j i = 0 := by
    intro i j hi1 hi2 hj
    rw [Matrix.sub_apply, hW j i hi1 hi2 hj, Matrix.one_apply]; split_ifs <;> simp
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, Qi_e hF]
    refine Qm_mulVec_mem_span (le_of_lt a.isLt) _ fun j hj => ?_
    rw [← mat_apply_bvec]; exact hcolX a j hj
  · rw [key, hQz]
    refine Qm_mulVec_mem_span le_rfl _ fun j hj => ?_
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hzB i hi, mul_zero]
    · push_neg at hi; rw [hcolW i j hi.1 hi.2 hj, zero_mul]
  · rw [key]
    refine Qm_mulVec_mem_span le_rfl _ fun j hj => ?_
    rw [show ((m - 1) *ᵥ (Qi ε e f wf z0 *ᵥ y)) j = ∑ i, (m - 1) j i * (Qi ε e f wf z0 *ᵥ y) i from rfl]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi1 : i.val < r
    · have : i = eI k r ⟨i.val, hi1⟩ := Fin.ext (by rw [eI_val])
      rw [this, hcolX _ j (by simp only; omega), zero_mul]
    · by_cases hi2 : i.val ≤ r + k
      · rw [hcolW i j (by omega) hi2 hj, zero_mul]
      ·
        have hi3 : 2 * r + k - i.val < r := by have := i.isLt; omega
        have : i = esI k r ⟨2 * r + k - i.val, hi3⟩ := Fin.ext (by rw [esI_val]; simp only; have := i.isLt; omega)
        rw [this, Qi_mulVec, sgn_esI, sig_esI_eq, colQ_eI, hy, mul_zero, mul_zero]

end Rev

section Levi
variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem UJ_ext {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b := Subtype.ext (Units.ext h)

theorem inS_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (he : ∀ a, h *ᵥ e a = e a) (hz : h *ᵥ z = z) (hn : InN ε e z n) : InS e z (h * n) := by
  have hspan : ∀ p, ∀ y ∈ spanLt e p, h *ᵥ y = y := by
    intro p y hy
    induction hy using Submodule.span_induction with
    | mem x hx => obtain ⟨b, -, rfl⟩ := hx; exact he b
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  obtain ⟨⟨h1, h2⟩, -⟩ := hn
  refine ⟨fun a => ?_, ?_⟩
  · have : (h * n - 1) *ᵥ e a = h *ᵥ ((n - 1) *ᵥ e a) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
      simp only [he]
    rw [this, hspan _ _ (h1 a)]; exact h1 a
  · have : (h * n - 1) *ᵥ z = h *ᵥ ((n - 1) *ᵥ z) := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]
      simp only [hz]
    rw [this, hspan _ _ h2]; exact h2

theorem HNset_iff (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zB = z)
    (hzB : ∀ i : Fin (2 * r + k + 1), i.val < r ∨ r + k < i.val → zB i = 0) (hz0 : ∃ t : ℂ, z0 = t • z)
    (s : Formalism.REAL.UJ ε) :
    s ∈ HNset ε e f wf z0 zB ↔ ∃ h n : Formalism.REAL.UJ ε, s = h * n ∧ (∀ a, uMat h *ᵥ e a = e a) ∧
      (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z ∧ InN ε e z (uMat n) := by
  constructor
  · rintro ⟨hB, hhB, mB, hmB, heq⟩
    have hUh := conjQ_UJ hF hhB.1
    have hUn := conjQ_UJ hF hmB.1
    refine ⟨toUJ _ hUh, toUJ _ hUn, UJ_ext ?_, ?_⟩
    · rw [uMat_mul, uMat_toUJ, uMat_toUJ]
      have : Qm e f wf z0 * hB * Qi ε e f wf z0 * (Qm e f wf z0 * mB * Qi ε e f wf z0) =
          Qm e f wf z0 * (hB * mB) * Qi ε e f wf z0 := by
        simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ (Qi ε e f wf z0) (Qm e f wf z0), Qi_mul_Qm hF,
          Matrix.mul_one]
      rw [this, ← heq]
      simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
      rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
    · obtain ⟨h1, h2, h3⟩ := rev_UW hF hz hhB
      exact ⟨h1, h2, h3, rev_N hF hz hzB hmB⟩
  · rintro ⟨h, n, rfl, he, hf, hzz, hn⟩
    refine ⟨_, conj_mem_UWset hF hz (uMat_mem h) he hf hzz, _, conj_mem_Nset hF hz0 (uMat_mem n) hn, ?_⟩
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f wf z0 * uMat h) (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.mul_one]

theorem inS_of_HNset (hF : IsFrameJ ε e f wf z0) {zB z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zB = z)
    (hzB : ∀ i : Fin (2 * r + k + 1), i.val < r ∨ r + k < i.val → zB i = 0) (hz0 : ∃ t : ℂ, z0 = t • z)
    {s : Formalism.REAL.UJ ε} (hs : s ∈ HNset ε e f wf z0 zB) : InS e z (uMat s) := by
  obtain ⟨h, n, rfl, he, -, hzz, hn⟩ := (HNset_iff hF hz hzB hz0 s).1 hs
  rw [uMat_mul]; exact inS_mul he hzz hn

theorem HNset_of_inS (hLevi : BesselLevi) (hF : IsFrameJ ε e f wf z0) {T : ℝ} (hT : 0 < T)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : Qm e f wf z0 *ᵥ zBv k r T = z) {s : Formalism.REAL.UJ ε}
    (hs : InS e z (uMat s)) : s ∈ HNset ε e f wf z0 (zBv k r T) := by
  have hQz : Qi ε e f wf z0 *ᵥ z = zBv k r T := by
    rw [← hz, Matrix.mulVec_mulVec, Qi_mul_Qm hF, Matrix.one_mulVec]
  refine hLevi k r T hT _ (conj_mem_UH hF (uMat_mem s)) (fun a i hai => ?_) (fun i hi => ?_)
  · rw [conj_apply, colQ_eI]
    obtain ⟨y, hy, hny⟩ : ∃ y ∈ spanLt e a.val, uMat s *ᵥ e a = e a + y :=
      ⟨(uMat s - 1) *ᵥ e a, hs.1 a, by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel⟩
    rw [hny, Matrix.mulVec_add, Pi.add_apply, Qi_e hF, bvec_apply]
    have h0 : (Qi ε e f wf z0 *ᵥ y) i = 0 := by
      refine coord_span_zero i _ ?_ hy
      rintro x ⟨b, hb, rfl⟩
      refine Qi_e_apply hF b i ?_
      intro h; have := congrArg Fin.val h; rw [eI_val] at this; simp only [Set.mem_setOf_eq] at hb; omega
    rw [h0, add_zero]
  · have e1 : (Qi ε e f wf z0 * uMat s * Qm e f wf z0) *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) =
        Qi ε e f wf z0 *ᵥ (uMat s *ᵥ z) := by
      have hz' : Qm e f wf z0 *ᵥ (((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z := hz
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz']
    rw [e1]
    obtain ⟨y, hy, hny⟩ : ∃ y ∈ spanLt e r, uMat s *ᵥ z = z + y :=
      ⟨(uMat s - 1) *ᵥ z, hs.2, by rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel⟩
    rw [hny, Matrix.mulVec_add, Pi.add_apply, hQz]
    have h0 : (Qi ε e f wf z0 *ᵥ y) i = 0 := by
      refine coord_span_zero i _ ?_ hy
      rintro x ⟨b, -, rfl⟩
      refine Qi_e_apply hF b i ?_
      intro h; have := congrArg Fin.val h; rw [eI_val] at this; have := b.isLt; omega
    rw [h0, add_zero]; rfl

end Levi

def LocHNProps : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    IsClosed {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)} ∧
    IsCompact {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z} ∧
    ((1 : Formalism.REAL.UJ ε) ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)} ∧
      (∀ a ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, ∀ b ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        a * b ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}) ∧
      ∀ a ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, a⁻¹ ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}) ∧
    (∀ h : Formalism.REAL.UJ ε, ((∀ a, uMat h *ᵥ e a = e a) ∧ (∀ a, uMat h *ᵥ f a = f a) ∧ uMat h *ᵥ z = z) →
      ∀ m : Formalism.REAL.UJ ε, InN ε e z (uMat m) → InN ε e z (uMat (h * m * h⁻¹)))

def NUnimodLoc : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (e f : Fin r → Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) (z0 z : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
    IsFrameJ ε e f wf z0 → c ≠ 0 → z0 = c • z →
    ∀ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ → μ ≠ 0 → μ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}ᶜ = 0 →
      (∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => s * x) = μ) →
      ∀ s ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)}, μ.map (fun x => x * s) = μ

end Formalism.L2.SG.Pf.WFL
