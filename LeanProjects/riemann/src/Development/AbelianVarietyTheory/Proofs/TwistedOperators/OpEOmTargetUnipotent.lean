import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.TargetUnip

theorem det_eq_one_of_level {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (M : Matrix ι ι k) (hM : ∀ r s, f s ≤ f r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hb : M.BlockTriangular f := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock f a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hM _ _ (by rw [i.2, j.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']

theorem mul_apply_of_inN {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) {m : Type*}
    (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (h.val * x) r s = x r s + ∑ r', if lev p r < lev p r' then h.val r r' * x r' s else 0 := by
  have h1 : x r s = ∑ r', (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r r' * x r' s := by
    rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [Matrix.mul_apply, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r' _ => ?_
  split_ifs with hl
  · rw [Matrix.one_apply_ne, zero_mul, zero_add]
    rintro rfl
    exact lt_irrefl _ hl
  · rw [hh r r' (not_lt.1 hl), add_zero]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_of_not_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r s} (hrs : ¬ Free p (r, s)) :
    affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, hrs]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_eq_zero (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r r' : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hrs : ¬ Free p (r, s))
    (hl : lev p r < lev p r') : affPt p x₀ e r' s = 0 := by
  rcases r with r | r <;> rcases r' with r' | r' <;> rcases s with s | s <;>
    simp only [lev, Free, Sum.elim_inl, Sum.elim_inr, lt_irrefl] at hrs hl <;>
    rw [affPt_of_not_free _ _ _ (by simp only [Free]; omega)] <;>
    simp [basePt] <;> omega

open Classical in

def linPart (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0

open Classical in
theorem det_linPart {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) :
    (linPart (n' := n') p h.val).det = 1 := by
  refine det_eq_one_of_level (fun a => lev p a.1.1) _ fun a b hab => ?_
  simp only [linPart, Matrix.of_apply]
  rw [hh _ _ hab]
  simp only [Matrix.one_apply, Subtype.ext_iff, Prod.ext_iff]
  by_cases h1 : a.1.1 = b.1.1 <;> by_cases h2 : a.1.2 = b.1.2 <;> simp [h1, h2]

open Classical in
theorem linPart_mulVec (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    (linPart p h).mulVec e a =
      ∑ r', h a.1.1 r' * (if hf : Free p (r', a.1.2) then e ⟨(r', a.1.2), hf⟩ else 0) := by
  let F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun b =>
    (if a.1.2 = b.2 then h a.1.1 b.1 else 0) * (if hf : Free p b then e ⟨b, hf⟩ else 0)
  have h1 : (linPart p h).mulVec e a = ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 := by
    simp only [Matrix.mulVec, dotProduct, linPart, Matrix.of_apply, F]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dif_pos b.2]
  have h2 : ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 = ∑ b, F b := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun b => Free p b) (by simp) F]
    refine Finset.sum_filter_of_ne fun b _ hb => ?_
    by_contra hf
    exact hb (by simp [F, hf])
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_eq_single a.1.2]
  · simp [F]
  · intro s _ hs
    simp [F, hs.symm]
  · simp

open Classical in
theorem mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    h.val * affPt p x₀ e = affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases hf : Free p (r, s)
  · have : affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) r s =
        basePt c x₀ r s + ((linPart p h.val).mulVec e ⟨(r, s), hf⟩ +
          (h.val * basePt c x₀ - basePt c x₀) r s) := by
      simp [affPt, hf]
    rw [this, linPart_mulVec, affPt, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    ring
  · rw [affPt_of_not_free _ _ _ hf, mul_apply_of_inN hh, affPt_of_not_free _ _ _ hf,
      Finset.sum_eq_zero, add_zero]
    intro r' _
    split_ifs with hl
    · rw [affPt_eq_zero p x₀ e hf hl, mul_zero]
    · rfl

omit [Fintype n'] [DecidableEq n'] in
theorem ch_mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (h.val * affPt p x₀ e) = ch (affPt p x₀ e) + simpleSum h := by
  rw [ch, ch, simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply_of_inN hh, Fintype.sum_sum_type, Finset.sum_eq_zero, zero_add]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : lev (n := n) p (Sum.inr i) < lev (n := n) p (Sum.inr j)
    · rw [if_pos hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rw [if_neg hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [if_neg (by omega)]
  · intro r _
    split_ifs with hl
    · simp only [lev, Sum.elim_inr, Sum.elim_inl] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rfl

end GlobalTheory.RootEx.TargetUnip

open GlobalTheory.RootEx.TargetUnip in

theorem GlobalTheory.RootEx.opE_om_target_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n c p, opE ψ ν p (om μ 1 g Φ) = (ψ (-simpleSum g) : ℂ) • opE ψ ν p Φ := by
  classical
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hg
  obtain ⟨hN, hadd, hdet, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p
  have hg' : g⁻¹ ∈ N k n c p := inv_mem hg
  have hh : InN p g⁻¹ := (hN _).1 hg'
  have hs1 : simpleSum (1 : GL (n ⊕ Fin c) k) = 0 := by
    have := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_add.1 this
  have hs : simpleSum g⁻¹ = -simpleSum g := by
    have := hadd g hg g⁻¹ hg'
    rw [mul_inv_cancel, hs1] at this
    linear_combination -this
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : ∀ x, om μ 1 g Φ x = Φ ((g⁻¹).val * x) := by
    intro x
    simp [om, hdet g hg, hn1]
  haveI := secondCountable k
  funext x₀
  let F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ := fun e =>
    Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)
  let t : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => ((g⁻¹).val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2
  let L := Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart (n' := n') p (g⁻¹).val)
    (by rw [det_linPart hh]; exact one_ne_zero)
  have hL : Matrix.GeneralLinearGroup.det L = 1 := by
    ext
    exact det_linPart hh
  have key : ∀ e, om μ 1 g Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (-simpleSum g) : ℂ) * F (L.val.mulVec e + t) := by
    intro e
    have h1 := mul_affPt hh x₀ e
    have h2 := ch_mul_affPt hh x₀ e
    have h3 : F (L.val.mulVec e + t) = Φ ((g⁻¹).val * affPt p x₀ e) *
        (ψ (-ch ((g⁻¹).val * affPt p x₀ e)) : ℂ) := by
      rw [h1]; rfl
    rw [h3, h2, hs, hom, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have hcov := integral_comp_mulVec_eq_smul ν L
    (fun e => F (e + t))
  rw [hL, hn1, inv_one, one_smul, integral_add_right_eq_self] at hcov
  simp only [opE, Pi.smul_apply, smul_eq_mul, key]
  rw [integral_const_mul, hcov]
