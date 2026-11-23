import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndepOfGqNeZero
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMassConst
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Tri

variable {m : ℕ} {u v : Matrix (Fin m) (Fin m) E}

theorem up_tri (h : IsUp u) : u.BlockTriangular id := fun i j hij => (h i j).1 hij

theorem mul_diag (hu : u.BlockTriangular id) (hv : v.BlockTriangular id) (i : Fin m) :
    (u * v) i i = u i i * v i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i _ (by simp)]
  intro k _ hk
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hu h, zero_mul]
  · rw [hv h, mul_zero]

theorem up_one : IsUp (1 : Matrix (Fin m) (Fin m) E) :=
  fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem up_mul (hu : IsUp u) (hv : IsUp v) : IsUp (u * v) := fun i j =>
  ⟨fun h => (up_tri hu).mul (up_tri hv) h, fun h => by
    subst h; rw [mul_diag (up_tri hu) (up_tri hv), (hu i i).2 rfl, (hv i i).2 rfl, one_mul]⟩

theorem up_det (hu : IsUp u) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular (up_tri hu)]
  exact Finset.prod_eq_one fun i _ => (hu i i).2 rfl

theorem up_mul_inv (hu : IsUp u) : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by simp [up_det hu])

theorem up_inv_mul (hu : IsUp u) : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul _ (by simp [up_det hu])

theorem up_inv (hu : IsUp u) : IsUp u⁻¹ := by
  letI := u.invertibleOfIsUnitDet (by simp [up_det hu])
  have h := Matrix.blockTriangular_inv_of_blockTriangular (up_tri hu)
  refine fun i j => ⟨fun hij => h hij, fun e => ?_⟩
  subst e
  have := mul_diag (up_tri hu) h i
  rw [up_mul_inv hu, (hu i i).2 rfl, one_mul, Matrix.one_apply_eq] at this
  exact this.symm

theorem lo_cT (σ : E →+* E) (hu : IsUp u) : IsLo (cT σ u) := fun i j =>
  ⟨fun h => by simp [cT, (hu j i).1 h], fun h => by simp [cT, (hu j i).2 h.symm]⟩

theorem lo_mul (hu : IsLo u) (hv : IsLo v) : IsLo (u * v) := by
  have t {w : Matrix (Fin m) (Fin m) E} (h : IsLo w) : IsUp wᵀ :=
    fun i j => ⟨(h j i).1, fun e => (h j i).2 e.symm⟩
  have := up_mul (t hv) (t hu)
  rw [← Matrix.transpose_mul] at this
  exact fun i j => ⟨(this j i).1, fun e => (this j i).2 e.symm⟩

theorem lo_det (hu : IsLo u) : u.det = 1 := by
  rw [← Matrix.det_transpose]
  exact up_det fun i j => ⟨(hu j i).1, fun e => (hu j i).2 e.symm⟩

theorem lead_block_mul (Z : Matrix (Fin m) (Fin m) E) (hu : IsUp u) {l : ℕ} (hl : l ≤ m) :
    (Z * u).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * u.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) (Fin.castLE_injective hl).injOn (by simp) ?_ (by simp)
  intro k _ hk
  have : Fin.castLE hl j < k := by
    by_contra h
    exact hk ⟨⟨k, by have := j.2; simp [Fin.lt_def] at h; omega⟩, by simp, rfl⟩
  rw [(hu k _).1 this, mul_zero]

theorem lead_mul_up (Z : Matrix (Fin m) (Fin m) E) (hu : IsUp u) (l : ℕ) (hl : l ≤ m) :
    SgAlg.lead (Z * u) l hl = SgAlg.lead Z l hl := by
  rw [SgAlg.lead, lead_block_mul Z hu, Matrix.det_mul,
    up_det (u := u.submatrix (Fin.castLE hl) (Fin.castLE hl)) fun i j => ⟨fun h => (hu _ _).1 h, fun h => (hu _ _).2 (congrArg _ h)⟩, mul_one,
    SgAlg.lead]

theorem lead_lo_mul (Z : Matrix (Fin m) (Fin m) E) (hu : IsLo u) (l : ℕ) (hl : l ≤ m) :
    SgAlg.lead (u * Z) l hl = SgAlg.lead Z l hl := by
  have t (W : Matrix (Fin m) (Fin m) E) : SgAlg.lead Wᵀ l hl = SgAlg.lead W l hl := by
    rw [SgAlg.lead, SgAlg.lead, ← Matrix.det_transpose]; rfl
  rw [← t, Matrix.transpose_mul, lead_mul_up (u := uᵀ) _ (fun i j => ⟨(hu j i).1, fun e => (hu j i).2 e.symm⟩), t]

def IsStrict (A : Matrix (Fin m) (Fin m) E) : Prop := ∀ i j, j ≤ i → A i j = 0

def simpleSum {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := ∑ a : Fin r, A a.castSucc a.succ

theorem strict_conj {r : ℕ} {u v A : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hu : IsUp u) (hv : IsUp v)
    (hA : IsStrict A) : IsStrict (v * A * u) ∧ simpleSum (v * A * u) = simpleSum A := by
  have h1 : IsStrict (v * A) := fun i j h => by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [(hv i k).1 hk, zero_mul]
    · rw [hA k j (h.trans hk), mul_zero]
  have h2 (a : Fin r) : (v * A) a.castSucc a.succ = A a.castSucc a.succ := by
    rw [Matrix.mul_apply, Finset.sum_eq_single a.castSucc _ (by simp), (hv _ _).2 rfl, one_mul]
    intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hv _ k).1 h, zero_mul]
    · rw [hA k _ (Fin.castSucc_lt_iff_succ_le.1 h), mul_zero]
  refine ⟨fun i j h => ?_, Finset.sum_congr rfl fun a _ => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge j k with hk | hk
    · rw [(hu k j).1 hk, mul_zero]
    · rw [h1 i k (hk.trans h), zero_mul]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a.succ _ (by simp), (hu _ _).2 rfl, mul_one, h2]
    intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [h1 _ k (Fin.le_castSucc_iff.2 h), zero_mul]
    · rw [(hu k _).1 h, mul_zero]

end Tri

section Frames

variable {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

theorem cT_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    cT σ (A * B) = cT σ B * cT σ A := by rw [cT, Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem pairM_isom (hs : IsUn σ J s) : pairM σ J (s * P') (s * P) = pairM σ J P' P := by
  rw [pairM, pairM, cT_mul]
  conv_rhs => rw [← hs]
  simp only [Matrix.mul_assoc]

theorem pairM_mul (u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    pairM σ J (P' * u) (P * v) = cT σ v * pairM σ J P' P * u := by
  rw [pairM, pairM, cT_mul]
  simp only [Matrix.mul_assoc]

theorem eOf_mul (hu : IsUp u) : eOf (P * u) = eOf P * u.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [eOf, Matrix.submatrix_apply, Matrix.mul_apply, id, Fin.sum_univ_castSucc]
  rw [(hu _ _).1 (Fin.castSucc_lt_last j), mul_zero, add_zero]

theorem up_block (hu : IsUp u) : IsUp (u.submatrix Fin.castSucc Fin.castSucc) :=
  fun _ _ => ⟨fun h => (hu _ _).1 h, fun h => (hu _ _).2 (congrArg _ h)⟩

theorem spanX_mul (hu : IsUp u) : spanX (P * u) = spanX P := by
  have k {Q : Matrix (Fin n) (Fin (r + 1)) E} {w : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hw : IsUp w) :
      spanX (Q * w) ≤ spanX Q := by
    rintro _ ⟨c, rfl⟩
    exact ⟨w.submatrix Fin.castSucc Fin.castSucc *ᵥ c, by simp [eOf_mul hw]⟩
  refine le_antisymm (k hu) ?_
  simpa [Matrix.mul_assoc, up_mul_inv hu] using k (Q := P * u) (up_inv hu)

theorem perpX_mul (hu : IsUp u) : perpX σ J (P * u) = perpX σ J P := by
  have k {Q : Matrix (Fin n) (Fin (r + 1)) E} {w : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hw : IsUp w) :
      perpX σ J Q ≤ perpX σ J (Q * w) := by
    intro x hx
    rw [mem_perpX] at hx ⊢
    rw [eOf_mul hw, cT_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  refine le_antisymm ?_ (k hu)
  simpa [Matrix.mul_assoc, up_mul_inv hu] using k (Q := P * u) (up_inv hu)

theorem mulVec_mem_spanX {x : Fin n → E} (hx : x ∈ spanX P) : s *ᵥ x ∈ spanX (s * P) := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c, (Matrix.mulVec_mulVec c s (eOf P)).symm⟩

theorem isFrame_mul {T : E} (h : IsFrame σ J T P) (hu : IsUp u) : IsFrame σ J T (P * u) := by
  obtain ⟨⟨L, hL⟩, h2⟩ := h
  refine ⟨⟨u⁻¹ * L, by rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, hL, Matrix.one_mul, up_inv_mul hu]⟩, ?_⟩
  rw [pairM_mul, h2]
  ext a b
  have e (c : Fin (r + 1)) : u (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
    split_ifs with h
    · exact (hu _ _).2 h.symm
    · exact (hu _ _).1 (Fin.lt_last_iff_ne_last.2 h)
  simp only [TF, Matrix.mul_apply, Matrix.diagonal_apply, cT, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r) (fun k _ hk => by simp [hk]) (by simp)]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, e]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb, eq_comm]

theorem isFrame_isom (hJ : IsUnit J.det) {T : E} (h : IsFrame σ J T P) (hs : IsUn σ J s) :
    IsFrame σ J T (s * P) := by
  obtain ⟨⟨L, hL⟩, h2⟩ := h
  refine ⟨⟨L * s⁻¹, ?_⟩, by rw [pairM_isom hs, h2]⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc s⁻¹, Matrix.nonsing_inv_mul _ (isUnit_det_of_isUn hJ hs),
    Matrix.one_mul, hL]

theorem isUn_inv (hJ : IsUnit J.det) (hs : IsUn σ J s) : IsUn σ J s⁻¹ :=
  isUn_of_mul_eq_one hs (Matrix.mul_nonsing_inv _ (isUnit_det_of_isUn hJ hs))

theorem inS_iff : InS σ J P s ↔ IsUn σ J s ∧
    ∃ a : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUp a ∧ s * P = P * a := Iff.rfl

theorem inN_iff : InN σ J P s ↔ IsUn σ J s ∧ (∃ a : Matrix (Fin r) (Fin r) E, IsUp a ∧ s * eOf P = eOf P * a) ∧
    ∀ x ∈ perpX σ J P, ∃ c, s *ᵥ x - x = eOf P *ᵥ c := Iff.rfl

theorem inS_one : InS σ J P 1 := inS_iff.2 ⟨isUn_one, 1, up_one, by simp⟩

theorem inS_mul {t : Matrix (Fin n) (Fin n) E} (hs : InS σ J P s) (ht : InS σ J P t) : InS σ J P (s * t) := by
  obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
  obtain ⟨h2, b, hb, f⟩ := inS_iff.1 ht
  exact inS_iff.2 ⟨isUn_mul h1 h2, a * b, up_mul ha hb, by
    rw [Matrix.mul_assoc, f, ← Matrix.mul_assoc, e, Matrix.mul_assoc]⟩

theorem inS_inv (hJ : IsUnit J.det) (hs : InS σ J P s) : InS σ J P s⁻¹ := by
  obtain ⟨h1, a, ha, e⟩ := inS_iff.1 hs
  refine inS_iff.2 ⟨isUn_inv hJ h1, a⁻¹, up_inv ha, ?_⟩
  have : P = s * (P * a⁻¹) := by rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, up_mul_inv ha, Matrix.mul_one]
  conv_lhs => rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_isUn hJ h1), Matrix.one_mul]

theorem inS_of_inN {T : E} (hP : IsFrame σ J T P) (hs : InN σ J P s) : InS σ J P s := by
  obtain ⟨h1, ⟨a, ha, e⟩, h3⟩ := inN_iff.1 hs
  obtain ⟨c, hc⟩ := h3 _ (zOf_mem_perpX hP)
  refine inS_iff.2 ⟨h1, Matrix.of fun i j => Fin.lastCases (motive := fun _ => E)
    (Fin.lastCases (motive := fun _ => E) 1 c i)
    (fun j => Fin.lastCases (motive := fun _ => E) 0 (fun i => a i j) i) j, fun i j => ?_, ?_⟩
  · induction j using Fin.lastCases <;> induction i using Fin.lastCases
    · simp
    · simp [(Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).le]
    · simp [(Fin.castSucc_lt_last _).ne']
    · simpa using ha _ _
  · ext i j
    induction j using Fin.lastCases
    · have := congrFun hc i
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, zOf, eOf, Matrix.submatrix_apply, id] at this
      simp only [Matrix.mul_apply, Matrix.of_apply, Fin.lastCases_last, Fin.sum_univ_castSucc,
        Fin.lastCases_castSucc, mul_one]
      rw [← this]; ring
    · have := congrFun (congrFun e i) ‹_›
      simpa [Matrix.mul_apply, Fin.sum_univ_castSucc, eOf] using this

theorem inN_one : InN σ J P 1 := inN_iff.2 ⟨isUn_one, ⟨1, up_one, by simp⟩, fun v _ => ⟨0, by simp⟩⟩

theorem inN_perp (hs : InN σ J P s) (x : Fin n → E) : s *ᵥ x ∈ perpX σ J P ↔ x ∈ perpX σ J P := by
  obtain ⟨h1, ⟨a, ha, e⟩, -⟩ := inN_iff.1 hs
  rw [← mulVec_mem_perpX h1 P x, mem_perpX, mem_perpX, show eOf (s * P) = s * eOf P from rfl, e, cT_mul,
    Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (cT σ a)]
  have hu : IsUnit (cT σ a) := (Matrix.isUnit_iff_isUnit_det _).2 (by simp [lo_det (lo_cT σ ha)])
  exact ⟨fun h => by rw [h, Matrix.mulVec_zero],
    fun h => Matrix.mulVec_injective_iff_isUnit.2 hu (h.trans (Matrix.mulVec_zero _).symm)⟩

theorem inN_mul {t : Matrix (Fin n) (Fin n) E} (hs : InN σ J P s) (ht : InN σ J P t) : InN σ J P (s * t) := by
  have k := inN_perp ht
  obtain ⟨h1, ⟨a, ha, e⟩, h3⟩ := inN_iff.1 hs
  obtain ⟨h2, ⟨b, hb, f⟩, h4⟩ := inN_iff.1 ht
  refine inN_iff.2 ⟨isUn_mul h1 h2, ⟨a * b, up_mul ha hb, by
    rw [Matrix.mul_assoc, f, ← Matrix.mul_assoc, e, Matrix.mul_assoc]⟩, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := h3 _ ((k x).2 hx)
  obtain ⟨d, hd⟩ := h4 _ hx
  exact ⟨c + d, by rw [Matrix.mulVec_add, ← hc, ← hd, Matrix.mulVec_mulVec]; abel⟩

theorem inN_inv (hJ : IsUnit J.det) (hs : InN σ J P s) : InN σ J P s⁻¹ := by
  have k := inN_perp hs
  obtain ⟨h1, ⟨a, ha, e⟩, h3⟩ := inN_iff.1 hs
  have hu := isUnit_det_of_isUn hJ h1
  refine inN_iff.2 ⟨isUn_inv hJ h1, ⟨a⁻¹, up_inv ha, ?_⟩, fun x hx => ?_⟩
  · have : eOf P = s * (eOf P * a⁻¹) := by
      rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, up_mul_inv ha, Matrix.mul_one]
    conv_lhs => rw [this, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  · have e1 : s *ᵥ (s⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    obtain ⟨c, hc⟩ := h3 _ ((k (s⁻¹ *ᵥ x)).1 (by rwa [e1]))
    exact ⟨-c, by rw [Matrix.mulVec_neg, ← hc, e1]; abel⟩

end Frames

section Lattices

variable [NumberField E] {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ M : Submodule (𝓞 E) (Fin n → E)}

def triRing (E : Type) [Field E] [NumberField E] (r : ℕ) : Subring (Matrix (Fin (r + 1)) (Fin (r + 1)) E) where
  carrier := {u | ∀ a b : Fin (r + 1), (b < a → u a b = 0) ∧ u a b ∈ dInv E ((b : ℕ) - a)}
  one_mem' := fun a b => ⟨(one_mem_UO.1 a b).1, UO.entry_mem one_mem_UO a b⟩
  zero_mem' := fun _ _ => ⟨fun _ => rfl, FractionalIdeal.zero_mem _⟩
  add_mem' := fun hu hv a b => ⟨fun h => by simp [(hu a b).1 h, (hv a b).1 h],
    Submodule.add_mem (dInv E _ : Submodule (𝓞 E) E) (hu a b).2 (hv a b).2⟩
  neg_mem' := fun hu a b => ⟨fun h => by simp [(hu a b).1 h],
    Submodule.neg_mem (dInv E _ : Submodule (𝓞 E) E) (hu a b).2⟩
  mul_mem' := fun {u v} hu hv a b => ⟨fun h =>
    Matrix.BlockTriangular.mul (b := id) (fun i j k => (hu i j).1 k) (fun i j k => (hv i j).1 k) h, by
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem (dInv E _ : Submodule (𝓞 E) E) fun k _ => ?_
    rcases lt_or_ge k a with h1 | h1
    · rw [(hu a k).1 h1, zero_mul]; exact Submodule.zero_mem _
    rcases lt_or_ge b k with h2 | h2
    · rw [(hv k b).1 h2, mul_zero]; exact Submodule.zero_mem _
    have h3 : (a : ℕ) ≤ k := h1
    have h4 : (k : ℕ) ≤ b := h2
    rw [show (b : ℕ) - a = ((k : ℕ) - a) + ((b : ℕ) - k) by omega]
    exact mul_mem_dInv (hu a k).2 (hv k b).2⟩

theorem mem_UO_iff : u ∈ UO E r ↔ IsUp u ∧ u ∈ triRing E r :=
  ⟨fun h => ⟨h.1, fun a b => ⟨(h.1 a b).1, UO.entry_mem h a b⟩⟩, fun h => ⟨h.1, fun a b _ => (h.2 a b).2⟩⟩

theorem UO_mul (hu : u ∈ UO E r) (hv : v ∈ UO E r) : u * v ∈ UO E r :=
  mem_UO_iff.2 ⟨up_mul hu.1 hv.1, mul_mem (mem_UO_iff.1 hu).2 (mem_UO_iff.1 hv).2⟩

theorem UO_inv (hu : u ∈ UO E r) : u⁻¹ ∈ UO E r := by
  refine mem_UO_iff.2 ⟨up_inv hu.1, ?_⟩
  have h := Matrix.aeval_self_charpoly (1 - u)
  rw [Matrix.charpoly_of_upperTriangular _ ((up_tri up_one).sub (up_tri hu.1))] at h
  have e (i : Fin (r + 1)) : (1 - u) i i = 0 := by simp [(hu.1 i i).2 rfl]
  simp only [e, map_zero, sub_zero, Finset.prod_const, map_pow, Polynomial.aeval_X] at h
  have k := mul_neg_geom_sum (1 - u) (Finset.univ : Finset (Fin (r + 1))).card
  rw [h, sub_sub_cancel, sub_zero] at k
  rw [Matrix.inv_eq_right_inv k]
  exact sum_mem fun i _ => pow_mem (sub_mem (one_mem _) (mem_UO_iff.1 hu).2) i

theorem frameLat_mul (hu : u ∈ UO E r) : frameLat (P * u) = frameLat P :=
  le_antisymm (frameLat_mul_le P hu) (by
    simpa [Matrix.mul_assoc, up_mul_inv hu.1] using frameLat_mul_le (P * u) (UO_inv hu))

theorem mem_UO_of_le (hP : Free P) (hu : IsUp u) (h : frameLat (P * u) ≤ frameLat P) : u ∈ UO E r := by
  obtain ⟨L, hL⟩ := hP
  refine ⟨hu, fun a b hab => ?_⟩
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have hne (j : ℕ) : dInv E j ≠ 0 := fun e => by
    simpa [e] using Iota.one_mem_dInv (E := E) j
  have hI : dInv E ((b : ℕ) - a) = dInv E (r - a) / dInv E (r - b) := by
    rw [eq_div_iff (hne _), dInv, dInv, dInv, ← pow_add]
    congr 1; omega
  rw [hI, FractionalIdeal.mem_div_iff_of_ne_zero (hne _)]
  intro t ht
  obtain ⟨c, hc, e⟩ := (Iota.mem_frameLat _ _).1 (h ((Iota.mem_frameLat _ _).2 ⟨Pi.single b t, fun k => by
    rcases eq_or_ne k b with rfl | hk
    · simpa using ht
    · simp [hk, FractionalIdeal.zero_mem], rfl⟩))
  have e2 := congrArg (L *ᵥ ·) e
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.one_mulVec] at e2
  have := hc a
  rw [e2] at this
  simpa [mul_comm] using this

theorem frameLat_isom (s : Matrix (Fin n) (Fin n) E) : frameLat (s * P) = latMap s (frameLat P) := by
  ext x
  simp only [mem_latMap, Iota.mem_frameLat]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨_, ⟨a, ha, rfl⟩, by rw [Matrix.mulVec_mulVec, e]⟩,
    fun ⟨_, ⟨a, ha, rfl⟩, e⟩ => ⟨a, ha, by rw [← e, Matrix.mulVec_mulVec]⟩⟩

omit [NumberField E] in

theorem mulVec_mem_latMap (hs : IsUnit s.det) (x : Fin n → E) : s *ᵥ x ∈ latMap s M ↔ x ∈ M :=
  ⟨fun ⟨w, hw, e⟩ => Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs) e ▸ hw,
    fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in

theorem mulVec_mem_span (hs : IsUnit s.det) (x : Fin n → E) :
    s *ᵥ x ∈ Submodule.span E (latMap s M : Set (Fin n → E)) ↔ x ∈ Submodule.span E (M : Set (Fin n → E)) := by
  have e : Submodule.span E (latMap s M : Set (Fin n → E)) =
      (Submodule.span E (M : Set (Fin n → E))).map s.mulVecLin := by
    rw [Submodule.map_span]; rfl
  rw [e]
  exact ⟨fun ⟨w, hw, e⟩ => Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs) e ▸ hw,
    fun h => ⟨x, h, rfl⟩⟩

omit [NumberField E] in

theorem primIn_latMap (hs : IsUnit s.det) : PrimIn (latMap s M) (latMap s Λ) ↔ PrimIn M Λ := by
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hs)
  simp only [PrimIn, SetLike.le_def]
  refine and_congr (hsur.forall.trans ?_) (hsur.forall.trans ?_) <;>
    simp only [mulVec_mem_latMap hs, mulVec_mem_span hs]

omit [NumberField E] in

theorem selfDual_latMap (hJ : IsUnit J.det) (hs : IsUn σ J s) (h : SelfDual σ J Λ) :
    SelfDual σ J (latMap s Λ) := by
  have hu := isUnit_det_of_isUn hJ hs
  have hsur := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu)
  refine ⟨h.1.map _, hsur.forall.2 fun x => ?_⟩
  rw [hsur.forall]
  simp only [mulVec_mem_latMap hu, form_mulVec hs]
  exact h.2 x

end Lattices

end GlobalTheory.IntTerm
