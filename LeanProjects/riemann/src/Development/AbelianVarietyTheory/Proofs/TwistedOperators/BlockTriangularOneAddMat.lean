import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantAddChar

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker

namespace GlobalTheory.SmGL.UnipHaar

section Algebra

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem det_of_blocks {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I R) (b : I → α)
    (hM : M.BlockTriangular b) (T : α → Type) [∀ a, Fintype (T a)] [∀ a, DecidableEq (T a)]
    (A : ∀ a, Matrix (m a) (m a) R) (φ : ∀ a, m a × T a ≃ {p // b p = a})
    (h : ∀ a x y, M (φ a x) (φ a y) = if x.2 = y.2 then A a x.1 y.1 else 0) :
    M.det = ∏ a, (A a).det ^ Fintype.card (T a) := by
  rw [hM.det_fintype]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← det_submatrix_equiv_self (φ a)]
  have : (M.toSquareBlock b a).submatrix (φ a) (φ a) = A a ⊗ₖ (1 : Matrix (T a) (T a) R) := by
    ext x y
    refine (h a x y).trans ?_
    simp [kroneckerMap_apply, one_apply]
  rw [this, det_kronecker]
  simp

abbrev Idx (e : (Σ a, m a) ≃ n) : Type := {p : n × n // blk e p.1 < blk e p.2}

variable (e : (Σ a, m a) ≃ n)

def ent (X : Matrix n n R) : Idx e → R := fun p => X p.1.1 p.1.2

def mat (x : Idx e → R) : Matrix n n R :=
  Matrix.of fun i j => if h : blk e i < blk e j then x ⟨(i, j), h⟩ else 0

def lmat (A : Matrix n n R) : Matrix (Idx e) (Idx e) R :=
  Matrix.of fun p q => if p.1.2 = q.1.2 then A p.1.1 q.1.1 else 0

def rmat (B : Matrix n n R) : Matrix (Idx e) (Idx e) R :=
  Matrix.of fun p q => if p.1.1 = q.1.1 then B q.1.2 p.1.2 else 0

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] in
theorem ent_mat (x : Idx e → R) : ent e (mat e x) = x := by
  funext p
  simp [ent, mat, p.2]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem ent_one_add (X : Matrix n n R) : ent e (1 + X) = ent e X := by
  funext p
  have : p.1.1 ≠ p.1.2 := fun h => p.2.ne (by rw [h])
  simp [ent, this]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [DecidableEq n] in
theorem sum_idx (f : n → n → R) (x : Idx e → R) :
    ∑ q : Idx e, f q.1.1 q.1.2 * x q = ∑ i, ∑ j, f i j * mat e x i j := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : n × n => blk e p.1 < blk e p.2), Finset.sum_eq_zero (s := Finset.filter (fun p => ¬ _) _), add_zero,
    Finset.sum_subtype (p := fun p : n × n => blk e p.1 < blk e p.2) _ (by simp)]
  · exact Finset.sum_congr rfl fun q _ => by simp [mat, q.2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [mat, hp]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem ent_mul_mat (A : Matrix n n R) (x : Idx e → R) :
    ent e (A * mat e x) = (lmat e A).mulVec x := by
  funext p
  refine Eq.trans ?_ (sum_idx e (fun i j => if p.1.2 = j then A p.1.1 i else 0) x).symm
  simp [ent, mul_apply]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem ent_mat_mul (B : Matrix n n R) (x : Idx e → R) :
    ent e (mat e x * B) = (rmat e B).mulVec x := by
  funext p
  refine Eq.trans ?_ (sum_idx e (fun i j => if p.1.1 = i then B j p.1.2 else 0) x).symm
  rw [Finset.sum_comm]
  simp [ent, mul_apply, mul_comm]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem mul_mat {A : Matrix n n R} (hA : A.BlockTriangular (blk e)) (x : Idx e → R) :
    A * mat e x = mat e ((lmat e A).mulVec x) := by
  rw [← ent_mul_mat]
  ext i j
  by_cases h : blk e i < blk e j
  · simp [mat, h, ent]
  · simp only [mat, of_apply, h, dif_neg, not_false_eq_true, mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h' : blk e l < blk e j
    · rw [hA (h'.trans_le (not_lt.1 h)), zero_mul]
    · simp [h']

theorem eq_one_add_mat {u : GL n R} (hu : u ∈ unipRad R e) :
    (u : Matrix n n R) = 1 + mat e (ent e (u : Matrix n n R)) := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  rcases lt_trichotomy a b with h | rfl | h
  · simp [mat, ent, h, one_apply, h.ne]
  · simp [mat, h2, one_apply]
  · simp [mat, h.not_gt, one_apply, h.ne', mem_parab_iff.1 h1 a b i j h]

omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] in
theorem blockTriangular_one_add_mat (x : Idx e → R) : (1 + mat e x).BlockTriangular (blk e) :=
  blockTriangular_one.add fun i j h => by simp [mat, h.not_gt]

omit [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem det_one_add_mat (x : Idx e → R) : (1 + mat e x).det = 1 := by
  rw [(blockTriangular_one_add_mat e x).det_fintype]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (1 + mat e x).toSquareBlock (blk e) a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [toSquareBlock_def, mat, hi, hj, one_apply]
  rw [this, det_one]

def unipEquiv : unipRad R e ≃ (Idx e → R) where
  toFun u := ent e ((u : GL n R) : Matrix n n R)
  invFun x := ⟨GeneralLinearGroup.mk'' (1 + mat e x) (by rw [det_one_add_mat]; exact isUnit_one),
    mem_unipRad.2 ⟨blockTriangular_one_add_mat e x, fun a i j => by
      show (1 + mat e x) _ _ = _
      simp [mat, one_apply]⟩⟩
  left_inv u := Subtype.ext (Units.ext (eq_one_add_mat e u.2).symm)
  right_inv x := (ent_one_add e _).trans (ent_mat e x)

theorem val_unipEquiv_symm (x : Idx e → R) :
    ((((unipEquiv e).symm x : unipRad R e) : GL n R) : Matrix n n R) = 1 + mat e x := rfl

omit [LinearOrder α] [∀ a, DecidableEq (m a)] [DecidableEq n] in
theorem card_blk (p : α → Prop) [DecidablePred p] :
    Fintype.card {j : n // p (blk e j)} = ∑ b with p b, Fintype.card (m b) := by
  rw [Fintype.card_subtype, Finset.card_filter, ← e.sum_comp, Fintype.sum_sigma, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : p b <;> simp [h]

def rowEquiv (a : α) : m a × {j : n // a < blk e j} ≃ {p : Idx e // blk e p.1.1 = a} :=
  Equiv.ofBijective (fun x => ⟨⟨(e ⟨a, x.1⟩, x.2.1), by simpa using x.2.2⟩, by simp⟩) ⟨by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simpa [Subtype.ext_iff] using h, by
    rintro ⟨⟨⟨i, j⟩, h⟩, hi⟩
    obtain ⟨⟨b, i⟩, rfl⟩ := e.surjective i
    obtain rfl : b = a := by simpa using hi
    exact ⟨(i, ⟨j, by simpa using h⟩), rfl⟩⟩

def colEquiv (a : α) : m a × {j : n // blk e j < a} ≃ {p : Idx e // blk e p.1.2 = a} :=
  Equiv.ofBijective (fun x => ⟨⟨(x.2.1, e ⟨a, x.1⟩), by simpa using x.2.2⟩, by simp⟩) ⟨by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simpa [Subtype.ext_iff, and_comm] using h, by
    rintro ⟨⟨⟨i, j⟩, h⟩, hi⟩
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    obtain rfl : b = a := by simpa using hi
    exact ⟨(j, ⟨i, by simpa using h⟩), rfl⟩⟩

theorem det_lmat {A : Matrix n n R} (hA : A.BlockTriangular (blk e)) (D : ∀ a, Matrix (m a) (m a) R)
    (hD : ∀ a i j, A (e ⟨a, i⟩) (e ⟨a, j⟩) = D a i j) :
    (lmat e A).det = ∏ a, (D a).det ^ ∑ b with a < b, Fintype.card (m b) := by
  rw [det_of_blocks (lmat e A) (fun p => blk e p.1.1) ?_ (fun a => {j : n // a < blk e j}) D
    (rowEquiv e) ?_]
  · simp only [card_blk]
  · intro p q h
    simp [lmat, hA h]
  · intro a x y
    exact if_congr Subtype.ext_iff.symm (hD a x.1 y.1) rfl

theorem det_rmat (g : Levi R m) :
    (rmat e (leviEmb R e g : Matrix n n R)).det =
      ∏ a, (g a : Matrix (m a) (m a) R).det ^ ∑ b with b < a, Fintype.card (m b) := by
  rw [det_of_blocks (rmat e _) (fun p => blk e p.1.2) ?_ (fun a => {j : n // blk e j < a})
    (fun a => (g a : Matrix (m a) (m a) R)ᵀ) (colEquiv e) ?_]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [card_blk e (· < a), det_transpose]
  · rintro ⟨⟨i, j⟩, _⟩ ⟨⟨i', j'⟩, _⟩ h
    obtain ⟨⟨a, j⟩, rfl⟩ := e.surjective j
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j'
    have : b < a := by simpa using h
    simp [rmat, leviEmb_apply_ne R e g this.ne]
  · intro a x y
    exact if_congr Subtype.ext_iff.symm (leviEmb_apply_same R e g a y.1 x.1) rfl

theorem unipEquiv_mul (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e (u * (unipEquiv e).symm x) =
      unipEquiv e u + (lmat e ((u : GL n R) : Matrix n n R)).mulVec x := by
  rw [← ent_mul_mat]
  show ent e (((u : GL n R) : Matrix n n R) * (1 + mat e x)) = _
  rw [mul_add, mul_one]
  rfl

theorem det_lmat_unip (u : unipRad R e) : (lmat e ((u : GL n R) : Matrix n n R)).det = 1 := by
  rw [det_lmat e (mem_unipRad.1 u.2).1 (fun _ => 1) (mem_unipRad.1 u.2).2]
  simp

def conj (g : Levi R m) (u : unipRad R e) : unipRad R e :=
  ⟨leviEmb R e g * u * (leviEmb R e g)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer R e g) _).1 u.2⟩

def cmat (g : Levi R m) : Matrix (Idx e) (Idx e) R :=
  rmat e (leviEmb R e g⁻¹ : Matrix n n R) * lmat e (leviEmb R e g : Matrix n n R)

theorem unipEquiv_conj (g : Levi R m) (x : Idx e → R) :
    unipEquiv e (conj e g ((unipEquiv e).symm x)) = (cmat e g).mulVec x := by
  rw [cmat, ← mulVec_mulVec, ← ent_mat_mul, ← mul_mat e (leviEmb_mem_parab R e g), map_inv,
    ← ent_one_add e (_ * _ * _)]
  show ent e ((leviEmb R e g : Matrix n n R) * (1 + mat e x) * ((leviEmb R e g)⁻¹ : GL n R).val) = _
  rw [mul_add, mul_one, add_mul, Units.mul_inv]

theorem det_cmat (g : Levi R m) :
    ((∏ a, GeneralLinearGroup.det (g a) ^ modExp m a : Rˣ) : R) = (cmat e g).det := by
  rw [cmat, det_mul, det_rmat, det_lmat e (leviEmb_mem_parab R e g) _ (leviEmb_apply_same R e g),
    ← Finset.prod_mul_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp, ← Nat.cast_sum, ← Nat.cast_sum, sub_eq_neg_add, _root_.zpow_add, _root_.zpow_neg,
    ← _root_.inv_zpow, zpow_natCast, zpow_natCast, ← map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val]
  rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

def unipHomeo : unipRad R e ≃ₜ (Idx e → R) where
  toEquiv := unipEquiv e
  continuous_toFun := continuous_pi fun p =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem p.1.1 p.1.2
  continuous_invFun := by
    have h : Continuous fun x : Idx e → R => 1 + mat e x := by
      refine continuous_const.add (continuous_matrix fun i j => ?_)
      by_cases h : blk e i < blk e j
      · simp only [mat, of_apply, h, dif_pos]
        exact continuous_apply _
      · simp only [mat, of_apply, h, dif_neg, not_false_eq_true]
        exact continuous_const
    refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨h, h.matrix_adjugate.congr fun x => ?_⟩) _
    rw [Matrix.coe_units_inv, Matrix.inv_def]
    show _ = Ring.inverse (1 + mat e x).det • (1 + mat e x).adjugate
    rw [det_one_add_mat, Ring.inverse_one, one_smul]

theorem continuous_conj (g : Levi R m) : Continuous (conj e g) :=
  Continuous.subtype_mk (by fun_prop) _

end Algebra

section Measure

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isHaarMeasure_map :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)) :=
    Measure.IsFiniteMeasureOnCompacts.map _ _
  haveI : (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)).IsOpenPosMeasure :=
    (unipHomeo e).symm.continuous.isOpenPosMeasure_map (unipHomeo e).symm.surjective
  haveI : (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)).IsMulLeftInvariant := by
    refine ⟨fun u => ?_⟩
    have hm : Measurable (lmat e ((u : GL n k) : Matrix n n k)).mulVec :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_lmat_unip e u).symm
    rw [map_one, ENNReal.coe_one, one_smul] at h1
    have h2 : (u * ·) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
        (lmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
      funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_mul e u x)
    rw [Measure.map_map (measurable_const_mul u) hΦ, h2,
      ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
      ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]
  exact {}

theorem map_preimage_conj (g : Levi k m) {T : Set (unipRad k e)} (hT : MeasurableSet T) :
    Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν) T = ENNReal.ofReal (modulus k m g) *
      Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν) (conj e g ⁻¹' T) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  have hm : Measurable (cmat e g).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ _ (det_cmat e g)
  have h2 : conj e g ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ (cmat e g).mulVec :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_conj e g x)
  have hc := (continuous_conj e g).measurable
  rw [← Measure.map_apply hc hT, Measure.map_map hc hΦ, h2, ← Measure.map_map hΦ hm]
  conv_lhs => rw [← h1, Measure.map_smul, Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  simp [modulus, nabs]

end Measure

theorem haar_conj_eq_modulus_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure] (g : Levi k m) (S : Set (unipRad k e)), MeasurableSet S → μ {u | ∃ s ∈ S, (u : GL n k) = leviEmb k e g * (s : GL n k) * (leviEmb k e g)⁻¹} = ENNReal.ofReal (modulus k m g) * μ S := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _ g S hS
  borelize k
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI := isHaarMeasure_map e (Measure.addHaar : Measure k)
  have h1 : {u : unipRad k e | ∃ s ∈ S, (u : GL n k) = leviEmb k e g * (s : GL n k) * (leviEmb k e g)⁻¹} =
      conj e g⁻¹ ⁻¹' S := by
    ext u
    refine ⟨?_, fun h => ⟨_, h, by simp [conj, mul_assoc]⟩⟩
    rintro ⟨s, hs, h⟩
    have : conj e g⁻¹ u = s := Subtype.ext (by simp [conj, h, mul_assoc])
    rwa [Set.mem_preimage, this]
  have h2 : conj e g ⁻¹' (conj e g⁻¹ ⁻¹' S) = S := by
    ext u
    have : conj e g⁻¹ (conj e g u) = u := Subtype.ext (by simp [conj, mul_assoc])
    rw [Set.mem_preimage, Set.mem_preimage, this]
  have h3 := map_preimage_conj e (Measure.addHaar : Measure k) g
    ((continuous_conj e g⁻¹).measurable hS)
  rw [h2] at h3
  rw [h1, Measure.isMulLeftInvariant_eq_smul μ
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => (Measure.addHaar : Measure k))),
    Measure.smul_apply, Measure.smul_apply, h3, mul_smul_comm]

end GlobalTheory.SmGL.UnipHaar
