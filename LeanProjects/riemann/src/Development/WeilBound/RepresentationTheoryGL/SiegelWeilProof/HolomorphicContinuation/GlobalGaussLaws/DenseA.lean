import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseD

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem ext_mR {x y : GR n} (h : mR x = mR y) : x = y := Subtype.ext (Units.ext h)

theorem mR_mul (x y : GR n) : mR (x * y) = mR x * mR y := rfl

theorem mR_inv (x : GR n) : mR x⁻¹ = (mR x)⁻¹ := by
  unfold mR
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]

theorem JJ_mul_JJ : JJ n * JJ n = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [JJ, Matrix.fromBlocks_multiply]

theorem inv_JJ : (JJ n)⁻¹ = -JJ n :=
  Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, JJ_mul_JJ, neg_neg])

theorem inv_nU (x : Matrix (Fin n) (Fin n) ℂ) : (nU x)⁻¹ = nU (-x) :=
  Matrix.inv_eq_left_inv (by unfold nU; simp [Matrix.fromBlocks_multiply])

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  unfold InG nU JJ
  rw [Matrix.fromBlocks_conjTranspose]
  simp [Matrix.fromBlocks_multiply, hb]

theorem inG_lev {a : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit a.det) : InG (fromBlocks a 0 0 (a⁻¹)ᴴ) := by
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have h1 : aᴴ * a⁻¹ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ ha, Matrix.conjTranspose_one]
  have h1' : aᴴ * aᴴ⁻¹ = 1 := Matrix.mul_nonsing_inv _ haH
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul _ ha
  unfold InG JJ
  rw [Matrix.fromBlocks_conjTranspose]
  simp [Matrix.fromBlocks_multiply, h1, h2]

theorem inG_JJ : InG (JJ n) := by
  have hH : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
    simp
  unfold InG
  rw [hH, Matrix.neg_mul, JJ_mul_JJ, neg_neg, Matrix.one_mul]

def nEl (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) : GR n := mkGR (nU b) (inG_nU hb)

def mEl (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : GR n := mkGR (fromBlocks a 0 0 (a⁻¹)ᴴ) (inG_lev ha)

def wEl : GR n := mkGR (JJ n) inG_JJ

theorem blocks_of_inG {a b c d : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks a b c d)) :
    aᴴ * c = cᴴ * a ∧ aᴴ * d - cᴴ * b = 1 ∧ dᴴ * a - bᴴ * c = 1 ∧ bᴴ * d = dᴴ * b := by
  unfold InG JJ at h
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  have e11 := congrArg Matrix.toBlocks₁₁ h
  have e12 := congrArg Matrix.toBlocks₁₂ h
  have e21 := congrArg Matrix.toBlocks₂₁ h
  have e22 := congrArg Matrix.toBlocks₂₂ h
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂] at e11 e12 e21 e22
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← e11]; noncomm_ring
  · rw [← e12]; noncomm_ring
  · have k : -(dᴴ * a - bᴴ * c) = -1 := by rw [← e21]; noncomm_ring
    exact neg_inj.mp k
  · rw [← sub_eq_zero, ← e22]; noncomm_ring

theorem cross_of_inG {a b c d : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks a b c d)) : c * dᴴ = d * cᴴ := by
  obtain ⟨h11, h12, h21, h22⟩ := blocks_of_inG h
  have hl : fromBlocks dᴴ (-bᴴ) (-cᴴ) aᴴ * fromBlocks a b c d = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
    · rw [← h21]; noncomm_ring
    · rw [Matrix.neg_mul, h22]; abel
    · rw [Matrix.neg_mul, ← h11]; abel
    · rw [← h12]; noncomm_ring
  have hr : fromBlocks a b c d * fromBlocks dᴴ (-bᴴ) (-cᴴ) aᴴ = 1 := mul_eq_one_comm.mp hl
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hr
  have e := congrArg Matrix.toBlocks₂₁ hr
  simp only [Matrix.toBlocks_fromBlocks₂₁] at e
  rw [← sub_eq_zero, ← e]; noncomm_ring

theorem det_ne (g : GR n) : ((mR g).toBlocks₂₂ - Complex.I • (mR g).toBlocks₂₁).det ≠ 0 := by
  set a := (mR g).toBlocks₁₁
  set b := (mR g).toBlocks₁₂
  set c := (mR g).toBlocks₂₁
  set d := (mR g).toBlocks₂₂
  have hA : mR g = fromBlocks a b c d := (Matrix.fromBlocks_toBlocks _).symm
  have hU : InG (fromBlocks a b c d) := by rw [← hA]; exact g.2
  have hc := cross_of_inG hU
  have hG : IsUnit (fromBlocks a b c d).det := by rw [← hA]; exact isUnit_det_of_inG g.2
  intro h0
  have h0' : (d - Complex.I • c)ᴴ.det = 0 := by rw [Matrix.det_conjTranspose, h0, star_zero]
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
  have hMH : (d - Complex.I • c)ᴴ = dᴴ + Complex.I • cᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul]
    simp [sub_eq_add_neg, Complex.conj_I]
  rw [hMH, Matrix.add_mulVec, Matrix.smul_mulVec] at hMv
  set w := cᴴ *ᵥ v
  set u := dᴴ *ᵥ v
  have hu : u = -(Complex.I • w) := eq_neg_of_add_eq_zero_left hMv
  have k1 : star v ⬝ᵥ ((c * dᴴ) *ᵥ v) = star w ⬝ᵥ u := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    congr 1
    have := Matrix.star_mulVec cᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at this
    exact this.symm
  have k2 : star v ⬝ᵥ ((d * cᴴ) *ᵥ v) = star u ⬝ᵥ w := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    congr 1
    have := Matrix.star_mulVec dᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at this
    exact this.symm
  have k3 : star w ⬝ᵥ u = star u ⬝ᵥ w := by rw [← k1, ← k2, hc]
  rw [hu] at k3
  simp only [dotProduct_neg, neg_dotProduct, dotProduct_smul, smul_dotProduct, star_neg, star_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_I] at k3
  have hS : star w ⬝ᵥ w = 0 := by
    have k4 : (2 * Complex.I) * (star w ⬝ᵥ w) = 0 := by linear_combination -k3
    rcases mul_eq_zero.mp k4 with h2 | h2
    · exact absurd h2 (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    · exact h2
  have hw : w = 0 := dotProduct_star_self_eq_zero.mp hS
  have hu0 : u = 0 := by rw [hu, hw, smul_zero, neg_zero]
  have hz : (fromBlocks a b c d)ᴴ *ᵥ Sum.elim (0 : Fin n → ℂ) v = 0 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add]
    show Sum.elim w u = 0
    rw [hw, hu0]
    exact Sum.elim_zero_zero
  have hz0 : Sum.elim (0 : Fin n → ℂ) v ≠ 0 := by
    intro hz'
    apply hv
    funext i
    have := congrFun hz' (Sum.inr i)
    simpa using this
  have hdet : (fromBlocks a b c d)ᴴ.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hz0, hz⟩
  rw [Matrix.det_conjTranspose] at hdet
  exact hG.ne_zero (star_eq_zero.mp hdet)

theorem exists_real (c d : Matrix (Fin n) (Fin n) ℂ) (h : (d - Complex.I • c).det ≠ 0) :
    ∃ t : ℝ, (d + (t : ℂ) • c).det ≠ 0 := by
  classical
  let P : Polynomial ℂ := (d.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • c.map Polynomial.C).det
  have hev : ∀ z : ℂ, P.eval z = (d + z • c).det := by
    intro z
    rw [show P.eval z = Polynomial.evalRingHom z P from rfl, RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply]
    ring
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have := hev (-Complex.I)
    rw [h0, Polynomial.eval_zero, neg_smul, ← sub_eq_add_neg] at this
    exact this.symm
  have hfin : (Complex.ofReal ⁻¹' {x : ℂ | P.IsRoot x}).Finite :=
    (Polynomial.finite_setOfPred_isRoot hP).preimage Complex.ofReal_injective.injOn
  obtain ⟨t, -, ht⟩ := Set.infinite_univ.exists_notMem_finite hfin
  refine ⟨t, ?_⟩
  rw [← hev]
  exact ht

abbrev genSet (n : ℕ) : Set (GR n) := {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h}

theorem mem_of_unit (h : GR n) (hd : IsUnit (mR h).toBlocks₂₂.det) : h ∈ Subgroup.closure (genSet n) := by
  set a := (mR h).toBlocks₁₁
  set b := (mR h).toBlocks₁₂
  set c := (mR h).toBlocks₂₁
  set d := (mR h).toBlocks₂₂
  have hA : mR h = fromBlocks a b c d := (Matrix.fromBlocks_toBlocks _).symm
  have hU : InG (fromBlocks a b c d) := by rw [← hA]; exact h.2
  obtain ⟨h11, h12, h21, h22⟩ := blocks_of_inG hU
  have e1 : d * d⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have e1' : d⁻¹ * d = 1 := Matrix.nonsing_inv_mul _ hd
  have e2 : d⁻¹ᴴ * dᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have hβ : (b * d⁻¹)ᴴ = b * d⁻¹ := by
    calc (b * d⁻¹)ᴴ = d⁻¹ᴴ * bᴴ * (d * d⁻¹) := by rw [e1, Matrix.mul_one, Matrix.conjTranspose_mul]
      _ = d⁻¹ᴴ * (bᴴ * d) * d⁻¹ := by simp only [Matrix.mul_assoc]
      _ = d⁻¹ᴴ * (dᴴ * b) * d⁻¹ := by rw [h22]
      _ = (d⁻¹ᴴ * dᴴ) * b * d⁻¹ := by simp only [Matrix.mul_assoc]
      _ = b * d⁻¹ := by rw [e2, Matrix.one_mul]
  have hdH : IsUnit dᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  have hα : IsUnit (dᴴ)⁻¹.det := Matrix.isUnit_nonsing_inv_det _ hdH
  have hαinv : ((dᴴ)⁻¹)⁻¹ᴴ = d := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hdH, Matrix.conjTranspose_conjTranspose]
  have k1 : dᴴ * (b * d⁻¹) = bᴴ := by
    rw [← Matrix.mul_assoc, ← h22, Matrix.mul_assoc, e1, Matrix.mul_one]
  have k2 : b * d⁻¹ * d = b := by rw [Matrix.mul_assoc, e1', Matrix.mul_one]
  let n1 := nEl (b * d⁻¹) hβ
  let m1 := mEl (dᴴ)⁻¹ hα
  let l1 := m1⁻¹ * n1⁻¹ * h
  have hm1 : (mR m1)⁻¹ = fromBlocks dᴴ 0 0 d⁻¹ := by
    show (fromBlocks (dᴴ)⁻¹ 0 0 ((dᴴ)⁻¹)⁻¹ᴴ)⁻¹ = _
    rw [hαinv]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_nonsing_inv _ hdH]; noncomm_ring
    · noncomm_ring
    · noncomm_ring
    · rw [e1']; noncomm_ring
  have hl1 : mR l1 = fromBlocks 1 0 (d⁻¹ * c) 1 := by
    show (mR m1)⁻¹ * (mR n1)⁻¹ * mR h = _
    rw [hm1, show mR n1 = nU (b * d⁻¹) from rfl, inv_nU, hA]
    unfold nU
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
    · calc _ = dᴴ * a - (dᴴ * (b * d⁻¹)) * c := by noncomm_ring
        _ = 1 := by rw [k1]; exact h21
    · calc _ = dᴴ * (b - b * d⁻¹ * d) := by noncomm_ring
        _ = 0 := by rw [k2, sub_self, Matrix.mul_zero]
    · noncomm_ring
    · calc _ = d⁻¹ * d := by noncomm_ring
        _ = 1 := e1'
  have he : (d⁻¹ * c)ᴴ = d⁻¹ * c := by
    have hU1 : InG (mR l1) := l1.2
    rw [hl1] at hU1
    unfold InG JJ at hU1
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hU1
    have k := congrArg Matrix.toBlocks₁₁ hU1
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.conjTranspose_one, Matrix.conjTranspose_zero] at k
    rw [eq_comm, ← sub_eq_zero, ← k]; noncomm_ring
  have hneg : (-(d⁻¹ * c))ᴴ = -(d⁻¹ * c) := by rw [Matrix.conjTranspose_neg, he]
  let n2 := nEl (-(d⁻¹ * c)) hneg
  have hl1' : l1 = wEl * n2 * wEl⁻¹ := by
    apply ext_mR
    rw [hl1, mR_mul, mR_mul, mR_inv, show mR (wEl (n := n)) = JJ n from rfl, show mR n2 = nU (-(d⁻¹ * c)) from rfl,
      inv_JJ]
    unfold JJ nU
    rw [Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring
  have hn1 : n1 ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inl ⟨_, hβ, rfl⟩)
  have hm1' : m1 ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inr (Or.inl ⟨_, hα, rfl⟩))
  have hw : (wEl : GR n) ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hn2 : n2 ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inl ⟨_, hneg, rfl⟩)
  have hl : l1 ∈ Subgroup.closure (genSet n) := by
    rw [hl1']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw hn2) (Subgroup.inv_mem _ hw)
  have hh : h = n1 * m1 * l1 := by
    show h = n1 * m1 * (m1⁻¹ * n1⁻¹ * h)
    group
  rw [hh]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn1 hm1') hl

theorem genSt : GenSt := by
  intro n g
  have hA : mR g = fromBlocks (mR g).toBlocks₁₁ (mR g).toBlocks₁₂ (mR g).toBlocks₂₁ (mR g).toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks _).symm
  obtain ⟨t, ht⟩ := exists_real _ _ (det_ne g)
  have htH : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  let nt := nEl ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) htH
  have hnt : nt ∈ Subgroup.closure (genSet n) := Subgroup.subset_closure (Or.inl ⟨_, htH, rfl⟩)
  have hh : g * nt ∈ Subgroup.closure (genSet n) := by
    apply mem_of_unit
    rw [mR_mul, show mR nt = nU ((t : ℂ) • 1) from rfl, hA]
    unfold nU
    rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₂]
    have e : (mR g).toBlocks₂₁ * ((t : ℂ) • 1) + (mR g).toBlocks₂₂ * 1 =
        (mR g).toBlocks₂₂ + (t : ℂ) • (mR g).toBlocks₂₁ := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one, add_comm]
    rw [e]
    exact isUnit_iff_ne_zero.2 ht
  have hg : g = g * nt * nt⁻¹ := by group
  rw [hg]
  exact Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hnt)

end PositivityTheory.Rg.Sw.Glob.DenseP
