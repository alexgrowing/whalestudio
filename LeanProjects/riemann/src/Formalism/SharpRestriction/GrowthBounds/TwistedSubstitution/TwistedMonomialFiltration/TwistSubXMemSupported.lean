import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.MaxTwistDegreePderivLeAddOne

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

open Classical

def wDeg (w : Set ι) (μ : ι × Fin n →₀ ℕ) : ℕ := ∑ v ∈ μ.support, if v.1 ∈ w then μ v else 0

def wCoeff (w : Set ι) (M : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) : MvPolynomial (ι × Fin n) R :=
  ∑ μ ∈ F.support with μ.filter (fun v => v.1 ∈ w) = M, monomial (μ.filter (fun v => v.1 ∉ w)) (F.coeff μ)

theorem coeff_wCoeff (w : Set ι) (M ν : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) R) :
    coeff ν (wCoeff w M P) =
      if ν.filter (fun v => v.1 ∈ w) = 0 ∧ M.filter (fun v => v.1 ∉ w) = 0 then coeff (M + ν) P else 0 := by
  unfold wCoeff
  rw [coeff_sum]
  simp only [coeff_monomial]
  have key : ∀ μ : ι × Fin n →₀ ℕ, (μ.filter (fun v => v.1 ∈ w) = M ∧ μ.filter (fun v => v.1 ∉ w) = ν) ↔
      (μ = M + ν ∧ ν.filter (fun v => v.1 ∈ w) = 0 ∧ M.filter (fun v => v.1 ∉ w) = 0) := by
    intro μ
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [← h1, ← h2, Finsupp.filter_pos_add_filter_neg]
      · rw [← h2]; ext x
        simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
        split_ifs <;> simp_all
      · rw [← h1]; ext x
        simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
        split_ifs <;> simp_all
    · rintro ⟨rfl, h2, h3⟩
      refine ⟨?_, ?_⟩
      · rw [Finsupp.filter_add, h2, add_zero]
        have := Finsupp.filter_pos_add_filter_neg M (fun v => v.1 ∈ w)
        rw [h3, add_zero] at this
        exact this
      · rw [Finsupp.filter_add, h3, zero_add]
        have := Finsupp.filter_pos_add_filter_neg ν (fun v => v.1 ∈ w)
        rw [h2, zero_add] at this
        exact this
  split_ifs with hc
  · by_cases hm : M + ν ∈ P.support
    · rw [Finset.sum_eq_single (M + ν)]
      · rw [if_pos ((key _).2 ⟨rfl, hc⟩).2]
      · intro μ hμ hne
        rw [Finset.mem_filter] at hμ
        rw [if_neg]
        intro h2
        exact hne ((key μ).1 ⟨hμ.2, h2⟩).1
      · intro h; exact absurd (Finset.mem_filter.2 ⟨hm, ((key _).2 ⟨rfl, hc⟩).1⟩) h
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      refine Finset.sum_eq_zero fun μ hμ => ?_
      rw [Finset.mem_filter] at hμ
      rw [if_neg]
      intro h2
      have := ((key μ).1 ⟨hμ.2, h2⟩).1
      subst this
      exact hm hμ.1
  · refine Finset.sum_eq_zero fun μ hμ => ?_
    rw [Finset.mem_filter] at hμ
    rw [if_neg]
    intro h2
    exact hc ((key μ).1 ⟨hμ.2, h2⟩).2

def WFree {B : Type*} [CommRing B] (w : Set ι) (P : MvPolynomial (ι × Fin n) B) : Prop :=
  ∀ ν ∈ P.support, ν.filter (fun v => v.1 ∈ w) = 0

theorem wCoeff_add (w : Set ι) (M : ι × Fin n →₀ ℕ) (P Q : MvPolynomial (ι × Fin n) R) :
    wCoeff w M (P + Q) = wCoeff w M P + wCoeff w M Q := by
  ext ν
  simp only [coeff_add, coeff_wCoeff]
  split_ifs <;> simp

theorem wCoeff_mem {Fl : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Fil R} (w : Set ι) (M : ι × Fin n →₀ ℕ) {t : ℤ}
    {P : MvPolynomial (ι × Fin n) R} (hP : P ∈ (Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lift Fl 0).F t) :
    wCoeff w M P ∈ (Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lift Fl 0).F t := by
  intro ν
  rw [coeff_wCoeff]
  split_ifs
  · simpa using hP (M + ν)
  · exact (Fl.F _).zero_mem

theorem wfree_iff_supported {B : Type*} [CommRing B] (w : Set ι) (P : MvPolynomial (ι × Fin n) B) :
    WFree w P ↔ P ∈ supported B {v : ι × Fin n | v.1 ∉ w} := by
  classical
  rw [mem_supported]
  constructor
  · intro h v hv
    rw [Finset.mem_coe, mem_vars] at hv
    obtain ⟨d, hd, hvd⟩ := hv
    have h1 := h d hd
    intro hw
    have : (d.filter (fun v => v.1 ∈ w)) v = 0 := by rw [h1]; rfl
    rw [Finsupp.filter_apply, if_pos hw] at this
    exact (Finsupp.mem_support_iff.1 hvd) this
  · intro h ν hν
    ext x
    rw [Finsupp.filter_apply]
    split_ifs with hx
    · by_contra hne
      have hv : x ∈ (P.vars : Set (ι × Fin n)) := by
        rw [Finset.mem_coe, mem_vars]
        exact ⟨ν, hν, Finsupp.mem_support_iff.2 hne⟩
      exact (h hv) hx
    · rfl

theorem wfree_monomial (w : Set ι) (μ : ι × Fin n →₀ ℕ) (c : R) :
    WFree w (monomial (μ.filter (fun v => v.1 ∉ w)) c) := by
  classical
  intro ν hν
  have := support_monomial_subset hν
  rw [Finset.mem_singleton] at this
  subst this
  ext x
  simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs <;> simp_all

theorem wCoeff_mul_monomial (w : Set ι) (M M' : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) R) (hP : WFree w P)
    (hM' : M'.filter (fun v => v.1 ∉ w) = 0) :
    wCoeff w M (P * monomial M' 1) = if M' = M then P else 0 := by
  classical
  have hM'x : ∀ x, x.1 ∉ w → M' x = 0 := by
    intro x hx
    have : (M'.filter (fun v => v.1 ∉ w)) x = 0 := by rw [hM']; rfl
    rwa [Finsupp.filter_apply, if_pos hx] at this
  have hPz : ∀ ρ : ι × Fin n →₀ ℕ, (∃ x, x.1 ∈ w ∧ ρ x ≠ 0) → coeff ρ P = 0 := by
    rintro ρ ⟨x, hx, hρ⟩
    by_contra hne
    have h1 := hP ρ (MvPolynomial.mem_support_iff.2 hne)
    have : (ρ.filter (fun v => v.1 ∈ w)) x = 0 := by rw [h1]; rfl
    rw [Finsupp.filter_apply, if_pos hx] at this
    exact hρ this
  ext ν
  rw [coeff_wCoeff, coeff_mul_monomial']
  split_ifs with hc h1 h2 h2 h1 h1
  · subst h2
    rw [mul_one, add_tsub_cancel_left]
  · rw [mul_one]
    apply hPz
    have hMx : ∀ x, x.1 ∉ w → M x = 0 := by
      intro x hx
      have : (M.filter (fun v => v.1 ∉ w)) x = 0 := by rw [hc.2]; rfl
      rwa [Finsupp.filter_apply, if_pos hx] at this
    have hνx : ∀ x, x.1 ∈ w → ν x = 0 := by
      intro x hx
      have : (ν.filter (fun v => v.1 ∈ w)) x = 0 := by rw [hc.1]; rfl
      rwa [Finsupp.filter_apply, if_pos hx] at this
    have : ∃ x, M' x ≠ M x := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact h2 (Finsupp.ext hall)
    obtain ⟨x, hx⟩ := this
    have hxw : x.1 ∈ w := by
      by_contra hxw
      exact hx (by rw [hM'x x hxw, hMx x hxw])
    refine ⟨x, hxw, ?_⟩
    have hle := h1 x
    rw [Finsupp.add_apply, hνx x hxw, add_zero] at hle
    rw [Finsupp.tsub_apply, Finsupp.add_apply, hνx x hxw, add_zero]
    omega
  · exact absurd (by rw [h2]; exact le_self_add) h1
  · simp
  · subst h1
    by_cases hν : ν.filter (fun v => v.1 ∈ w) = 0
    · exact absurd ⟨hν, hM'⟩ hc
    · by_contra hne
      exact hν (hP ν (MvPolynomial.mem_support_iff.2 (Ne.symm hne)))
  · rfl

theorem monomial_split (w : Set ι) (μ : ι × Fin n →₀ ℕ) (c : R) :
    monomial μ c = monomial (μ.filter (fun v => v.1 ∉ w)) c * monomial (μ.filter (fun v => v.1 ∈ w)) 1 := by
  rw [monomial_mul, mul_one, add_comm, Finsupp.filter_pos_add_filter_neg]

theorem filter_neg_filter_pos (w : Set ι) (μ : ι × Fin n →₀ ℕ) :
    (μ.filter (fun v => v.1 ∈ w)).filter (fun v => v.1 ∉ w) = 0 := by
  ext x
  simp only [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs <;> simp_all

theorem wCoeff_monomial (w : Set ι) (M μ : ι × Fin n →₀ ℕ) (c : R) :
    wCoeff w M (monomial μ c) = if μ.filter (fun v => v.1 ∈ w) = M then monomial (μ.filter (fun v => v.1 ∉ w)) c else 0 := by
  rw [monomial_split w μ c, wCoeff_mul_monomial w M _ _ (wfree_monomial w μ c) (filter_neg_filter_pos w μ)]

theorem X_mem_supported' {B : Type*} [CommRing B] (w : Set ι) (v : ι × Fin n) (hv : v.1 ∉ w) :
    (X v : MvPolynomial (ι × Fin n) B) ∈ supported B {x : ι × Fin n | x.1 ∉ w} := by
  classical
  rw [mem_supported]
  intro x hx
  rw [Finset.mem_coe, mem_vars] at hx
  obtain ⟨d, hd, hxd⟩ := hx
  have h1 := support_monomial_subset (R := B) hd
  rw [Finset.mem_singleton] at h1
  subst h1
  have h2 := Finsupp.support_single_subset hxd
  rw [Finset.mem_singleton] at h2
  subst h2
  exact hv

theorem twistSub_X_mem_supported (w : Set ι) (j : Fin n) (v : ι × Fin n) (hv : v.1 ∉ w) :
    twistSub (R := R) LL S j (X v) ∈ supported (GLLaurent R n) {x : ι × Fin n | x.1 ∉ w} := by
  unfold twistSub
  rw [eval₂Hom_X']
  split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (X_mem_supported' w _ hv)
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (X_mem_supported' w _ hv)
  · exact X_mem_supported' w _ hv

theorem twistSub_wfree (w : Set ι) (j : Fin n) (P : MvPolynomial (ι × Fin n) R) (hP : WFree w P) :
    WFree w (twistSub LL S j P) := by
  rw [wfree_iff_supported]
  rw [P.as_sum, map_sum]
  refine Subalgebra.sum_mem _ fun ν hν => ?_
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  refine Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun v hv => ?_)
  · rw [twistSub, eval₂Hom_C]
    exact Subalgebra.algebraMap_mem _ _
  · rw [map_pow]
    refine Subalgebra.pow_mem _ ?_ _
    apply twistSub_X_mem_supported
    intro hw
    have h1 := hP ν hν
    have : (ν.filter (fun v => v.1 ∈ w)) v = 0 := by rw [h1]; rfl
    rw [Finsupp.filter_apply, if_pos hw] at this
    exact (Finsupp.mem_support_iff.1 hv) this

theorem twistSub_monomial_w (w : Set ι) (hd : Disjoint S w) (j : Fin n) (M' : ι × Fin n →₀ ℕ)
    (hM' : M'.filter (fun v => v.1 ∉ w) = 0) :
    twistSub (R := R) LL S j (monomial M' 1) = monomial M' 1 := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, monomial_eq, Finsupp.prod]
  congr 1
  · rw [twistSub, eval₂Hom_C, map_one, map_one]
  · refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_pow]
    congr 1
    have hw : v.1 ∈ w := by
      by_contra hw
      have : (M'.filter (fun v => v.1 ∉ w)) v = 0 := by rw [hM']; rfl
      rw [Finsupp.filter_apply, if_pos hw] at this
      exact (Finsupp.mem_support_iff.1 hv) this
    exact Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL S j v (Set.disjoint_right.1 hd hw)

theorem twistSub_wCoeff (w : Set ι) (hd : Disjoint S w) (j : Fin n) (M : ι × Fin n →₀ ℕ)
    (F : MvPolynomial (ι × Fin n) R) : twistSub LL S j (wCoeff w M F) = wCoeff w M (twistSub LL S j F) := by
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [wCoeff_add, map_add, map_add, wCoeff_add, hP, hQ]
  | monomial μ c =>
    rw [wCoeff_monomial, monomial_split w μ c, map_mul, twistSub_monomial_w LL S w hd j _ (filter_neg_filter_pos w μ),
      wCoeff_mul_monomial w M _ _ (twistSub_wfree LL S w j _ (wfree_monomial w μ c)) (filter_neg_filter_pos w μ)]
    split_ifs <;> simp

theorem sum_wCoeff (w : Set ι) (F : MvPolynomial (ι × Fin n) R) :
    F = ∑ M ∈ F.support.image (fun μ => μ.filter (fun v => v.1 ∈ w)), monomial M 1 * wCoeff w M F := by
  calc F = ∑ μ ∈ F.support, monomial μ (coeff μ F) := F.as_sum
    _ = ∑ M ∈ F.support.image (fun μ => μ.filter (fun v => v.1 ∈ w)),
          ∑ μ ∈ F.support with μ.filter (fun v => v.1 ∈ w) = M, monomial μ (coeff μ F) :=
        (Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem _ hμ) _).symm
    _ = _ := by
        refine Finset.sum_congr rfl fun M _ => ?_
        unfold wCoeff
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [monomial_mul, one_mul]
        congr 1
        rw [← (Finset.mem_filter.1 hμ).2, Finsupp.filter_pos_add_filter_neg]

def trivFil (B : Type*) [CommRing B] : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Fil B where
  F t := if t ≤ 0 then ⊤ else ⊥
  mul_mem := by
    intro t u a b ha hb
    by_cases ht : t ≤ 0
    · by_cases hu : u ≤ 0
      · rw [if_pos (by omega)]; exact AddSubgroup.mem_top _
      · rw [if_neg hu, AddSubgroup.mem_bot] at hb; rw [hb, mul_zero]; exact AddSubgroup.zero_mem _
    · rw [if_neg ht, AddSubgroup.mem_bot] at ha; rw [ha, zero_mul]; exact AddSubgroup.zero_mem _
  one_mem := by simp
  anti := by
    intro t u htu
    by_cases hu : u ≤ 0
    · rw [if_pos hu, if_pos (by omega)]
    · rw [if_neg hu]; exact bot_le

theorem trivFil_F (B : Type*) [CommRing B] (t : ℤ) : (trivFil B).F t = if t ≤ 0 then ⊤ else ⊥ := rfl

def wDegHom (w : Set ι) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ w then Nat.castAddMonoidHom ℤ else 0

theorem wDegHom_eq (w : Set ι) (μ : ι × Fin n →₀ ℕ) : wDegHom w μ = (wDeg w μ : ℤ) := by
  unfold wDegHom wDeg
  rw [Finsupp.liftAddHom_apply, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp

theorem wDegHom_single (w : Set ι) (v : ι × Fin n) :
    wDegHom w (Finsupp.single v 1) = if v.1 ∈ w then 1 else 0 := by
  unfold wDegHom
  rw [Finsupp.liftAddHom_apply_single]
  split_ifs <;> simp

def untw (w : Set ι) (j : Fin n) :
    MvPolynomial (ι × Fin n) (GLLaurent R n) →+* MvPolynomial (ι × Fin n) (GLLaurent R n) :=
  eval₂Hom C fun v =>
    if v.1 ∈ w then ∑ b : Fin n, C (twistMat R n j (-1) b v.2) * X (v.1, b) else X v

theorem untw_C (w : Set ι) (j : Fin n) (a : GLLaurent R n) :
    untw (R := R) (n := n) w j (C a : MvPolynomial (ι × Fin n) (GLLaurent R n)) = C a := by
  unfold untw; rw [eval₂Hom_C]

theorem untw_X (w : Set ι) (j : Fin n) (v : ι × Fin n) :
    untw (R := R) (n := n) w j (X v) =
      if v.1 ∈ w then ∑ b : Fin n, C (twistMat R n j (-1) b v.2) * X (v.1, b) else X v := by
  unfold untw; rw [eval₂Hom_X']

theorem untw_comp (w : Set ι) (hw : ∀ l ∈ w, LL.vec l = true) (hd : Disjoint S w) (j : Fin n) :
    (untw (R := R) (n := n) w j).comp (twistSub LL (S ∪ w) j) = twistSub LL S j := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, twistSub, eval₂Hom_C]
    exact untw_C w j _
  · intro v
    rw [RingHom.comp_apply]
    by_cases hS : v.1 ∈ S
    · have hnw : v.1 ∉ w := Set.disjoint_left.1 hd hS
      unfold twistSub
      rw [eval₂Hom_X', eval₂Hom_X', if_pos (Set.mem_union_left w hS), if_pos hS]
      split_ifs
      · rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, untw_C, untw_X, if_neg hnw]
      · rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul, untw_C, untw_X, if_neg hnw]
    · by_cases hW : v.1 ∈ w
      · rw [Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL S j v hS]
        unfold twistSub
        rw [eval₂Hom_X', if_pos (Set.mem_union_right S hW), if_pos (hw _ hW)]
        rw [map_sum]
        simp_rw [map_mul, untw_C, untw_X, if_pos hW, Finset.mul_sum, ← mul_assoc, ← C_mul]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul, ← map_sum]
        have hm : ∀ b' : Fin n, ∑ b : Fin n, twistMat R n j 1 b v.2 * twistMat R n j (-1) b' b =
            (1 : Matrix (Fin n) (Fin n) (GLLaurent R n)) b' v.2 := by
          intro b'
          have h1 := Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_twistMat_mul R n j (-1)
          rw [neg_neg] at h1
          rw [← h1, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        simp_rw [hm, Matrix.one_apply]
        simp
      · rw [Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL S j v hS,
          Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out LL (S ∪ w) j v (by simp [hS, hW]), untw_X, if_neg hW]

theorem valS_wCoeff_ge (w : Set ι) (hw : ∀ l ∈ w, LL.vec l = true) (hd : Disjoint S w) (F : MvPolynomial (ι × Fin n) R)
    (dw : ℕ) (hdeg : ∀ μ ∈ F.support, wDeg w μ ≤ dw) (th : ℤ) (hF : (th : WithTop ℤ) ≤ valS LL (S ∪ w) F)
    (M : ι × Fin n →₀ ℕ) : ((th - dw : ℤ) : WithTop ℤ) ≤ valS LL S (wCoeff w M F) := by
  open Formalism.MainNotions.TestSideWords.TwistedFiltration.G1 in
  have htriv0 : ∀ (B : Type _) [CommRing B] (b : B), b ∈ (trivFil B).F 0 := by
    intro B _ b; simp [trivFil]

  have hB : twistSub LL (S ∪ w) (lastIdx n) F ∈
      (flt_lift (trivFil (GLLaurent R n)) (-wDegHom w)).F (-(dw : ℤ)) := by
    refine flt_hom_mem (trivFil R) _ _ (-wDegHom w) ?_ ?_ ?_
    · intro t b hb
      rw [twistSub, eval₂Hom_C]
      apply flt_C_mem
      by_cases ht : t ≤ 0
      · simp [trivFil, ht]
      · have hb' : b ∈ (⊥ : AddSubgroup R) := by simpa [trivFil, ht] using hb
        rw [AddSubgroup.mem_bot] at hb'
        rw [hb', map_zero]
        exact AddSubgroup.zero_mem _
    · intro v
      have e1 : ∀ b : Fin n, (-wDegHom w) (Finsupp.single (v.1, b) 1) = (-wDegHom w) (Finsupp.single v 1) := by
        intro b; simp [wDegHom_single]
      unfold twistSub
      rw [eval₂Hom_X']
      split_ifs
      · refine AddSubgroup.sum_mem _ fun b _ => ?_
        rw [C_mul_X_eq_monomial]
        apply flt_monomial_mem
        rw [e1 b, sub_self]
        exact htriv0 _ _
      · refine AddSubgroup.sum_mem _ fun b _ => ?_
        rw [C_mul_X_eq_monomial]
        apply flt_monomial_mem
        rw [e1 b, sub_self]
        exact htriv0 _ _
      · apply flt_monomial_mem
        rw [sub_self]
        exact htriv0 _ _
    · intro m
      by_cases hm : m ∈ F.support
      · have h1 := hdeg m hm
        have : -(dw : ℤ) - (-wDegHom w) m ≤ 0 := by
          rw [AddMonoidHom.neg_apply, wDegHom_eq]; omega
        rw [trivFil_F, if_pos this]
        exact AddSubgroup.mem_top _
      · rw [MvPolynomial.notMem_support_iff.1 hm]
        exact AddSubgroup.zero_mem _

  have hC : twistSub LL (S ∪ w) (lastIdx n) F ∈
      (flt_lift (flt_L (GLCoord R n) 1) (-wDegHom w)).F (th - dw) := by
    intro m
    have h1 := ((flt_le_valS LL (S ∪ w) F th).1 hF) m
    have h2 := hB m
    by_cases hm : (wDeg w m : ℤ) ≤ dw
    · refine (flt_L (GLCoord R n) 1).anti ?_ h1
      rw [AddMonoidHom.neg_apply, wDegHom_eq]
      simp only [AddMonoidHom.zero_apply]
      omega
    · have : ¬ (-(dw : ℤ) - (-wDegHom w) m ≤ 0) := by
        rw [AddMonoidHom.neg_apply, wDegHom_eq]; omega
      have h3 : coeff m (twistSub LL (S ∪ w) (lastIdx n) F) ∈ (⊥ : AddSubgroup (GLLaurent R n)) := by
        rw [trivFil_F, if_neg this] at h2
        exact h2
      rw [AddSubgroup.mem_bot] at h3
      rw [h3]
      exact AddSubgroup.zero_mem _

  have hD : untw w (lastIdx n) (twistSub LL (S ∪ w) (lastIdx n) F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) 1).F (th - dw) := by
    refine flt_hom_mem (flt_L (GLCoord R n) 1) (laurentCoeffFiltration R n (ι × Fin n) 1) (untw w (lastIdx n)) (-wDegHom w) ?_ ?_ hC
    · intro t b hb
      rw [untw_C]
      exact flt_C_mem hb
    · intro v
      rw [untw_X]
      split_ifs with hv
      · refine AddSubgroup.sum_mem _ fun b _ => ?_
        rw [C_mul_X_eq_monomial]
        apply flt_monomial_mem
        rw [AddMonoidHom.neg_apply, wDegHom_single, if_pos hv]
        simp only [AddMonoidHom.zero_apply, sub_zero]
        exact flt_twistMat_mem R n (lastIdx n) (-1) 1 (-1) (by norm_num) (by norm_num) b v.2
      · apply flt_monomial_mem
        rw [AddMonoidHom.neg_apply, wDegHom_single, if_neg hv]
        simpa using (flt_L (GLCoord R n) 1).one_mem
  rw [← RingHom.comp_apply, untw_comp LL S w hw hd] at hD
  rw [flt_le_valS, twistSub_wCoeff LL S w hd]
  exact wCoeff_mem w M hD

theorem valS_wCoeff_of_disj (w : Set ι) (hd : Disjoint S w) (F : MvPolynomial (ι × Fin n) R) (M : ι × Fin n →₀ ℕ) :
    valS LL S F ≤ valS LL S (wCoeff w M F) := by
  have h := Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withTop_le (a := valS LL S F) (b := valS LL S (wCoeff w M F)) (N := 0) (by
    intro t ht
    rw [sub_zero, Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_le_valS] at *
    rw [twistSub_wCoeff LL S w hd]
    exact wCoeff_mem w M ht)
  simpa using h

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
