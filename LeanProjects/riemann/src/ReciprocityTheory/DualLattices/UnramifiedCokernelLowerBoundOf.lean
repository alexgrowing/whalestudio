import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundStatement
import ReciprocityTheory.DualLattices.MapSmulOneMulVec

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

abbrev cokGen {g : ℕ} {R : Type} [CommRing R] (Ht : Matrix (Fin g) (Ix g) R)
    (A : Matrix (Fin g) (Fin g) R) (B : Matrix (Ix g) (Ix g) R) :=
  LinearMap.range (Matrix.mulVecLin Aᵀ) ⧸
    ((LinearMap.range (Matrix.mulVecLin B)).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin Aᵀ)).subtype

def LenExStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g : ℕ) (Ht : Matrix (Fin g) (Ix g) R) (A : Matrix (Fin g) (Fin g) R)
    (B : Matrix (Ix g) (Ix g) R), ∃ x, HasLen v R (cokGen Ht A B) x

def KilledGenStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (M : Type) [AddCommGroup M] [Module R M] (x : NNReal) (d : ℕ) (c : R),
    HasLen v R M x → (∃ y : Fin d → M, Submodule.span R (Set.range y) = ⊤) →
    (∀ m : M, c • m = 0) → v (algebraMap R C c) ^ d ≤ x

def IdemGenStatement : Prop :=
  ∀ (R : Type) [CommRing R] (g d : ℕ) (P : Matrix (Fin g) (Fin g) R), P * P = P →
    Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R)) →
    ∃ y : Fin d → LinearMap.range (Matrix.mulVecLin Pᵀ), Submodule.span R (Set.range y) = ⊤

private lemma stdJ_form'' {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply, Finset.sum_sub_distrib]
  try ring

private lemma mul_eq_smul_one_comm_of_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    [IsDomain R] {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • 1) :
    B * A = c • 1 := by
  have hdet : A.det * B.det = c ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  have hA : A.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact pow_ne_zero _ hc hdet.symm
  have h1 : A * (B * A - c • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul, sub_self]
  have h2 : A.det • (B * A - c • 1) = 0 := by
    rw [← Matrix.one_mul (B * A - c • 1), ← Matrix.smul_mul, ← Matrix.adjugate_mul A,
      Matrix.mul_assoc, h1, Matrix.mul_zero]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h3
  have h4 := (mul_eq_zero.1 h3).resolve_left hA
  rw [Matrix.sub_apply, sub_eq_zero] at h4
  exact h4

lemma ht_cp_surj {R : Type} [CommRing R] [IsDomain R] {g : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (E : Matrix (Ix g) (Ix g) R) (cp : R) (hEt : Eᵀ = -E) (hdiag : ∀ i, E i i = 0)
    (hdet : IsUnit E.det) (hc : cp ≠ 0) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    ∀ f : Fin g → R, ∃ t, Ht *ᵥ t = cp • f := by
  intro f
  classical
  have hΨΦ : E⁻¹ * Matrix.fromCols Btᵀ (-Htᵀ) * Matrix.fromRows Ht Bt =
      cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [Matrix.mul_assoc, Matrix.fromCols_mul_fromRows, Matrix.neg_mul, ← sub_eq_add_neg, hform,
      Matrix.mul_smul, Matrix.nonsing_inv_mul E hdet]
  have hsq := mul_eq_smul_one_comm_of_ne_zero (n := Ix g) hc hΨΦ
  refine ⟨(E⁻¹ * Matrix.fromCols Btᵀ (-Htᵀ)) *ᵥ (Sum.elim f 0 : Fin g ⊕ Fin g → R), ?_⟩
  funext k
  have h5 : (cp • (1 : Matrix (Ix g) (Ix g) R)) *ᵥ (Sum.elim f 0 : Fin g ⊕ Fin g → R) =
      cp • (Sum.elim f 0 : Fin g ⊕ Fin g → R) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h1 := congrFun (congrArg (fun M => M *ᵥ (Sum.elim f 0 : Fin g ⊕ Fin g → R)) hsq) (Sum.inl k)
  rw [← Matrix.mulVec_mulVec, h5] at h1
  exact h1

lemma span_mk_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (N : Submodule R M)
    {d : ℕ} (y : Fin d → M) (hy : Submodule.span R (Set.range y) = ⊤) :
    Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (y k) : M ⧸ N)) = ⊤ := by
  rw [show (fun k => (Submodule.Quotient.mk (y k) : M ⧸ N)) = N.mkQ ∘ y from rfl, Set.range_comp,
    ← Submodule.map_span, hy, Submodule.map_top, Submodule.range_mkQ]

section HTDfacts

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

lemma htd_domain (hS : HodgeTateSetting p v R O σ cp) : IsDomain R := by
  exact Function.Injective.isDomain (algebraMap R C) hS.integers.hom_inj

lemma htd_cp_ne (hS : HodgeTateSetting p v R O σ cp) : cp ≠ 0 := by
  intro h
  have h1 := hS.cp_val
  rw [h, map_zero, map_zero, zero_pow] at h1
  · exact hS.p_ne h1.symm
  · have := (Fact.out : p.Prime).two_le
    omega

lemma htd_E (H : HodgeTateDatum p g v R O σ cp) :
    (H.E.map (algebraMap ℤ_[p] R))ᵀ = -H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, H.E.map (algebraMap ℤ_[p] R) i i = 0) ∧ IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  · intro i
    simp [Matrix.map_apply, H.E_alternating.2 i]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact H.isUnit_det_E.map _

lemma av_kill (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) (a b : O) (hab : σ b = a) :
    ∀ m : htCoker H a b, cp • m = 0 := by
  haveI := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  intro m
  refine Submodule.Quotient.induction_on _ m fun x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨t, ht⟩ := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt y
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, Submodule.mem_map,
    tPart, LinearMap.mem_range]
  refine ⟨(H.ρ b).map (algebraMap ℤ_[p] R) *ᵥ t, ⟨t, rfl⟩, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, H.Ht_equivariant.1 b, hab]
  rw [← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul]

lemma vp_rpow (hS : HodgeTateSetting p v R O σ cp) (d : ℕ) :
    (v (algebraMap R C (p : R)) : ℝ) ^ ((d : ℝ) / (p - 1)) =
      ((v (algebraMap R C cp) ^ d : NNReal) : ℝ) := by
  have hp := (Fact.out : p.Prime).two_le
  have h1 : ((v (algebraMap R C (p : R)) : NNReal) : ℝ) =
      ((v (algebraMap R C cp) : ℝ)) ^ ((p : ℝ) - 1) := by
    rw [← hS.cp_val]
    push_cast
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_sub (by omega)]
    simp
  have hne : ((p : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have h2 : ((p : ℝ) - 1) * ((d : ℝ) / ((p : ℝ) - 1)) = d := by
    field_simp
  rw [h1, ← Real.rpow_mul (by positivity), h2]
  push_cast
  rw [Real.rpow_natCast]

end HTDfacts

theorem permutedCokernelLowerBound_of (hU6 : CokernelLengthComparisonStatement) (hEx : LenExStatement) (hKG : KilledGenStatement)
    (hIG : IdemGenStatement) : PermutedCokernelLowerBoundStatement := by
  unfold PermutedCokernelLowerBoundStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π he hσ hP1 hP2 hL1 hL2 w hw d hd cw hcw
  have hidem : H.ρL (e (π w)) * H.ρL (e (π w)) = H.ρL (e (π w)) := by
    rw [← map_mul, he, if_pos rfl]
  obtain ⟨y, hy⟩ := hIG R g d (H.ρL (e (π w))) hidem hd
  obtain ⟨cwb, hcwb⟩ := hEx C v R hS.integers g H.Ht (H.ρL (e (π w)))
    ((H.ρ (e w)).map (algebraMap ℤ_[p] R))
  have hkill := av_kill hS H (e (π w)) (e w) (hσ w)
  have hgen : ∃ y' : Fin d → htCoker H (e (π w)) (e w), Submodule.span R (Set.range y') = ⊤ :=
    ⟨fun k => Submodule.Quotient.mk (y k), span_mk_top _ y hy⟩
  have h1 := hKG C v R hS.integers (htCoker H (e (π w)) (e w)) cwb d cp hcwb hgen hkill
  have h2 := hU6 p g C v R O σ cp hS H m e π he hσ hP1 hP2 hL1 hL2 w hw cw cwb hcw hcwb
  rw [vp_rpow hS d]
  exact_mod_cast h1.trans h2

section Unram

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

lemma cj_cj (hS : HodgeTateSetting p v R O σ cp) {H : HodgeTateDatum p g v R O σ cp}
    (U : UnramData p g v R O σ cp H) (k : Fin U.m) : U.cj (U.cj k) = k := by
  by_contra hne
  obtain ⟨a, ha⟩ := U.distinct _ _ hne
  rw [U.conj, U.conj, hS.invol, sub_self, map_zero, map_zero] at ha
  exact zero_ne_one ha

lemma ht_block_zero (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (k j : Fin U.m) (hkj : U.cj k ≠ j) :
    (U.εL k)ᵀ * H.Ht * U.εT j = 0 := by
  haveI := htd_domain hS
  obtain ⟨a, ha⟩ := U.distinct (U.cj k) j hkj
  set X := (U.εL k)ᵀ * H.Ht * U.εT j with hX
  have h1 : (U.εL k)ᵀ * (H.ρL (σ a))ᵀ = U.sg (U.cj k) a • (U.εL k)ᵀ := by
    rw [← Matrix.transpose_mul, U.εL_eig, Matrix.transpose_smul, U.conj]
  have h2 : H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j = U.sg j a • (H.Ht * U.εT j) := by
    rw [Matrix.mul_assoc, U.εT_eig, Matrix.mul_smul]
  have h3 : U.sg j a • X = U.sg (U.cj k) a • X := by
    calc U.sg j a • X = (U.εL k)ᵀ * (H.Ht * (H.ρ a).map (algebraMap ℤ_[p] R) * U.εT j) := by
          rw [h2, Matrix.mul_smul, hX, Matrix.mul_assoc]
      _ = (U.εL k)ᵀ * ((H.ρL (σ a))ᵀ * H.Ht * U.εT j) := by rw [H.Ht_equivariant.1 a]
      _ = U.sg (U.cj k) a • X := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.smul_mul, hX]
  have h4 : (U.sg (U.cj k) a - U.sg j a) • X = 0 := by rw [sub_smul, ← h3, sub_self]
  have hc : U.sg (U.cj k) a - U.sg j a ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at ha
    exact zero_ne_one ha
  ext i1 i2
  have h5 := congrFun (congrFun h4 i1) i2
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hc

lemma up_kill (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    ∀ m : cokE H.Ht U.εT U.εL (U.cj i) i, cp • m = 0 := by
  haveI := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsumL : ∑ k, (U.εL k)ᵀ = 1 := by
    rw [← Matrix.transpose_sum, U.εL_sum, Matrix.transpose_one]
  have key1 : H.Ht * U.εT i = (U.εL (U.cj i))ᵀ * H.Ht * U.εT i := by
    conv_lhs => rw [← Matrix.one_mul H.Ht, ← hsumL, Matrix.sum_mul, Matrix.sum_mul]
    rw [Finset.sum_eq_single (U.cj i)]
    · intro k _ hk
      apply ht_block_zero hS H U
      intro h
      apply hk
      rw [← h, cj_cj hS U]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have key2 : (U.εL (U.cj i))ᵀ * H.Ht * U.εT i = (U.εL (U.cj i))ᵀ * H.Ht := by
    conv_rhs => rw [← Matrix.mul_one ((U.εL (U.cj i))ᵀ * H.Ht), ← U.εT_sum, Matrix.mul_sum]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      apply ht_block_zero hS H U
      rw [cj_cj hS U]
      exact fun h => hj h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  intro m
  refine Submodule.Quotient.induction_on _ m fun x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨t, ht⟩ := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt y
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, Submodule.mem_map,
    LinearMap.mem_range]
  refine ⟨U.εT i *ᵥ t, ⟨t, rfl⟩, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [key1, key2, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul]

end Unram

theorem unramifiedCokernelLowerBound_of (hU7 : UnramifiedCokernelLengthStatement) (hEx : LenExStatement) (hKG : KilledGenStatement)
    (hIG : IdemGenStatement) : UnramifiedCokernelLowerBoundStatement := by
  unfold UnramifiedCokernelLowerBoundStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U i V1 hV1
  have hidem : U.εL (U.cj i) * U.εL (U.cj i) = U.εL (U.cj i) := by
    rw [U.εL_orth, if_pos rfl]
  obtain ⟨y, hy⟩ := hIG R g (U.r (U.cj i)) (U.εL (U.cj i)) hidem (U.rank (U.cj i))
  obtain ⟨V2, hV2⟩ := hEx C v R hS.integers g H.Ht (U.εL (U.cj i)) (U.εT i)
  have hkill := up_kill hS H U i
  have hgen : ∃ y' : Fin (U.r (U.cj i)) → cokE H.Ht U.εT U.εL (U.cj i) i,
      Submodule.span R (Set.range y') = ⊤ :=
    ⟨fun k => Submodule.Quotient.mk (y k), span_mk_top _ y hy⟩
  have h1 := hKG C v R hS.integers (cokE H.Ht U.εT U.εL (U.cj i) i) V2 (U.r (U.cj i)) cp hV2
    hgen hkill
  have h2 := hU7 p g C v R O σ cp hp2 hS H U i V1 V2 hV1 hV2
  have h3 := vp_rpow hS (U.r (U.cj i))
  have hx : (0 : ℝ) < (v (algebraMap R C (p : R)) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 hS.p_ne)
  have hsplit : ((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i =
      (U.r (U.cj i) : ℝ) / (p - 1) + ((U.r i : ℝ) / (p - 1) - frobSum U i) := by ring
  rw [hsplit, Real.rpow_add hx, h2, h3]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
  exact_mod_cast h1

theorem cokernelLowerBound_of (hU6 : CokernelLengthComparisonStatement) (hU7 : UnramifiedCokernelLengthStatement) (hEx : LenExStatement)
    (hKG : KilledGenStatement) (hIG : IdemGenStatement) : CokernelLowerBoundStatement := by
  exact And.intro (permutedCokernelLowerBound_of hU6 hEx hKG hIG) (unramifiedCokernelLowerBound_of hU7 hEx hKG hIG)

end ReciprocityTheory.PGsh.Up
