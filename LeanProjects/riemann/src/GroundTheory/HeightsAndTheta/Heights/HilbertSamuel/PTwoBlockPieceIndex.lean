import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceIndex
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockPieceIndex

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem prod_X_pow_eq (d : K → ℕ) :
    (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) = monomial (Finsupp.equivFunOnFinite.symm d) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp

theorem mConeMap_of_homog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm d) 1 := by
  classical
  rw [← prod_X_pow_eq]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem aeval_i2comp (y : (Σ k, ι k) → Ω) (m : K → ℕ) (q : MRing ι) :
    aeval y (i2comp m q) = coeff (Finsupp.equivFunOnFinite.symm m) (mConeMap y q) := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [mConeMap_of_homog y (isMultiHomog_monomial μ c), i2comp_of_homog (isMultiHomog_monomial μ c),
      coeff_C_mul, coeff_monomial]
    by_cases h : (fun k => ∑ i, μ ⟨k, i⟩) = m
    · rw [if_pos h, if_pos (by rw [h]), mul_one]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h')), mul_zero, map_zero]
  | add p q hp hq => rw [i2comp_add, map_add, hp, hq, map_add, coeff_add]

theorem aeval_i2comp_of_mem (y : (Σ k, ι k) → Ω) {p : MRing ι} (hp : p ∈ mCoordIdeal y) (m : K → ℕ) :
    aeval y (i2comp m p) = 0 := by
  rw [aeval_i2comp, show mConeMap y p = 0 from RingHom.mem_ker.mp hp, coeff_zero]

theorem mem_mCoordIdeal_of_homog (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  show f ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap_of_homog y hf, h0, map_zero, zero_mul]

def evPiece (y : (Σ k, ι k) → Ω) (m : K → ℕ) : Submodule ℤ Ω :=
  (mHom ι m).map (aeval y).toLinearMap

theorem evPiece_mul_le (y : (Σ k, ι k) → Ω) (m n : K → ℕ) :
    evPiece y m * evPiece y n ≤ evPiece y (m + n) := by
  refine Submodule.mul_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
  refine ⟨f * g, (mem_mHom_iff _ _).mpr
    (isMultiHomog_mul' ((mem_mHom_iff _ _).mp hf) ((mem_mHom_iff _ _).mp hg)), ?_⟩
  simp

theorem one_le_evPiece (y : (Σ k, ι k) → Ω) : 1 ≤ evPiece y 0 := by
  rw [Submodule.one_le]
  exact ⟨1, (mem_mHom_iff _ _).mpr isMultiHomog_one, by simp⟩

theorem pow_le_evPiece (y : (Σ k, ι k) → Ω) {L : Submodule ℤ Ω} {d : K → ℕ} (h : L ≤ evPiece y d) :
    ∀ n : ℕ, L ^ n ≤ evPiece y (n • d)
  | 0 => by rw [pow_zero, zero_smul]; exact one_le_evPiece y
  | n + 1 => by
    rw [pow_succ, succ_nsmul]
    exact (mul_le_mul' (pow_le_evPiece y h n) h).trans (evPiece_mul_le y _ _)

theorem map_piece [DecidableEq K] (y : (Σ k, ι k) → Ω) {g : MRing ι} {e : K → ℕ} (hg : IsMultiHomog g e)
    (k : K) (m : K → ℕ) :
    ((mCoordIdeal y ⊔ Ideal.span (Set.range fun j : ι k => g * X ⟨k, j⟩)).restrictScalars ℤ ⊓
        mHom ι (m + (e + Pi.single k 1))).map (aeval y).toLinearMap =
      (Submodule.span ℤ (Set.range fun j : ι k => y ⟨k, j⟩) * evPiece y m).map
        (LinearMap.mulLeft ℤ (aeval y g)) := by
  have hgX : ∀ j, IsMultiHomog (g * X ⟨k, j⟩) (e + Pi.single k 1) := fun j =>
    isMultiHomog_mul' hg (isMultiHomog_X' k j)
  apply le_antisymm
  · rintro _ ⟨f, ⟨hfJ, hfH⟩, rfl⟩
    have hf := (mem_mHom_iff _ _).mp hfH
    obtain ⟨p, hp, s, hs, rfl⟩ := Submodule.mem_sup.mp (Submodule.restrictScalars_mem ℤ _ _ |>.mp hfJ)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hs
    have e1 : i2comp (m + (e + Pi.single k 1)) (p + ∑ j, c j * (g * X ⟨k, j⟩)) =
        i2comp (m + (e + Pi.single k 1)) p + ∑ j, i2comp m (c j) * (g * X ⟨k, j⟩) := by
      rw [i2comp_add]
      congr 1
      rw [show i2comp (m + (e + Pi.single k 1)) (∑ j, c j * (g * X ⟨k, j⟩)) =
          ∑ j, i2comp (m + (e + Pi.single k 1)) (c j * (g * X ⟨k, j⟩)) from map_sum (i2compHom _) _ _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [i2comp_mul_right (hgX j), if_pos le_add_self, add_tsub_cancel_right]
    rw [AlgHom.toLinearMap_apply, ← i2comp_self hf, e1, map_add, aeval_i2comp_of_mem y hp, zero_add, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine ⟨y ⟨k, j⟩ * aeval y (i2comp m (c j)), Submodule.mul_mem_mul (Submodule.subset_span ⟨j, rfl⟩)
      ⟨_, (mem_mHom_iff _ _).mpr (isMultiHomog_i2comp _ _), rfl⟩, ?_⟩
    simp only [LinearMap.mulLeft_apply, map_mul, aeval_X]
    ring
  · rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
    rintro u hu _ ⟨h, hh, rfl⟩
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hu
    refine ⟨∑ j, n j • (h * (g * X ⟨k, j⟩)), ⟨?_, ?_⟩, ?_⟩
    · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      exact (Submodule.restrictScalars_mem ℤ _ _).mpr
        (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)))
    · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      exact (mem_mHom_iff _ _).mpr (isMultiHomog_mul' ((mem_mHom_iff _ _).mp hh) (hgX j))
    · simp only [LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_sum, map_zsmul,
        map_mul, aeval_X, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [zsmul_eq_mul]
      ring

theorem relIndex_eq_map {M : Type*} [AddCommGroup M] (f : M →ₗ[ℤ] Ω) {A B H : Submodule ℤ M} (hA : A ≤ H)
    (hB : B ≤ H) (hker : ∀ u ∈ H, f u = 0 → u ∈ A) :
    A.toAddSubgroup.relIndex B.toAddSubgroup = (A.map f).toAddSubgroup.relIndex (B.map f).toAddSubgroup := by
  have hAB : A.toAddSubgroup ⊓ B.toAddSubgroup =
      (A.map f).toAddSubgroup.comap f.toAddMonoidHom ⊓ B.toAddSubgroup := by
    ext u
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap,
      LinearMap.toAddMonoidHom_coe, Submodule.mem_map]
    constructor
    · rintro ⟨huA, huB⟩
      exact ⟨⟨u, huA, rfl⟩, huB⟩
    · rintro ⟨⟨v, hvA, hv⟩, huB⟩
      refine ⟨?_, huB⟩
      have : u - v ∈ A := hker _ (sub_mem (hB huB) (hA hvA)) (by rw [map_sub, hv, sub_self])
      simpa using add_mem this hvA
  rw [← AddSubgroup.inf_relIndex_right, hAB, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  congr 1

end General

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

omit [CharZero Ω] in

theorem relIndex_map_mulLeft {γ : Ω} (hγ : γ ≠ 0) (A B : Submodule ℤ Ω) :
    (A.map (LinearMap.mulLeft ℤ γ)).toAddSubgroup.relIndex (B.map (LinearMap.mulLeft ℤ γ)).toAddSubgroup =
      A.toAddSubgroup.relIndex B.toAddSubgroup := by
  have e : ∀ C : Submodule ℤ Ω, (C.map (LinearMap.mulLeft ℤ γ)).toAddSubgroup =
      C.toAddSubgroup.map (LinearMap.mulLeft ℤ γ).toAddMonoidHom := fun C => by
    ext
    simp
  rw [e, e, AddSubgroup.relIndex_map_map_of_injective _ _
    (fun u v h => mul_left_cancel₀ hγ (by simpa using h))]

omit [CharZero Ω] [Fintype κ] in
theorem prod_pow_mem_pow {L : Submodule ℤ Ω} {v : κ → Ω} (hv : ∀ i, v i ∈ L) (n : κ → ℕ) (s : Finset κ) :
    ∏ i ∈ s, v i ^ n i ∈ L ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, pow_zero]
    exact Submodule.one_le.mp le_rfl
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
    exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (hv i) _) ih

theorem evPiece_pair (x x' : Ix κ → Ω) (a b : ℕ) :
    evPiece (pair x x') ![a, b] = sec ℤ x a * sec ℤ x' b := by
  apply le_antisymm
  · rw [evPiece, Submodule.map_le_iff_le_comap]
    intro s hs
    have hs' := (mem_mHom_iff _ _).mp hs
    rw [Submodule.mem_comap, AlgHom.toLinearMap_apply, s.as_sum, map_sum]
    refine Submodule.sum_mem _ fun μ hμ => ?_
    rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma, Fin.prod_univ_two,
      algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul]
    refine Submodule.smul_mem _ _ (Submodule.mul_mem_mul ?_ ?_)
    · have h0 : ∑ i, μ ⟨0, i⟩ = a := by simpa using hs' μ hμ 0
      rw [sec_eq_span_pow, ← h0]
      refine prod_pow_mem_pow (fun i => ?_) _ _
      exact Submodule.subset_span ⟨⟨(), i⟩, by simp [pair]⟩
    · have h1 : ∑ i, μ ⟨1, i⟩ = b := by simpa using hs' μ hμ 1
      rw [sec_eq_span_pow, ← h1]
      refine prod_pow_mem_pow (fun i => ?_) _ _
      exact Submodule.subset_span ⟨⟨(), i⟩, by simp [pair]⟩
  · have h0 : Submodule.span ℤ (Set.range x) ≤ evPiece (pair x x') (Pi.single 0 1) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
      exact Submodule.mem_map.mpr ⟨X ⟨0, i⟩, (mem_mHom_iff _ _).mpr (isMultiHomog_X' (ι := FinTwoTypeFamily κ) 0 i), by simp [pair]⟩
    have h1 : Submodule.span ℤ (Set.range x') ≤ evPiece (pair x x') (Pi.single 1 1) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨⟨⟨⟩, i⟩, rfl⟩
      exact Submodule.mem_map.mpr ⟨X ⟨1, i⟩, (mem_mHom_iff _ _).mpr (isMultiHomog_X' (ι := FinTwoTypeFamily κ) 1 i), by simp [pair]⟩
    have e : (a • Pi.single 0 1 + b • Pi.single 1 1 : Fin 2 → ℕ) = ![a, b] := by
      funext k
      fin_cases k <;> simp
    rw [sec_eq_span_pow, sec_eq_span_pow, ← e]
    exact (mul_le_mul' (pow_le_evPiece _ h0 a) (pow_le_evPiece _ h1 b)).trans (evPiece_mul_le _ _ _)

end TwoBlock

end TwoBlockPieceIndex

open TwoBlockPieceIndex in

theorem TwoBlockPieceIndex.proof : TwoBlockPieceIndex.Statement := by
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl a b
  have hxc : x ⟨(), c⟩ ≠ 0 := hx.ne_zero _
  set x' := matAct B x with hx'
  have hnum : IsMultiHomog (twoBlockNum l) (Pi.single 1 1) := by
    refine (mem_mHom_iff _ _).mp (Submodule.sum_mem _ fun j _ => ?_)
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_mHom_iff _ _).mpr (isMultiHomog_X' (ι := FinTwoTypeFamily κ) 1 j.2))
  have hout := map_piece (pair x x') (isMultiHomog_X' (ι := FinTwoTypeFamily κ) 0 c) 1 ![a, b]
  have hin := map_piece (pair x x') hnum 0 ![a, b]
  have d1 : (![a, b] + (Pi.single 0 1 + Pi.single 1 1) : Fin 2 → ℕ) = ![a + 1, b + 1] := by
    funext k
    fin_cases k <;> simp
  have d2 : (![a, b] + (Pi.single 1 1 + Pi.single 0 1) : Fin 2 → ℕ) = ![a + 1, b + 1] := by
    funext k
    fin_cases k <;> simp
  have gout : aeval (pair x x') (X ⟨0, c⟩ : MRing (FinTwoTypeFamily κ)) = x ⟨(), c⟩ := by simp [pair]
  have gin : aeval (pair x x') (twoBlockNum l) = x ⟨(), c⟩ := by
    rw [hl]
    simp [twoBlockNum, pair, hx']
  rw [d1, gout] at hout
  rw [d2, gin] at hin
  have hY1 : Submodule.span ℤ (Set.range fun j : κ => pair x x' ⟨1, j⟩) = Submodule.span ℤ (Set.range x') := by
    congr 1
    ext v
    simp only [Set.mem_range, pair]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨(), i⟩, by simp⟩
    · rintro ⟨⟨⟨⟩, i⟩, rfl⟩
      exact ⟨i, by simp⟩
  have hY0 : Submodule.span ℤ (Set.range fun j : κ => pair x x' ⟨0, j⟩) = Submodule.span ℤ (Set.range x) := by
    congr 1
    ext v
    simp only [Set.mem_range, pair]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨(), i⟩, by simp⟩
    · rintro ⟨⟨⟨⟩, i⟩, rfl⟩
      exact ⟨i, by simp⟩
  have hker : ∀ u ∈ mHom (FinTwoTypeFamily κ) ![a + 1, b + 1], (aeval (pair x x')).toLinearMap u = 0 →
      u ∈ (twoBlockMInner x x' l).restrictScalars ℤ ⊓ mHom (FinTwoTypeFamily κ) ![a + 1, b + 1] := fun u hu h0 =>
    ⟨(Submodule.restrictScalars_mem ℤ _ _).mpr
      (Ideal.mem_sup_left (mem_mCoordIdeal_of_homog _ ((mem_mHom_iff _ _).mp hu) h0)), hu⟩
  unfold twoBlockStep modPieceCard
  rw [relIndex_eq_map (aeval (pair x x')).toLinearMap inf_le_right inf_le_right hker]
  have eo : ((twoBlockMOuter x x' c).restrictScalars ℤ ⊓ mHom (FinTwoTypeFamily κ) ![a + 1, b + 1]).map
      (aeval (pair x x')).toLinearMap = _ := hout
  have ei : ((twoBlockMInner x x' l).restrictScalars ℤ ⊓ mHom (FinTwoTypeFamily κ) ![a + 1, b + 1]).map
      (aeval (pair x x')).toLinearMap = _ := hin
  rw [eo, ei, relIndex_map_mulLeft hxc, evPiece_pair, hY1, hY0]
  have e1 : Submodule.span ℤ (Set.range x) * (sec ℤ x a * sec ℤ x' b) = sec ℤ x (a + 1) * sec ℤ x' b := by
    simp only [sec_eq_span_pow]
    ring
  have e2 : Submodule.span ℤ (Set.range x') * (sec ℤ x a * sec ℤ x' b) = sec ℤ x a * sec ℤ x' (b + 1) := by
    simp only [sec_eq_span_pow]
    ring
  rw [e1, e2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
