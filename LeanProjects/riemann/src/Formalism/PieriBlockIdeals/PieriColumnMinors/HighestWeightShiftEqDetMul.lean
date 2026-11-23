import Formalism.PieriBlockIdeals.ExZTranslate
import Formalism.PieriBlockIdeals.PieriColumnMinors.ProdInitialMinorsMemDetSpan

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LA

open Formalism.GradedWeylDivisibility

def genericMatrix' (R : Type) [CommRing R] (r : ℕ) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) R) :=
  Matrix.of fun p q : Fin r => (X (p, q) : MvPolynomial (Fin r × Fin r) R)

def genericDet (R : Type) [CommRing R] (r : ℕ) : MvPolynomial (Fin r × Fin r) R :=
  (genericMatrix' R r).det

theorem leading_minor_full_eq_det (R : Type) [CommRing R] {r : ℕ} (s : ℕ) (hs : s = r) (hr : s ≤ r)
    (hn : s ≤ r) : lpMinor R s hr hn = genericDet R r := by
  subst hs
  rfl

theorem row_generator_det_of_ne (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (hab : a ≠ b) :
    rowGen R a b (genericDet R r) = Polynomial.C (genericDet R r) := by
  have hM : (rowGen R a b).mapMatrix (genericMatrix' R r) =
      (RingHom.mapMatrix Polynomial.C (genericMatrix' R r)).updateRow b
        (RingHom.mapMatrix Polynomial.C (genericMatrix' R r) b +
          (Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin r) R)) •
            RingHom.mapMatrix Polynomial.C (genericMatrix' R r) a) := by
    ext p q
    by_cases hp : p = b
    · subst hp
      simp [rowGen, genericMatrix', Matrix.updateRow_apply]
    · simp [rowGen, genericMatrix', Matrix.updateRow_apply, hp]
  unfold genericDet
  rw [AlgHom.map_det (rowGen R a b), hM, Matrix.det_updateRow_add_smul_self _ (Ne.symm hab),
    ← RingHom.map_det]

theorem row_generator_det_diag (R : Type) [CommRing R] {r : ℕ} (a : Fin r) :
    rowGen R a a (genericDet R r) = Polynomial.C (genericDet R r) * (1 + Polynomial.X) := by
  have hM : (rowGen R a a).mapMatrix (genericMatrix' R r) =
      (RingHom.mapMatrix Polynomial.C (genericMatrix' R r)).updateRow a
        ((1 + Polynomial.X : Polynomial (MvPolynomial (Fin r × Fin r) R)) •
          RingHom.mapMatrix Polynomial.C (genericMatrix' R r) a) := by
    refine Matrix.ext fun p q => ?_
    by_cases hp : p = a
    · subst hp
      simp [rowGen, genericMatrix', Matrix.updateRow_apply] <;> ring
    · simp [rowGen, genericMatrix', Matrix.updateRow_apply, hp]
  unfold genericDet
  rw [AlgHom.map_det (rowGen R a a), hM, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    ← RingHom.map_det]
  ring

theorem divided_power_det_mul_of_ne (R : Type) [CommRing R] {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a b k (genericDet R r * f) = genericDet R r * rowDiv R a b k f := by
  unfold rowDiv
  rw [map_mul, row_generator_det_of_ne R a b hab, Polynomial.coeff_C_mul]

theorem divided_power_zero_det_mul (R : Type) [CommRing R] {r : ℕ} (a : Fin r)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a a 0 (genericDet R r * f) = genericDet R r * rowDiv R a a 0 f := by
  unfold rowDiv
  rw [map_mul, row_generator_det_diag, mul_assoc, Polynomial.coeff_C_mul, add_mul, one_mul,
    Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, add_zero]

theorem divided_power_succ_det_mul (R : Type) [CommRing R] {r : ℕ} (a : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin r) R) :
    rowDiv R a a (k + 1) (genericDet R r * f) =
      genericDet R r * (rowDiv R a a (k + 1) f + rowDiv R a a k f) := by
  unfold rowDiv
  rw [map_mul, row_generator_det_diag, mul_assoc, Polynomial.coeff_C_mul, add_mul, one_mul,
    Polynomial.coeff_add, Polynomial.coeff_X_mul]

theorem divided_power_stable_det_mul (R : Type) [CommRing R] {r : ℕ}
    (L : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ L →
      rowDiv R a b k f ∈ L) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ L.map (LinearMap.mulLeft R (genericDet R r))) :
    rowDiv R a b k f ∈ L.map (LinearMap.mulLeft R (genericDet R r)) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
  rw [LinearMap.mulLeft_apply]
  by_cases hab : a = b
  · subst hab
    cases k with
    | zero =>
      rw [divided_power_zero_det_mul]
      exact Submodule.mem_map.mpr ⟨_, hs a a 0 g hg, by simp⟩
    | succ k =>
      rw [divided_power_succ_det_mul]
      exact Submodule.mem_map.mpr ⟨_, L.add_mem (hs a a (k + 1) g hg) (hs a a k g hg), by simp⟩
  · rw [divided_power_det_mul_of_ne R a b hab]
    exact Submodule.mem_map.mpr ⟨_, hs a b k g hg, by simp⟩

theorem det_mul_divided_power_mem (R : Type) [CommRing R] {r : ℕ}
    (W : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hW : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ W →
      rowDiv R a b k f ∈ W) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : genericDet R r * f ∈ W) : genericDet R r * rowDiv R a b k f ∈ W := by
  by_cases hab : a = b
  · subst hab
    induction k with
    | zero =>
      rw [← divided_power_zero_det_mul]
      exact hW a a 0 _ hf
    | succ k ih =>
      have h1 := hW a a (k + 1) _ hf
      rw [divided_power_succ_det_mul, mul_add] at h1
      have h2 := W.sub_mem h1 ih
      simpa using h2
  · rw [← divided_power_det_mul_of_ne R a b hab]
    exact hW a b k _ hf

theorem highest_weight_shift_eq_det_mul (R : Type) [CommRing R] {r : ℕ} (ν : Fin r → ℕ) :
    hw R le_rfl (fun a => ν a + 1) = genericDet R r * hw R le_rfl ν := by
  cases r with
  | zero => simp [hw, genericDet]
  | succ r =>
    have hl : ∀ μ : Fin (r + 1) → ℕ, nuNext μ (Fin.last r) = 0 := fun μ => by simp [nuNext]
    have key : ∀ i : Fin r, ν i.castSucc + 1 - nuNext (fun a => ν a + 1) i.castSucc =
        ν i.castSucc - nuNext ν i.castSucc := by
      intro i
      have hs : (Fin.castSucc i).val + 1 < r + 1 := by
        have := i.isLt
        simp only [Fin.coe_castSucc]
        omega
      simp only [nuNext, dif_pos hs]
      omega
    have hL : ∀ (h1 : (Fin.last r).val + 1 ≤ r + 1) (h2 : (Fin.last r).val + 1 ≤ r + 1),
        lpMinor R ((Fin.last r).val + 1) h1 h2 = genericDet R (r + 1) :=
      fun h1 h2 => leading_minor_full_eq_det R _ (by simp) h1 h2
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [key, hl, Nat.sub_zero, hL]
    ring

theorem highest_weight_ones_eq_det (R : Type) [CommRing R] (r : ℕ) :
    hw R le_rfl (fun _ : Fin r => 1) = genericDet R r := by
  have h := highest_weight_shift_eq_det_mul R (fun _ : Fin r => 0)
  have h0 : hw R le_rfl (fun _ : Fin r => 0) = 1 := by simp [hw]
  simpa [h0] using h

private theorem divOp_mem_weyl (R : Type) [CommRing R] {r : ℕ} (μ : Fin r → ℕ)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ weyl R r r le_rfl μ) : rowDiv R a b k f ∈ weyl R r r le_rfl μ := by
  unfold weyl at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨(a, b, k) :: w, rfl⟩
  | zero => simp [rowDiv]
  | add x y _ _ hx hy =>
    unfold rowDiv at hx hy ⊢
    rw [map_add, Polynomial.coeff_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    unfold rowDiv at hx ⊢
    rw [map_smul, Polynomial.coeff_smul]
    exact Submodule.smul_mem _ c hx

private theorem applyWord_mem_of_stable' (R : Type) [CommRing R] {r : ℕ}
    (L : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ L →
      rowDiv R a b k f ∈ L) (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ L) : applyWord R w f ∈ L := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact hs x.1 x.2.1 x.2.2 _ ih

private theorem hw_mem_weyl (R : Type) [CommRing R] {r : ℕ} (μ : Fin r → ℕ) :
    hw R le_rfl μ ∈ weyl R r r le_rfl μ := by
  unfold weyl
  exact Submodule.subset_span ⟨[], rfl⟩

private theorem genericDet_mul_applyWord_mem (R : Type) [CommRing R] {r : ℕ}
    (W : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hW : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ W →
      rowDiv R a b k f ∈ W) (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : genericDet R r * f ∈ W) : genericDet R r * applyWord R w f ∈ W := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact det_mul_divided_power_mem R W hW x.1 x.2.1 x.2.2 _ ih

theorem weyl_shift_eq_map_det_mul (R : Type) [CommRing R] {r : ℕ} (ν : Fin r → ℕ) :
    weyl R r r le_rfl (fun a => ν a + 1) =
      (weyl R r r le_rfl ν).map (LinearMap.mulLeft R (genericDet R r)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe]
    rw [highest_weight_shift_eq_det_mul]
    exact applyWord_mem_of_stable' R ((weyl R r r le_rfl ν).map (LinearMap.mulLeft R (genericDet R r)))
      (fun a b k f hf => divided_power_stable_det_mul R (weyl R r r le_rfl ν) (divOp_mem_weyl R ν) a b k f hf)
      w _ (Submodule.mem_map.mpr ⟨_, hw_mem_weyl R ν, by simp⟩)
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    apply genericDet_mul_applyWord_mem R (weyl R r r le_rfl (fun a => ν a + 1))
      (divOp_mem_weyl R (fun a => ν a + 1)) w
    rw [← highest_weight_shift_eq_det_mul]
    exact hw_mem_weyl R _

theorem generic_det_ne_zero (r : ℕ) : genericDet ℤ r ≠ 0 := by
  exact Matrix.det_mvPolynomialX_ne_zero (Fin r) ℤ

theorem det_mem_dual_weyl_ones (r : ℕ) : genericDet ℤ r ∈ dualWeyl ℤ r r (fun _ => 1) := by
  unfold dualWeyl
  rw [Submodule.mem_inf]
  constructor
  · unfold genericDet
    rw [Matrix.det_apply]
    refine Submodule.sum_mem _ (fun σ _ => ?_)
    rw [Units.smul_def]
    refine Submodule.smul_mem _ _ ?_
    rw [mem_weightedHomogeneousSubmodule]
    have hp := IsWeightedHomogeneous.prod (w := colW r r) Finset.univ
      (fun i => genericMatrix' ℤ r (σ i) i) (fun i => colW r r (σ i, i))
      (fun i _ => by simpa [genericMatrix'] using isWeightedHomogeneous_X (R := ℤ) (w := colW r r) (σ i, i))
    convert hp using 1
    funext t
    simp [colW, Finset.sum_apply, Pi.single_apply]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero]
    intro l j hlj
    have hM : (colAddGen ℤ l j).mapMatrix (genericMatrix' ℤ r) =
        Matrix.transpose ((Matrix.transpose ((rename (R := ℤ)
          (some : Fin r × Fin r → Option (Fin r × Fin r))).mapMatrix (genericMatrix' ℤ r))).updateRow j
          (Matrix.transpose ((rename (R := ℤ)
            (some : Fin r × Fin r → Option (Fin r × Fin r))).mapMatrix (genericMatrix' ℤ r)) j +
          (X none : MvPolynomial (Option (Fin r × Fin r)) ℤ) •
            Matrix.transpose ((rename (R := ℤ)
              (some : Fin r × Fin r → Option (Fin r × Fin r))).mapMatrix (genericMatrix' ℤ r)) l)) := by
      ext p q
      by_cases hq : q = j
      · subst hq
        simp [colAddGen, genericMatrix', Matrix.updateRow_apply]
      · simp [colAddGen, genericMatrix', Matrix.updateRow_apply, hq]
    unfold genericDet
    rw [AlgHom.map_det (colAddGen ℤ l j), hM, Matrix.det_transpose,
      Matrix.det_updateRow_add_smul_self _ hlj.ne', Matrix.det_transpose, ← AlgHom.map_det]

theorem weighted_homogeneous_cancel {σ : Type} {n : ℕ} (w : σ → Fin n → ℕ) (D g : MvPolynomial σ ℤ)
    (δ ν : Fin n → ℕ) (hD0 : D ≠ 0) (hD : IsWeightedHomogeneous w D δ)
    (h : IsWeightedHomogeneous w (D * g) (δ + ν)) : IsWeightedHomogeneous w g ν := by
  classical
  unfold IsWeightedHomogeneous
  intro d hd
  by_contra hne
  have key : ∀ e : σ →₀ ℕ,
      coeff e (D * weightedHomogeneousComponent w (Finsupp.weight w d) g) =
        if Finsupp.weight w e = δ + Finsupp.weight w d then coeff e (D * g) else 0 := by
    intro e
    rw [coeff_mul, coeff_mul]
    split_ifs with he
    · refine Finset.sum_congr rfl ?_
      rintro ⟨x, y⟩ hxy
      have hxy' : x + y = e := by
        first
          | simpa using hxy
          | exact Finset.mem_antidiagonal.mp hxy
          | exact Finsupp.mem_antidiagonal.mp hxy
      dsimp only
      rw [coeff_weightedHomogeneousComponent]
      split_ifs with hy
      · rfl
      · by_cases hx : coeff x D = 0
        · simp [hx]
        · exfalso
          apply hy
          have h1 := hD hx
          rw [← hxy', map_add, h1] at he
          exact add_left_cancel he
    · refine Finset.sum_eq_zero ?_
      rintro ⟨x, y⟩ hxy
      have hxy' : x + y = e := by
        first
          | simpa using hxy
          | exact Finset.mem_antidiagonal.mp hxy
          | exact Finsupp.mem_antidiagonal.mp hxy
      dsimp only
      rw [coeff_weightedHomogeneousComponent]
      split_ifs with hy
      · by_cases hx : coeff x D = 0
        · simp [hx]
        · exfalso
          apply he
          rw [← hxy', map_add, hD hx, hy]
      · simp
  have hz : D * weightedHomogeneousComponent w (Finsupp.weight w d) g = 0 := by
    ext e
    rw [key, coeff_zero]
    split_ifs with he
    · by_contra hc
      apply hne
      have h3 := h hc
      rw [he] at h3
      exact add_left_cancel h3
    · rfl
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact hD0 h0
  · apply hd
    have h4 := congrArg (coeff d) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at h4
    exact h4

theorem det_mul_mem_dual_weyl_shift {r : ℕ} (ν : Fin r → ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (hg : g ∈ dualWeyl ℤ r r ν) : genericDet ℤ r * g ∈ dualWeyl ℤ r r (fun a => ν a + 1) := by
  have hd := det_mem_dual_weyl_ones r
  unfold dualWeyl at hg hd ⊢
  rw [Submodule.mem_inf] at hg hd ⊢
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hd1, hd2⟩ := hd
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at hg1 hd1 ⊢
    have h := hd1.mul hg1
    convert h using 1
    funext a
    simp only [Pi.add_apply]
    omega
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at hg2 hd2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hd2 l j hlj, hg2 l j hlj]

theorem mem_dual_weyl_of_det_mul {r : ℕ} (ν : Fin r → ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (h : genericDet ℤ r * g ∈ dualWeyl ℤ r r (fun a => ν a + 1)) : g ∈ dualWeyl ℤ r r ν := by
  have hd := det_mem_dual_weyl_ones r
  have hne : rename (R := ℤ) (some : Fin r × Fin r → Option (Fin r × Fin r)) (genericDet ℤ r) ≠ 0 := by
    intro h0
    apply generic_det_ne_zero r
    apply MvPolynomial.rename_injective _ (Option.some_injective _)
    rw [h0, map_zero]
  unfold dualWeyl at h hd ⊢
  rw [Submodule.mem_inf] at h hd ⊢
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hd1, hd2⟩ := hd
  constructor
  · rw [mem_weightedHomogeneousSubmodule] at h1 hd1 ⊢
    have e : (fun a => ν a + 1) = (fun _ => 1) + ν := by
      funext a
      simp only [Pi.add_apply]
      omega
    rw [e] at h1
    exact weighted_homogeneous_cancel (colW r r) (genericDet ℤ r) g (fun _ => 1) ν (generic_det_ne_zero r) hd1 h1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      AlgHom.toLinearMap_apply, sub_eq_zero] at h2 hd2 ⊢
    intro l j hlj
    have h3 := h2 l j hlj
    rw [map_mul, map_mul, hd2 l j hlj] at h3
    exact mul_left_cancel₀ hne h3

private theorem genericDet_dvd_of_nsmul_eq_mul {r : ℕ} (N : ℕ) (hN : N ≠ 0)
    (f g : MvPolynomial (Fin r × Fin r) ℤ) (h : (N : ℤ) • f = genericDet ℤ r * g) :
    genericDet ℤ r ∣ f := by
  have hev : MvPolynomial.eval (fun v : Fin r × Fin r => if v.1 = v.2 then (1 : ℤ) else 0)
      (genericDet ℤ r) = 1 := by
    unfold genericDet
    rw [RingHom.map_det]
    have hM : (MvPolynomial.eval (fun v : Fin r × Fin r => if v.1 = v.2 then (1 : ℤ) else 0)).mapMatrix
        (genericMatrix' ℤ r) = 1 := by
      ext p q
      simp [genericMatrix', Matrix.one_apply]
    rw [hM, Matrix.det_one]
  have hnd : ∀ p : ℕ, p.Prime → ¬ (C (p : ℤ) ∣ genericDet ℤ r) := by
    rintro p hp ⟨h', hh⟩
    have he := congrArg (MvPolynomial.eval (fun v : Fin r × Fin r =>
      if v.1 = v.2 then (1 : ℤ) else 0)) hh
    rw [hev, map_mul, eval_C] at he
    have h1 : (p : ℤ) ∣ 1 := ⟨_, he⟩
    have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
    exact hp.one_lt.ne' (by exact_mod_cast h2)
  revert f g
  refine Nat.recOnMul (motive := fun N => N ≠ 0 → ∀ f g : MvPolynomial (Fin r × Fin r) ℤ,
    (N : ℤ) • f = genericDet ℤ r * g → genericDet ℤ r ∣ f) ?_ ?_ ?_ ?_ N hN
  · intro h0
    exact absurd rfl h0
  · intro _ f g h
    rw [Nat.cast_one, one_smul] at h
    exact ⟨g, h⟩
  · intro p hp _ f g h
    have hpr : Prime (C (p : ℤ) : MvPolynomial (Fin r × Fin r) ℤ) :=
      (MvPolynomial.prime_C_iff (Fin r × Fin r)).mpr (Nat.prime_iff_prime_int.mp hp)
    rw [MvPolynomial.smul_eq_C_mul] at h
    rcases hpr.dvd_or_dvd ⟨f, h.symm⟩ with hd | ⟨g', rfl⟩
    · exact absurd hd (hnd p hp)
    · refine ⟨g', mul_left_cancel₀ hpr.ne_zero ?_⟩
      rw [h]
      ring
  · intro a b ha hb hab f g h
    have h' : (a : ℤ) • ((b : ℤ) • f) = genericDet ℤ r * g := by
      rw [smul_smul, ← Nat.cast_mul]
      exact h
    obtain ⟨g', hg'⟩ := ha (left_ne_zero_of_mul hab) _ g h'
    exact hb (right_ne_zero_of_mul hab) f g' hg'

theorem det_dvd_of_mem_dual_weyl_shift {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν)
    {f : MvPolynomial (Fin r × Fin r) ℤ} (hf : f ∈ dualWeyl ℤ r r (fun a => ν a + 1)) :
    genericDet ℤ r ∣ f := by
  obtain ⟨N, hN, hNx⟩ := la_uniform r r le_rfl (fun a => ν a + 1)
    (fun a b hab => Nat.add_le_add_right (hν hab) 1)
  have hmem := hNx f hf
  rw [weyl_shift_eq_map_det_mul] at hmem
  obtain ⟨g, -, hg⟩ := Submodule.mem_map.mp hmem
  exact genericDet_dvd_of_nsmul_eq_mul N hN f g (by rw [← hg, LinearMap.mulLeft_apply])

theorem incl_z_shift_by_one_iff (r : ℕ) (ν : Fin r → ℕ) (l e : ℕ) (hν : Antitone ν) :
    InclZ r r le_rfl (fun a => ν a + 1) l e ↔ InclZ r r le_rfl ν l e := by
  unfold InclZ
  have hW := weyl_shift_eq_map_det_mul ℤ ν
  have hdn := generic_det_ne_zero r
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, fun x hx => ?_⟩
    have h1 := h _ (det_mul_mem_dual_weyl_shift ν hx)
    rw [hW] at h1
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp h1
    rw [LinearMap.mulLeft_apply] at hxy
    have hyx : y = ((m * l ^ e : ℕ) : ℤ) • x := by
      apply mul_left_cancel₀ hdn
      rw [hxy, mul_smul_comm]
    rw [← hyx]
    exact hy
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, fun x hx => ?_⟩
    obtain ⟨g, rfl⟩ := det_dvd_of_mem_dual_weyl_shift ν hν hx
    have hg := mem_dual_weyl_of_det_mul ν hx
    rw [hW, ← mul_smul_comm]
    exact Submodule.mem_map.mpr ⟨_, h g hg, by simp⟩

theorem incl_z_twist_by_det : InclZTwist := by
  unfold InclZTwist
  intro r ν c l e hν hl
  induction c with
  | zero => simp
  | succ c ih =>
    have hνc : Antitone (fun a => ν a + c) := fun a b hab => Nat.add_le_add_right (hν hab) c
    have he : (fun a => ν a + (c + 1)) = (fun a => (fun a => ν a + c) a + 1) := by
      funext a
      show ν a + (c + 1) = ν a + c + 1
      omega
    rw [he]
    exact (incl_z_shift_by_one_iff r (fun a => ν a + c) l e hνc).trans ih

theorem exact_z_twist_by_det : ExZTwist := by
  unfold ExZTwist
  intro r ν c l hν hl
  have h : ∀ e, InclZ r r le_rfl (fun a => ν a + c) l e ↔ InclZ r r le_rfl ν l e :=
    fun e => incl_z_twist_by_det r ν c l e hν hl
  unfold exZ
  simp only [h]

end Formalism.CohomologicalDescent.LA
