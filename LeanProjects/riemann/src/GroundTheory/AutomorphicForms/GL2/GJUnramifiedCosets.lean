import Mathlib
import GroundTheory.AutomorphicForms.Satake
import GroundTheory.AutomorphicForms.GL2.GJUnramifiedDegree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra
open ValuativeRel (valuation)
open scoped ValuativeRel Pointwise

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "ϖ" => (GLnLocal.uniformizer F : F)

variable (F) in

def digitSum (m : ℕ) (a : Fin m → 𝓀[F]) : F :=
  ∑ t : Fin m, (residueLift F (a t) : F) * ϖ ^ (t : ℕ)

theorem digitSum_succ (m : ℕ) (a : Fin (m + 1) → 𝓀[F]) :
    digitSum F (m + 1) a = residueLift F (a 0) + ϖ * digitSum F m (Fin.tail a) := by
  rw [digitSum, Fin.sum_univ_succ, digitSum, Finset.mul_sum]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Fin.tail]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by ring

theorem digitSum_mem (m : ℕ) (a : Fin m → 𝓀[F]) : digitSum F m a ∈ 𝒪[F] :=
  Subring.sum_mem _ fun t _ =>
    Subring.mul_mem _ (residueLift F (a t)).2 (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _)

theorem exists_eq_uniformizer_pow_mul {m : ℕ} {x : F} (hx : Bdd F m x) :
    ∃ y ∈ 𝒪[F], x = ϖ ^ m * y := by
  have hϖ : ϖ ≠ 0 := Cartan.uniformizer_ne_zero F
  refine ⟨(ϖ ^ m)⁻¹ * x, ?_, by rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hϖ), one_mul]⟩
  apply mem_of_bdd
  have := (bdd_zpow (F := F) (-(m : ℤ))).mul hx
  rwa [neg_add_cancel, _root_.zpow_neg, zpow_natCast] at this

theorem exists_digitSum (m : ℕ) {x : F} (hx : x ∈ 𝒪[F]) :
    ∃ a : Fin m → 𝓀[F], Bdd F m (x - digitSum F m a) := by
  induction m generalizing x with
  | zero => exact ⟨Fin.elim0, by simpa [digitSum] using bdd_of_mem hx⟩
  | succ m ih =>
    set a₀ := IsLocalRing.residue 𝒪[F] ⟨x, hx⟩
    have h1 : Bdd F 1 (x - residueLift F a₀) := by
      have := (bdd_one_of_mem_maximalIdeal (residueLift_sub_mem (F := F) ⟨x, hx⟩)).neg
      convert this using 1
      push_cast
      ring
    obtain ⟨y, hy, hxy⟩ := exists_eq_uniformizer_pow_mul (m := 1) (by simpa using h1)
    obtain ⟨a', ha'⟩ := ih hy
    refine ⟨Fin.cons a₀ a', ?_⟩
    rw [digitSum_succ, Fin.cons_zero, Fin.tail_cons]
    have heq : x - ((residueLift F a₀ : F) + ϖ * digitSum F m a') = ϖ * (y - digitSum F m a') := by
      rw [mul_sub, ← pow_one ϖ, ← hxy]
      ring
    rw [heq]
    have := (bdd_zpow (F := F) 1).mul ha'
    rw [zpow_one] at this
    convert this using 1
    push_cast
    ring

theorem eq_of_bdd_digitSum_sub (m : ℕ) {a b : Fin m → 𝓀[F]}
    (h : Bdd F m (digitSum F m a - digitSum F m b)) : a = b := by
  induction m with
  | zero => exact funext fun t => t.elim0
  | succ m ih =>
    rw [digitSum_succ, digitSum_succ] at h
    set D := digitSum F m (Fin.tail a) - digitSum F m (Fin.tail b)
    have hD : D ∈ 𝒪[F] := Subring.sub_mem _ (digitSum_mem _ _) (digitSum_mem _ _)
    have hd : (residueLift F (a 0) : F) + ϖ * digitSum F m (Fin.tail a) -
        ((residueLift F (b 0) : F) + ϖ * digitSum F m (Fin.tail b)) =
        ((residueLift F (a 0) : F) - residueLift F (b 0)) + ϖ * D := by
      simp only [D]; ring
    rw [hd] at h
    have hϖD : Bdd F 1 (ϖ * D) := by
      have := (bdd_zpow (F := F) 1).mul (bdd_of_mem hD)
      rwa [zpow_one, add_zero] at this
    have h0 : Bdd F 1 ((residueLift F (a 0) : F) - residueLift F (b 0)) := by
      have := (h.mono (show (1 : ℤ) ≤ ((m + 1 : ℕ) : ℤ) by omega)).add hϖD.neg
      rwa [add_neg_cancel_right] at this
    have ha0 : a 0 = b 0 := by
      have hmax : residueLift F (a 0) - residueLift F (b 0) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
        have := (mem_maximalIdeal_pow_iff F (m := 1)
          (y := residueLift F (a 0) - residueLift F (b 0))).2 (by
            rw [pow_one]
            push_cast
            simpa [Bdd] using h0)
        rwa [pow_one] at this
      have := (IsLocalRing.residue_eq_zero_iff _).2 hmax
      rw [map_sub, residue_residueLift, residue_residueLift, sub_eq_zero] at this
      exact this
    have htail : Bdd F m D := by
      rw [ha0, sub_self, zero_add] at h
      have := (bdd_zpow (F := F) (-1)).mul h
      rw [← mul_assoc, ← zpow_add_one₀ (Cartan.uniformizer_ne_zero F), neg_add_cancel, zpow_zero,
        one_mul] at this
      convert this using 1
      push_cast
      ring
    have ht := ih htail
    funext t
    refine Fin.cases ha0 (fun t => ?_) t
    exact congrFun ht t

abbrev UpperPairs (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

variable (F) in

abbrev NormalData (l : Fin n → ℕ) : Type _ := ∀ p : UpperPairs n, Fin (l p.1.1) → 𝓀[F]

variable (F) in

def normalMat (l : Fin n → ℕ) (c : NormalData F l) : Matrix (Fin n) (Fin n) F :=
  fun i j => if h : i < j then digitSum F (l i) (c ⟨(i, j), h⟩) else if i = j then ϖ ^ l i else 0

theorem normalMat_of_lt (l : Fin n → ℕ) (c : NormalData F l) {i j : Fin n} (h : i < j) :
    normalMat F l c i j = digitSum F (l i) (c ⟨(i, j), h⟩) := by
  simp [normalMat, h]

theorem normalMat_self (l : Fin n → ℕ) (c : NormalData F l) (i : Fin n) :
    normalMat F l c i i = ϖ ^ l i := by
  simp [normalMat]

theorem normalMat_of_gt (l : Fin n → ℕ) (c : NormalData F l) {i j : Fin n} (h : j < i) :
    normalMat F l c i j = 0 := by
  simp [normalMat, not_lt.2 h.le, (ne_of_lt h).symm]

theorem normalMat_isUpperTriangular (l : Fin n → ℕ) (c : NormalData F l) :
    (normalMat F l c).IsUpperTriangular := fun _ _ h => normalMat_of_gt l c h

theorem det_normalMat (l : Fin n → ℕ) (c : NormalData F l) :
    (normalMat F l c).det = ∏ i, ϖ ^ l i := by
  rw [det_of_isUpperTriangular (normalMat_isUpperTriangular l c)]
  exact Finset.prod_congr rfl fun i _ => normalMat_self l c i

theorem det_normalMat_ne_zero (l : Fin n → ℕ) (c : NormalData F l) : (normalMat F l c).det ≠ 0 := by
  rw [det_normalMat]
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Cartan.uniformizer_ne_zero F)

variable (F) in

def normalGL (l : Fin n → ℕ) (c : NormalData F l) : GL (Fin n) F :=
  ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_normalMat_ne_zero l c))).unit

theorem coe_normalGL (l : Fin n → ℕ) (c : NormalData F l) :
    (normalGL F l c : Matrix (Fin n) (Fin n) F) = normalMat F l c :=
  IsUnit.unit_spec _

theorem normalGL_mem_borel (l : Fin n → ℕ) (c : NormalData F l) : normalGL F l c ∈ Iwasawa.borel F n := by
  rw [Iwasawa.mem_borel, coe_normalGL]
  exact normalMat_isUpperTriangular l c

theorem iwasawaExponent_normalGL (l : Fin n → ℕ) (c : NormalData F l) :
    iwasawaExponent F n (normalGL F l c) = fun i => (l i : ℤ) := by
  set L : Fin n → ℤ := fun i => (l i : ℤ)
  set u := normalGL F l c * torusPow F n (-L) with hu
  have huN : u ∈ unipotent F n := by
    refine (mem_unipotent F n).2 ⟨(Iwasawa.borel F n).mul_mem (normalGL_mem_borel l c)
      (torusPow_mem_borel F n _), fun i => ?_⟩
    rw [hu, mul_apply_self_of_mem_borel F n (normalGL_mem_borel l c) (torusPow_mem_borel F n _)]
    rw [coe_normalGL, normalMat_self, coe_torusPow, diagonal_apply_eq, Pi.neg_apply, ← zpow_natCast,
      ← zpow_add₀ (Cartan.uniformizer_ne_zero F), add_neg_cancel, zpow_zero]
  have : normalGL F l c = u * torusPow F n L * 1 := by
    rw [mul_one, hu, torusPow_neg, inv_mul_cancel_right]
  rw [this]
  exact iwasawaExponent_eq F n huN (integralGL F n).one_mem

theorem normalGL_injective (l : Fin n → ℕ) :
    Function.Injective fun c : NormalData F l =>
      (QuotientGroup.mk (normalGL F l c) : GL (Fin n) F ⧸ integralGL F n) := by
  intro c c' h
  have hϖ : ϖ ≠ 0 := Cartan.uniformizer_ne_zero F
  have hk : (normalGL F l c)⁻¹ * normalGL F l c' ∈ integralGL F n := QuotientGroup.eq.1 h
  set b := normalGL F l c with hbdef
  set b' := normalGL F l c' with hb'def
  set k := b⁻¹ * b' with hkdef
  have hb : b ∈ Iwasawa.borel F n := normalGL_mem_borel l c
  have hb' : b' ∈ Iwasawa.borel F n := normalGL_mem_borel l c'
  have hbU : (b : Matrix (Fin n) (Fin n) F).IsUpperTriangular := (Iwasawa.mem_borel F n).1 hb
  have hkB : k ∈ Iwasawa.borel F n := (Iwasawa.borel F n).mul_mem ((Iwasawa.borel F n).inv_mem hb) hb'
  have hkU : (k : Matrix (Fin n) (Fin n) F).IsUpperTriangular := (Iwasawa.mem_borel F n).1 hkB
  have hkO : ∀ i j, k i j ∈ 𝒪[F] := ((mem_integralGL_iff F n).1 hk).1
  have hbk : (b' : Matrix (Fin n) (Fin n) F) = (b : Matrix (Fin n) (Fin n) F) * k := by
    rw [← Units.val_mul, hkdef, mul_inv_cancel_left]
  have hbd : ∀ i, (b : Matrix (Fin n) (Fin n) F) i i = ϖ ^ l i := fun i => by
    rw [hbdef, coe_normalGL, normalMat_self]
  have hb'd : ∀ i, (b' : Matrix (Fin n) (Fin n) F) i i = ϖ ^ l i := fun i => by
    rw [hb'def, coe_normalGL, normalMat_self]
  have hkdiag : ∀ j, k j j = 1 := by
    intro j
    rw [hkdef, mul_apply_self_of_mem_borel F n ((Iwasawa.borel F n).inv_mem hb) hb',
      inv_apply_self_of_mem_borel F n hb]
    rw [hbd, hb'd, inv_mul_cancel₀ (pow_ne_zero _ hϖ)]
  have key : ∀ d : ℕ, ∀ i j : Fin n, ∀ hij : i < j, (j : ℕ) - i = d →
      k i j = 0 ∧ c ⟨(i, j), hij⟩ = c' ⟨(i, j), hij⟩ := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro i j hij hd
    have hsum : (b' : Matrix (Fin n) (Fin n) F) i j =
        ϖ ^ l i * k i j + (b : Matrix (Fin n) (Fin n) F) i j := by
      rw [hbk, Matrix.mul_apply, Fintype.sum_eq_add i j (ne_of_lt hij)]
      · rw [hbd, hkdiag, mul_one]
      · rintro m ⟨hmi, hmj⟩
        rcases lt_or_gt_of_ne hmi with hm | hm
        · rw [hbU hm, zero_mul]
        · rcases lt_or_gt_of_ne hmj with hm' | hm'
          · have hmj' : (j : ℕ) - m < d := by
              have := Fin.lt_def.1 hm
              have := Fin.lt_def.1 hm'
              omega
            rw [(ih _ hmj' m j hm' rfl).1, mul_zero]
          · rw [hkU hm', mul_zero]
    rw [hbdef, hb'def, coe_normalGL, coe_normalGL, normalMat_of_lt l c' hij,
      normalMat_of_lt l c hij] at hsum
    have hbdd : Bdd F (l i) (digitSum F (l i) (c ⟨(i, j), hij⟩) -
        digitSum F (l i) (c' ⟨(i, j), hij⟩)) := by
      rw [hsum]
      have := ((bdd_zpow (F := F) (l i)).mul (bdd_of_mem (hkO i j))).neg
      rw [add_zero, zpow_natCast] at this
      convert this using 1
      ring
    have hc := eq_of_bdd_digitSum_sub (l i) hbdd
    refine ⟨?_, hc⟩
    have hdc : digitSum F (l i) (c ⟨(i, j), hij⟩) = digitSum F (l i) (c' ⟨(i, j), hij⟩) := by
      rw [hc]
    have h0 : ϖ ^ l i * k i j = 0 := by linear_combination -hsum - hdc
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ)
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  exact (key _ i j hij rfl).2

theorem diag_mul_torusPow' {u : GL (Fin n) F} (hu : u ∈ unipotent F n) (l : Fin n → ℤ) (i j : Fin n) :
    ((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = u i j * ϖ ^ l j := by
  rw [Units.val_mul, coe_torusPow, mul_diagonal]

theorem exists_reduce_row (l : Fin n → ℕ) {h : GL (Fin n) F} (hB : h ∈ Iwasawa.borel F n)
    (hd : ∀ a, h a a = ϖ ^ l a) (hO : ∀ a b, h a b ∈ 𝒪[F]) (i : Fin n) :
    ∃ k ∈ integralGL F n, h * k ∈ Iwasawa.borel F n ∧ (∀ a, (h * k) a a = ϖ ^ l a) ∧
      (∀ a b, (h * k) a b ∈ 𝒪[F]) ∧ (∀ a b, i < a → (h * k) a b = h a b) ∧
      ∀ j, i < j → ∃ e : Fin (l i) → 𝓀[F], (h * k) i j = digitSum F (l i) e := by
  classical
  have hBU : (h : Matrix (Fin n) (Fin n) F).IsUpperTriangular := (Iwasawa.mem_borel F n).1 hB
  have hy : ∀ j, ∃ e : Fin (l i) → 𝓀[F], ∃ y ∈ 𝒪[F], h i j - digitSum F (l i) e = ϖ ^ l i * y :=
    fun j => by
      obtain ⟨e, he⟩ := exists_digitSum (l i) (hO i j)
      obtain ⟨y, hy, hxy⟩ := exists_eq_uniformizer_pow_mul he
      exact ⟨e, y, hy, hxy⟩
  choose e y hyO hxy using hy
  set A : Matrix (Fin n) (Fin n) F := Matrix.of fun a b => if a = i ∧ i < b then -y b else 0
    with hA
  set E : Matrix (Fin n) (Fin n) F := 1 + A with hE
  have hEU : E.IsUpperTriangular := by
    intro a b hab
    have hab' : b < a := hab
    simp only [hE, hA, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_gt hab')]
    split_ifs with h1
    · exact absurd (h1.1 ▸ h1.2) (not_lt.2 hab'.le)
    · simp
  have hEd : ∀ a, E a a = 1 := fun a => by
    simp only [hE, hA, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    rw [if_neg (fun h => by obtain ⟨rfl, h2⟩ := h; exact lt_irrefl _ h2), add_zero]
  have hEO : ∀ a b, E a b ∈ 𝒪[F] := fun a b => by
    simp only [hE, hA, Matrix.add_apply, Matrix.of_apply]
    refine Subring.add_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact (𝒪[F]).one_mem
      · exact (𝒪[F]).zero_mem
    · split_ifs
      · exact Subring.neg_mem _ (hyO b)
      · exact (𝒪[F]).zero_mem
  have hdet : E.det = 1 := by
    rw [det_of_isUpperTriangular hEU]
    simp [hEd]
  set Eg : GL (Fin n) F :=
    ((Matrix.isUnit_iff_isUnit_det E).2 (by rw [hdet]; exact isUnit_one)).unit with hEgdef
  have hEg : (Eg : Matrix (Fin n) (Fin n) F) = E := IsUnit.unit_spec _
  have hEgN : Eg ∈ unipotent F n :=
    (mem_unipotent F n).2 ⟨by rw [hEg]; exact hEU, fun a => by
      rw [hEg]; exact hEd a⟩
  have hEgK : Eg ∈ integralGL F n :=
    ((mem_unipotent_inf_integralGL_iff F n).2 ⟨hEgN, fun a b => by
      rw [hEg]; exact hEO a b⟩).2
  have hmul : ∀ a b, (h * Eg : GL (Fin n) F) a b = h a b + if i < b then h a i * -y b else 0 := by
    intro a b
    rw [Units.val_mul, hEg, hE, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
    congr 1
    by_cases hib : i < b
    · rw [if_pos hib, Finset.sum_eq_single i]
      · simp [hA, hib]
      · intro m _ hm
        simp [hA, hm]
      · simp
    · rw [if_neg hib]
      exact Finset.sum_eq_zero fun m _ => by simp [hA, hib]
  refine ⟨Eg, hEgK, (Iwasawa.borel F n).mul_mem hB (unipotent_le_borel F n hEgN), fun a => ?_,
    fun a b => ?_, fun a b hia => ?_, fun j hij => ⟨e j, ?_⟩⟩
  · rw [mul_apply_self_of_mem_borel F n hB (unipotent_le_borel F n hEgN), hd, hEgN.2, mul_one]
  · rw [hmul]
    refine Subring.add_mem _ (hO a b) ?_
    split_ifs
    · exact Subring.mul_mem _ (hO a i) (Subring.neg_mem _ (hyO b))
    · exact (𝒪[F]).zero_mem
  · rw [hmul, hBU hia, zero_mul, ite_self, add_zero]
  · rw [hmul, if_pos hij, hd]
    linear_combination hxy j

theorem exists_normalGL {g : GL (Fin n) F} (hg : ∀ i j, g i j ∈ 𝒪[F]) :
    ∃ l : Fin n → ℕ, ∃ c : NormalData F l,
      (QuotientGroup.mk (normalGL F l c) : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk g := by
  classical
  obtain ⟨u, hu, k₀, hk₀, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  set L := iwasawaExponent F n g
  set h := u * torusPow F n L with hh
  have hhg : h = g * k₀⁻¹ := by rw [he, mul_inv_cancel_right]
  have hO : ∀ i j, h i j ∈ 𝒪[F] := fun i j => by
    rw [hhg]
    rw [Units.val_mul]
    exact mul_mem_of_forall_mem hg
      ((mem_integralGL_iff F n).1 ((integralGL F n).inv_mem hk₀)).1 i j
  have hdiag : ∀ i, h i i = ϖ ^ L i := fun i => by
    change ((u * torusPow F n L : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
    rw [diag_mul_torusPow' hu, hu.2 i, one_mul]
  have hL : ∀ i, 0 ≤ L i := fun i => by
    have := bdd_of_mem (hO i i)
    rw [hdiag] at this
    exact le_of_bdd_zpow this
  set l : Fin n → ℕ := fun i => (L i).toNat with hldef
  have hdl : ∀ i, h i i = ϖ ^ l i := fun i => by
    rw [hdiag, hldef, ← zpow_natCast, Int.toNat_of_nonneg (hL i)]
  have hB : h ∈ Iwasawa.borel F n :=
    (Iwasawa.borel F n).mul_mem (unipotent_le_borel F n hu) (torusPow_mem_borel F n L)
  have red : ∀ r : ℕ, ∃ k ∈ integralGL F n, h * k ∈ Iwasawa.borel F n ∧ (∀ a, (h * k) a a = ϖ ^ l a) ∧
      (∀ a b, (h * k) a b ∈ 𝒪[F]) ∧ ∀ i j : Fin n, i < j → n ≤ r + i →
        ∃ e : Fin (l i) → 𝓀[F], (h * k) i j = digitSum F (l i) e := by
    intro r
    induction r with
    | zero =>
      refine ⟨1, one_mem _, by simpa using hB, by simpa using hdl, by simpa using hO,
        fun i j _ hi => absurd hi ?_⟩
      have := i.2
      omega
    | succ r ih =>
      obtain ⟨k, hk, hB', hd', hO', hred⟩ := ih
      by_cases hr : r < n
      · set i₀ : Fin n := ⟨n - 1 - r, by omega⟩ with hi₀
        obtain ⟨k', hk', hB'', hd'', hO'', hrows, hrow⟩ := exists_reduce_row l hB' hd' hO' i₀
        refine ⟨k * k', mul_mem hk hk', by rwa [← mul_assoc], by rwa [← mul_assoc],
          by rwa [← mul_assoc], fun i j hij hi => ?_⟩
        rw [← mul_assoc]
        by_cases hii : i = i₀
        · subst hii
          exact hrow j hij
        · have hne : (i : ℕ) ≠ n - 1 - r := fun h' => hii (Fin.ext h')
          have hi' : i₀ < i := by
            rw [Fin.lt_def]
            show n - 1 - r < (i : ℕ)
            omega
          rw [hrows i j hi']
          exact hred i j hij (by omega)
      · exact ⟨k, hk, hB', hd', hO', fun i j hij hi => hred i j hij (by omega)⟩
  obtain ⟨k, hk, hB', hd', hO', hred⟩ := red n
  set c : NormalData F l := fun p => (hred p.1.1 p.1.2 p.2 (Nat.le_add_right _ _)).choose
    with hcdef
  have hc : ∀ p : UpperPairs n, (h * k) p.1.1 p.1.2 = digitSum F (l p.1.1) (c p) := fun p =>
    (hred p.1.1 p.1.2 p.2 (Nat.le_add_right _ _)).choose_spec
  have hBU : ((h * k : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsUpperTriangular :=
    (Iwasawa.mem_borel F n).1 hB'
  refine ⟨l, c, ?_⟩
  have heq : normalGL F l c = h * k := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [coe_normalGL]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [normalMat_of_lt l c hij]
      exact (hc ⟨(i, j), hij⟩).symm
    · rw [normalMat_self]
      exact (hd' i).symm
    · rw [normalMat_of_gt l c hij]
      exact (hBU hij).symm
  rw [heq, hhg, mul_assoc]
  exact QuotientGroup.mk_mul_of_mem g ((integralGL F n).mul_mem ((integralGL F n).inv_mem hk₀) hk)

theorem ordDet_normalGL (l : Fin n → ℕ) (c : NormalData F l) :
    GodementJacquet.ordDet (normalGL F l c) = ∑ i, (l i : ℤ) := by
  rw [GodementJacquet.ordDet, coe_normalGL, det_normalMat,
    GodementJacquet.ord_prod _ (fun i _ => pow_ne_zero _ (Cartan.uniformizer_ne_zero F))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← zpow_natCast, GodementJacquet.ord_zpow_uniformizer]

theorem normalGL_apply_mem (l : Fin n → ℕ) (c : NormalData F l) (i j : Fin n) :
    (normalGL F l c) i j ∈ 𝒪[F] := by
  rw [coe_normalGL]
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [normalMat_of_lt l c hij]
    exact digitSum_mem _ _
  · rw [normalMat_self]
    exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 _
  · rw [normalMat_of_gt l c hij]
    exact (𝒪[F]).zero_mem

variable (F n) in

def integralShell (k : ℕ) : Set (GL (Fin n) F) :=
  {g | (∀ i j, g i j ∈ 𝒪[F]) ∧ GodementJacquet.ordDet g = k}

theorem normalGL_mem_integralShell (l : Fin n → ℕ) (c : NormalData F l) :
    normalGL F l c ∈ integralShell F n (∑ i, l i) :=
  ⟨normalGL_apply_mem l c, by rw [ordDet_normalGL]; push_cast; rfl⟩

theorem mul_mem_integralShell {k : ℕ} {g a b : GL (Fin n) F} (hg : g ∈ integralShell F n k)
    (ha : a ∈ integralGL F n) (hb : b ∈ integralGL F n) : a * g * b ∈ integralShell F n k := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact mul_mem_of_forall_mem (mul_mem_of_forall_mem ((mem_integralGL_iff F n).1 ha).1 h1)
      ((mem_integralGL_iff F n).1 hb).1 i j
  · rw [GodementJacquet.ordDet_mul, GodementJacquet.ordDet_mul,
      GodementJacquet.ordDet_of_mem_integralGL ha, GodementJacquet.ordDet_of_mem_integralGL hb, h2]
    ring

theorem mul_mem_integralShell_iff {k : ℕ} {a g b : GL (Fin n) F} (ha : a ∈ integralGL F n)
    (hb : b ∈ integralGL F n) : a * g * b ∈ integralShell F n k ↔ g ∈ integralShell F n k := by
  refine ⟨fun h => ?_, fun h => mul_mem_integralShell h ha hb⟩
  have := mul_mem_integralShell h ((integralGL F n).inv_mem ha) ((integralGL F n).inv_mem hb)
  simpa [mul_assoc] using this

theorem exists_normalGL_of_mem {k : ℕ} {g : GL (Fin n) F} (hg : g ∈ integralShell F n k) :
    ∃ l ∈ Finset.Nat.antidiagonalTuple n k, ∃ c : NormalData F l,
      (QuotientGroup.mk (normalGL F l c) : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk g := by
  obtain ⟨l, c, hc⟩ := exists_normalGL hg.1
  have hk : (normalGL F l c)⁻¹ * g ∈ integralGL F n := QuotientGroup.eq.1 hc
  have h1 := GodementJacquet.ordDet_mul (normalGL F l c) ((normalGL F l c)⁻¹ * g)
  rw [mul_inv_cancel_left, GodementJacquet.ordDet_of_mem_integralGL hk, add_zero, hg.2,
    ordDet_normalGL] at h1
  refine ⟨l, Finset.Nat.mem_antidiagonalTuple.2 ?_, c, hc⟩
  exact_mod_cast h1.symm

theorem integralShell_eq (k : ℕ) :
    integralShell F n k = ⋃ (l : Finset.Nat.antidiagonalTuple n k) (c : NormalData F l.1),
      normalGL F l.1 c • (integralGL F n : Set (GL (Fin n) F)) := by
  ext g
  simp only [Set.mem_iUnion]
  constructor
  · intro hg
    obtain ⟨l, hl, c, hc⟩ := exists_normalGL_of_mem hg
    have hk : (normalGL F l c)⁻¹ * g ∈ integralGL F n := QuotientGroup.eq.1 hc
    exact ⟨⟨l, hl⟩, c, _, hk, by simp [smul_eq_mul]⟩
  · rintro ⟨⟨l, hl⟩, c, k', hk', rfl⟩
    have := mul_mem_integralShell (normalGL_mem_integralShell l c) (integralGL F n).one_mem hk'
    rw [one_mul, Finset.Nat.mem_antidiagonalTuple.1 hl] at this
    exact this

theorem isCompact_integralShell (k : ℕ) : IsCompact (integralShell F n k) := by
  rw [integralShell_eq]
  exact isCompact_iUnion fun l => isCompact_iUnion fun c => (isCompact_integralGL F n).smul _

theorem isOpen_integralShell (k : ℕ) : IsOpen (integralShell F n k) := by
  rw [integralShell_eq]
  exact isOpen_iUnion fun l => isOpen_iUnion fun c => (isOpen_integralGL F n).smul _

theorem natCard_normalData (l : Fin n → ℕ) :
    Nat.card (NormalData F l) = qF F ^ ∑ p : UpperPairs n, l p.1.1 := by
  rw [Nat.card_pi]
  simp only [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem sum_upperPairs (f : Fin n → ℤ) :
    ∑ p : UpperPairs n, f p.1.1 = ∑ i : Fin n, ((n : ℤ) - 1 - ((i : ℕ) : ℤ)) * f i := by
  classical
  have hs := Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (p := fun p : Fin n × Fin n => p.1 < p.2) (F := inferInstance) (fun x => by simp) (fun p => f p.1)
  rw [← hs, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
  have hi := i.2
  rw [Nat.sub_sub, Nat.cast_sub (by omega : 1 + (i : ℕ) ≤ n)]
  push_cast
  ring

theorem two_mul_sum_upperPairs_sub_rhoPair (l : Fin n → ℕ) :
    2 * (∑ p : UpperPairs n, (l p.1.1 : ℤ)) - rhoPair (fun i => (l i : ℤ)) =
      ((n : ℤ) - 1) * ∑ i, (l i : ℤ) := by
  rw [sum_upperPairs (fun i => (l i : ℤ)), rhoPair, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

variable (μ) in

def integralHecke (k : ℕ) : SphericalHecke μ (F := F) (n := n) :=
  indicatorHecke μ (integralShell F n k) (isCompact_integralShell k) (isOpen_integralShell k)
    fun a ha x => ⟨by simpa using mul_mem_integralShell_iff (g := x) (k := k) ha (integralGL F n).one_mem,
      by simpa using mul_mem_integralShell_iff (g := x) (k := k) (integralGL F n).one_mem ha⟩

theorem integralHecke_apply (k : ℕ) (g : GL (Fin n) F) :
    (integralHecke μ k : HeckeAlgebra μ) g = (integralShell F n k).indicator (fun _ => (1 : ℂ)) g :=
  rfl

theorem satake_integralHecke (k : ℕ) :
    satake μ (integralHecke μ k) = (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) •
      ∑ l ∈ Finset.Nat.antidiagonalTuple n k,
        ((Nat.card (NormalData F l) : ℂ) • monomial (fun i => (l i : ℤ))) := by
  classical
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.Nat.antidiagonalTuple n k).biUnion
    fun l => Finset.univ.image fun c : NormalData F l => (QuotientGroup.mk (normalGL F l c) : _)
  rw [satake_eq_sum _ Cs]
  · congr 1
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hlk := Finset.Nat.mem_antidiagonalTuple.1 hl
      rw [Finset.sum_image fun c _ c' _ h => normalGL_injective l h]
      have : ∀ c : NormalData F l, AddMonoidAlgebra.single (iwasawaExponent F n
          (QuotientGroup.mk (normalGL F l c) : GL (Fin n) F ⧸ integralGL F n).out)
          ((integralHecke μ k : HeckeAlgebra μ)
            (QuotientGroup.mk (normalGL F l c) : GL (Fin n) F ⧸ integralGL F n).out) =
          monomial (fun i => (l i : ℤ)) := by
        intro c
        have hmem := normalGL_mem_integralShell l c
        rw [hlk] at hmem
        rw [iwasawaExponent_out, iwasawaExponent_normalGL, apply_out, integralHecke_apply,
          Set.indicator_of_mem hmem]
      simp only [this, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      rw [Nat.cast_smul_eq_nsmul]
    · intro l _ l' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.1 hx'
      have := congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'
      simp only [iwasawaExponent_out, iwasawaExponent_normalGL] at this
      exact hne (funext fun i => by exact_mod_cast (congrFun this i).symm)
  · intro x hx
    rw [integralHecke_apply]
    refine Set.indicator_of_notMem (fun hm => hx ?_) _
    obtain ⟨l, hl, c, hc⟩ := exists_normalGL_of_mem hm
    rw [QuotientGroup.out_eq'] at hc
    exact Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩

theorem evalAt_satakeTransform_integralHecke (z : Fin n → ℂˣ) (k : ℕ) :
    evalAt z (satakeTransform μ (integralHecke μ k)) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (((n : ℤ) - 1) * k) *
        ∑ l ∈ Finset.Nat.antidiagonalTuple n k, ∏ i, (z i : ℂ) ^ l i := by
  rw [satakeTransform_apply, evalAt_normalize, satake_integralHecke, map_smul, map_sum,
    smul_eq_mul, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlk := Finset.Nat.mem_antidiagonalTuple.1 hl
  rw [map_smul, evalAt_single, one_mul, map_mul, monomialChar_halfPoint, natCard_normalData,
    halfModulus_eq, smul_eq_mul]
  have hz : monomialChar (fun i => (l i : ℤ)) z = ∏ i, (z i : ℂ) ^ l i := by
    rw [monomialChar_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, zpow_natCast]
  rw [hz]
  have hq : ((qF F ^ ∑ p : UpperPairs n, l p.1.1 : ℕ) : ℂ) =
      sqrtQ F ^ (2 * (∑ p : UpperPairs n, (l p.1.1 : ℤ))) := by
    push_cast
    rw [← sqrtQ_sq, ← pow_mul, ← zpow_natCast]
    push_cast
    rfl
  have hexp := two_mul_sum_upperPairs_sub_rhoPair l
  rw [hq, show sqrtQ F ^ (((n : ℤ) - 1) * k) = sqrtQ F ^ (2 * (∑ p : UpperPairs n, (l p.1.1 : ℤ))) *
      sqrtQ F ^ (-rhoPair (fun i => (l i : ℤ))) by
    rw [← zpow_add₀ (sqrtQ_ne_zero (F := F)), ← sub_eq_add_neg, hexp, ← hlk]
    push_cast
    rfl]
  ring

end Spherical

end GroundTheory.Automorphic
