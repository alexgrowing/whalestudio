import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.TensorValue

open Formalism.L2.LamCM

def detPol (n : ℕ) (K : Type) [CommRing K] : Pol n K := (Matrix.of fun a s : Fin n => (X (a, s) : Pol n K)).det

theorem evalAt_detPol {n : ℕ} {K : Type} [CommRing K] (w : Matrix (Fin n) (Fin n) K) :
    DualWeyl.evalAt w (detPol n K) = w.det := by
  unfold detPol
  rw [AlgHom.map_det]
  congr 1
  ext a s
  simp

theorem eval_eq_evalAt {n : ℕ} {K : Type} [CommRing K] (v : Fin n × Fin n → K) (p : Pol n K) :
    eval v p = DualWeyl.evalAt (Matrix.of fun a s => v (a, s)) p := by
  simp [DualWeyl.evalAt, coe_aeval_eq_eval]

theorem eq_zero_of_evalAt {n : ℕ} {K : Type} [Field K] [Infinite K] (p : Pol n K)
    (h : ∀ w : Matrix (Fin n) (Fin n) K, w.det ≠ 0 → DualWeyl.evalAt w p = 0) : p = 0 := by
  have hd : detPol n K ≠ 0 := fun h0 => by
    have h1 := evalAt_detPol (K := K) (1 : Matrix (Fin n) (Fin n) K)
    rw [h0, map_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  have h1 : p * detPol n K = 0 := MvPolynomial.funext fun v => by
    rw [map_zero, eval_eq_evalAt, map_mul, evalAt_detPol]
    by_cases hw : (Matrix.of fun a s => v (a, s)).det = 0
    · rw [hw, mul_zero]
    · rw [h _ hw, zero_mul]
  exact (mul_eq_zero.mp h1).resolve_right hd

def blockDet (K : Type) [CommRing K] {T : Type} (N : T → ℕ) (t : T) : MvPolynomial (FrVar N) K :=
  (Matrix.of fun i k : Fin (N t) => (X ⟨t, (k, i)⟩ : MvPolynomial (FrVar N) K)).det

theorem evalFr_blockDet {K T : Type} [CommRing K] {N : T → ℕ} (t : T) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    evalFr (blockDet K N t) y = (y t).det := by
  unfold evalFr blockDet
  rw [RingHom.map_det]
  congr 1
  ext i k
  simp

theorem eq_zero_of_evalFr {T : Type} [Fintype T] {N : T → ℕ} {K : Type} [Field K] [Infinite K]
    (P : MvPolynomial (FrVar N) K)
    (h : ∀ y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → evalFr P y = 0) : P = 0 := by
  have hev : ∀ (Q : MvPolynomial (FrVar N) K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K),
      evalFr (Q * ∏ t, blockDet K N t) y = evalFr Q y * ∏ t, (y t).det := fun Q y => by
    simp only [← evalFr_blockDet (K := K) (N := N) _ y]
    simp only [evalFr, map_mul, map_prod]
  have hd : (∏ t, blockDet K N t) ≠ 0 := fun h0 => by
    have h1 := hev 1 (fun _ => 1)
    rw [h0, mul_zero] at h1
    simp [evalFr] at h1
  have h1 : P * ∏ t, blockDet K N t = 0 := MvPolynomial.funext fun v => by
    let y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K := fun t => Matrix.of fun i j => v ⟨t, (j, i)⟩
    have hy : ∀ Q : MvPolynomial (FrVar N) K, eval v Q = evalFr Q y := fun Q => rfl
    rw [map_zero, hy, hev]
    by_cases hw : ∀ t, (y t).det ≠ 0
    · rw [h y hw, zero_mul]
    · push_neg at hw
      obtain ⟨t, ht⟩ := hw
      rw [Finset.prod_eq_zero (Finset.mem_univ t) ht, mul_zero]
  exact (mul_eq_zero.mp h1).resolve_right hd

theorem exists_points {ι Z K : Type} [Fintype ι] [DecidableEq ι] [Field K] (Φ : ι → Z → K)
    (h : ∀ c : ι → K, (∀ z, ∑ i, c i * Φ i z = 0) → c = 0) :
    ∃ p : ι → Z, IsUnit (Matrix.of fun i k => Φ i (p k)) := by
  let v : Z → ι → K := fun z i => Φ i z
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    apply hf0
    have hc := h (fun i => f fun j => if i = j then 1 else 0) fun z => by
      have h1 : f (v z) = 0 := by
        have : f (v z) ∈ (Submodule.span K (Set.range v)).map f :=
          ⟨v z, Submodule.subset_span ⟨z, rfl⟩, rfl⟩
        rw [hf] at this
        exact (Submodule.mem_bot K).mp this
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [v, smul_eq_mul, mul_comm] using h1
    refine LinearMap.ext fun u => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f u]
    simp [fun i => congrFun hc i]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  rw [hspan] at hsp
  haveI : Finite κ := hli.finite
  haveI := Fintype.ofFinite κ
  let bas := Basis.mk hli hsp.ge
  have hcard : Fintype.card κ = Fintype.card ι := by
    have := Module.finrank_eq_card_basis bas
    simpa using this.symm
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ e, ?_⟩
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact hli.comp e e.injective

end GlobalTheory.TensorValue

namespace GlobalTheory.TensorValue

open Formalism.L2.LamCM

def bval {n : ℕ} (la : Fin n → ℕ) {S : Type} [CommRing S] (i : Idx la) (w : Matrix (Fin n) (Fin n) S) : S :=
  DualWeyl.evalAt w (map (Int.castRingHom S) (intVec la i))

theorem tval_eq {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ) {S : Type} [CommRing S]
    (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) :
    tval la x y = ∑ I : TIdx la, x I * ∏ t, bval (la t) (I t) (y t) := rfl

theorem exists_good_points {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] :
    ∃ z : Idx la → Matrix (Fin n) (Fin n) K, (∀ k, (z k).det ≠ 0) ∧
      IsUnit (Matrix.of fun i k => bval la i (z k)) := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨p, hp⟩ := exists_points (Z := {w : Matrix (Fin n) (Fin n) K // w.det ≠ 0})
    (fun i w => bval la i w.1) fun c hc => by
      have hq : ∑ i, c i • map (Int.castRingHom K) (intVec la i) = 0 := by
        refine eq_zero_of_evalAt _ fun w hw => ?_
        simpa [map_sum, bval] using hc ⟨w, hw⟩
      funext i
      exact Fintype.linearIndependent_iff.mp (intVec_spec la K).1 c hq i
  exact ⟨fun k => (p k).1, fun k => (p k).2, hp⟩

theorem map_evalFr {R S T : Type} [CommRing R] [CommRing S] {N : T → ℕ} (ψ : R →+* S)
    (P : MvPolynomial (FrVar N) R) (Y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) R) :
    ψ (evalFr P Y) = evalFr (map ψ P) (fun t => (Y t).map ψ) := by
  unfold evalFr
  rw [eval_map]
  show ψ (eval₂ (RingHom.id R) _ P) = _
  rw [eval₂_comp_left]
  rfl

section Slice

variable {T : Type} [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (K : Type) [Field K]
  [CharZero K]

theorem exists_slice (G : MvPolynomial (FrVar N) K)
    (hG : ∀ y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) →
      (∀ t, (b t).BlockTriangular id ∧ ∀ i, b t i i ≠ 0) →
      evalFr G (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * evalFr G y)
    (a : T) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (hy : ∀ t, (y t).det ≠ 0) :
    ∃ c : Idx (la a) → K, ∀ w, evalFr G (Function.update y a w) = ∑ i, c i * bval (la a) i w := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  let Y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) (Pol (N a) K) :=
    Function.update (fun t => (y t).map C) a (Matrix.of fun i j => X (i, j))
  let p : Pol (N a) K := evalFr (map C G) Y
  have hp : ∀ w, DualWeyl.evalAt w p = evalFr G (Function.update y a w) := by
    intro w
    have h1 := map_evalFr (DualWeyl.evalAt w).toRingHom (map C G) Y
    rw [map_map] at h1
    have h2 : (DualWeyl.evalAt w).toRingHom.comp C = RingHom.id K := by
      ext k
      simp [DualWeyl.evalAt]
    rw [h2, map_id] at h1
    have h3 : (fun t => (Y t).map (DualWeyl.evalAt w).toRingHom) = Function.update y a w := by
      funext t
      rcases eq_or_ne t a with rfl | ht
      · ext i j
        simp [Y]
      · ext i j
        simp [Y, Function.update_of_ne ht, DualWeyl.evalAt]
    rw [h3] at h1
    exact h1
  let one : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K := fun t => 1
  have hmem : p ∈ nabla (la a) K := by
    rw [mem_nabla_iff]
    intro b hb hdiag
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt _ fun w hw => ?_
    rw [map_sub, evalAt_colAct, map_smul, hp, hp, smul_eq_mul]
    have h1 := hG (Function.update y a w) (Function.update one a b)
      (fun t => by
        rcases eq_or_ne t a with rfl | ht
        · simpa using hw
        · simpa [Function.update_of_ne ht] using hy t)
      (fun t => by
        rcases eq_or_ne t a with rfl | ht
        · simpa using ⟨hb, hdiag⟩
        · simp only [Function.update_of_ne ht, one]
          exact ⟨Matrix.blockTriangular_one, fun i => by simp⟩)
    have h2 : (fun t => Function.update y a w t * Function.update one a b t) =
        Function.update y a (w * b) := by
      funext t
      rcases eq_or_ne t a with rfl | ht
      · simp
      · simp [Function.update_of_ne ht, one]
    have h3 : (∏ t, diagChar (la t) (Function.update one a b t)) =
        diagChar (la a) b := by
      rw [Finset.prod_eq_single a]
      · simp
      · intro t _ ht
        simp [Function.update_of_ne ht, diagChar, one]
      · simp
    rw [h2, h3] at h1
    rw [h1, sub_self]
  have h1 := congrArg Subtype.val ((basis (la a) K).sum_repr ⟨p, hmem⟩)
  obtain ⟨c, hc⟩ : ∃ c : Idx (la a) → K, p = ∑ i, c i • map (Int.castRingHom K) (intVec (la a) i) :=
    by
      rw [Submodule.coe_sum] at h1
      simp only [Submodule.coe_smul, coe_basis] at h1
      exact ⟨_, h1.symm⟩
  refine ⟨c, fun w => ?_⟩
  rw [← hp, hc]
  simp [map_sum, bval]

end Slice

def tpoly {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ) {K : Type} [CommRing K]
    (x : TIdx la → K) : MvPolynomial (FrVar N) K :=
  ∑ I : TIdx la, C (x I) * ∏ t, rename (fun v : Fin (N t) × Fin (N t) => (⟨t, (v.2, v.1)⟩ : FrVar N))
    (map (Int.castRingHom K) (intVec (la t) (I t)))

theorem evalFr_map_tpoly {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ)
    {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) (x : TIdx la → K) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) :
    evalFr (map φ (tpoly la x)) y = tval la (fun I => φ (x I)) y := by
  rw [tval_eq]
  simp only [tpoly, evalFr, map_sum, map_mul, map_prod, map_C, eval_C, map_rename, eval_rename, map_map]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [show φ.comp (Int.castRingHom K) = Int.castRingHom S from RingHom.ext_int _ _]
  simp [bval, DualWeyl.evalAt, coe_aeval_eq_eval, Function.comp_def]

theorem transfer {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K]
    [CharZero K] (G : MvPolynomial (FrVar N) K) (x : TIdx la → K)
    (h : ∀ y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → evalFr G y = tval la x y)
    (S : Type) [CommRing S] (φ : K →+* S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) :
    evalFr (map φ G) y = tval la (fun I => φ (x I)) y := by
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  have hG : G = tpoly la x := by
    rw [← sub_eq_zero]
    refine eq_zero_of_evalFr _ fun y hy => ?_
    have h1 := evalFr_map_tpoly la (RingHom.id K) x y
    rw [map_id] at h1
    have h2 : evalFr (G - tpoly la x) y = evalFr G y - evalFr (tpoly la x) y := by
      simp [evalFr]
    rw [h2, h1, h y hy]
    simp
  rw [hG]
  exact evalFr_map_tpoly la φ x y

theorem interpolation_inverse_matrix_sum_identity {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] (A : Matrix ι ι K) (hA : IsUnit A)
    (c F : ι → K) : ∑ k, (∑ i, c i * A i k) * ∑ j, A⁻¹ k j * F j = ∑ i, c i * F i := by
  change (c ᵥ* A) ⬝ᵥ (A⁻¹ *ᵥ F) = c ⬝ᵥ F
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.vecMul_one]

end GlobalTheory.TensorValue

namespace GlobalTheory.TensorValue

open Formalism.L2.LamCM

theorem exists_tval_of_triangular : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ)
    (K : Type) [Field K] [CharZero K] (G : MvPolynomial (Formalism.L2.LamCM.FrVar N) K),
    (∀ y b : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) →
      (∀ t, (b t).BlockTriangular id ∧ ∀ i, b t i i ≠ 0) →
      Formalism.L2.LamCM.evalFr G (fun t => y t * b t) = (∏ t, diagChar (la t) (b t)) * Formalism.L2.LamCM.evalFr G y) →
    ∃ x : TIdx la → K, ∀ (S : Type) [CommRing S] (φ : K →+* S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S),
      Formalism.L2.LamCM.evalFr (MvPolynomial.map φ G) y = tval la (fun I => φ (x I)) y := by
  intro T _ _ N la K _ _ G hG
  choose z hz hA using fun t => exists_good_points (la t) K
  let A : ∀ t, Matrix (Idx (la t)) (Idx (la t)) K := fun t => Matrix.of fun i k => bval (la t) i (z t k)
  let L : ∀ t, Idx (la t) → Matrix (Fin (N t)) (Fin (N t)) K → K :=
    fun t k w => ∑ i, (A t)⁻¹ k i * bval (la t) i w
  let zK : TIdx la → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K := fun J t => z t (J t)
  let Q : (∀ t, Matrix (Fin (N t)) (Fin (N t)) K) → K :=
    fun y => ∑ J : TIdx la, evalFr G (zK J) * ∏ t, L t (J t) (y t)
  let x : TIdx la → K := fun I => ∑ J : TIdx la, evalFr G (zK J) * ∏ t, (A t)⁻¹ (J t) (I t)
  let V : ∀ t, Submodule K (Matrix (Fin (N t)) (Fin (N t)) K → K) :=
    fun t => Submodule.span K (Set.range fun i => bval (la t) i)
  have hxQ : ∀ y, tval la x y = Q y := fun y => by
    rw [tval_eq]
    calc ∑ I : TIdx la, x I * ∏ t, bval (la t) (I t) (y t)
        = ∑ I : TIdx la, ∑ J : TIdx la, evalFr G (zK J) * ∏ t, ((A t)⁻¹ (J t) (I t) * bval (la t) (I t) (y t)) := by
          refine Finset.sum_congr rfl fun I _ => ?_
          simp only [x, Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]
      _ = ∑ J : TIdx la, evalFr G (zK J) * ∑ I : TIdx la,
            ∏ t, ((A t)⁻¹ (J t) (I t) * bval (la t) (I t) (y t)) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = Q y := by
          simp only [Q, L, Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hLz : ∀ t k k', L t k (z t k') = if k = k' then 1 else 0 := fun t k k' => by
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul (A t) ((Matrix.isUnit_iff_isUnit_det _).mp (hA t))) k) k'
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    exact h1
  have hQz : ∀ J, Q (zK J) = evalFr G (zK J) := fun J => by
    simp only [Q, zK, hLz]
    rw [Finset.sum_eq_single J]
    · simp
    · intro J' _ hne
      obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
      rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht]), mul_zero]
    · simp
  have hinterp : ∀ t, ∀ h ∈ V t, ∀ w, h w = ∑ k, h (z t k) * L t k w := fun t h hh w => by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hh
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, L]
    exact (interpolation_inverse_matrix_sum_identity (A t) (hA t) c fun i => bval (la t) i w).symm
  have hbV : ∀ t (c : Idx (la t) → K), (fun w => ∑ i, c i * bval (la t) i w) ∈ V t := fun t c => by
    have : (fun w => ∑ i, c i * bval (la t) i w) = ∑ i, c i • bval (la t) i := by
      funext w
      simp [Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have key : ∀ s : Finset T, ∀ y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) →
      (∀ t ∉ s, ∃ k, y t = z t k) → evalFr G y = Q y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y _ hy
      choose J hJ using fun t => hy t (Finset.notMem_empty t)
      have : y = zK J := funext hJ
      rw [this, hQz]
    | insert a s ha ih =>
      intro y hy hzs
      have hD : (fun w => evalFr G (Function.update y a w) - Q (Function.update y a w)) ∈ V a := by
        refine sub_mem ?_ ?_
        · obtain ⟨c, hc⟩ := exists_slice N la K G hG a y hy
          have : (fun w => evalFr G (Function.update y a w)) = fun w => ∑ i, c i * bval (la a) i w :=
            funext hc
          rw [this]
          exact hbV a c
        · have : (fun w => Q (Function.update y a w)) = ∑ J : TIdx la,
              (evalFr G (zK J) * ∏ t ∈ Finset.univ.erase a, L t (J t) (y t)) • L a (J a) := by
            funext w
            simp only [Q, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            refine Finset.sum_congr rfl fun J _ => ?_
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), Function.update_self,
              Finset.prod_congr rfl fun t ht => by rw [Function.update_of_ne (Finset.ne_of_mem_erase ht)]]
            ring
          rw [this]
          refine Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ?_
          exact hbV a _
      have h0 : ∀ k, evalFr G (Function.update y a (z a k)) - Q (Function.update y a (z a k)) = 0 := by
        intro k
        rw [sub_eq_zero]
        refine ih _ (fun t => ?_) (fun t ht => ?_)
        · rcases eq_or_ne t a with rfl | h
          · simpa using hz t k
          · simpa [Function.update_of_ne h] using hy t
        · rcases eq_or_ne t a with rfl | h
          · exact ⟨k, by simp⟩
          · rw [Function.update_of_ne h]
            exact hzs t (by simp [h, ht])
      have h1 := hinterp a _ hD (y a)
      simp only [h0, zero_mul, Finset.sum_const_zero, Function.update_eq_self] at h1
      exact sub_eq_zero.mp h1
  refine ⟨x, transfer la G x fun y hy => ?_⟩
  rw [hxQ]
  exact key Finset.univ y hy fun t ht => absurd (Finset.mem_univ t) ht

end GlobalTheory.TensorValue

end
