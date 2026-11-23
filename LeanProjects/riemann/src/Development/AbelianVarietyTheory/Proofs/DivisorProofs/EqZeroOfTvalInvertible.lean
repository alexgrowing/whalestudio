import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.CoordVanish

theorem coeff_eq_zero_of_evalAt {n : ℕ} (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] (c : Idx la → K)
    (h : ∀ y : Matrix (Fin n) (Fin n) K, y.det ≠ 0 →
      ∑ i, c i * DualWeyl.evalAt y (map (Int.castRingHom K) (intVec la i)) = 0) : c = 0 := by
  classical
  set Q : Pol n K := ∑ i, c i • map (Int.castRingHom K) (intVec la i) with hQ
  have hQe : ∀ y : Matrix (Fin n) (Fin n) K,
      DualWeyl.evalAt y Q = ∑ i, c i * DualWeyl.evalAt y (map (Int.castRingHom K) (intVec la i)) := by
    intro y
    simp [hQ, map_sum, smul_eq_mul]
  set D : Pol n K := (Matrix.of fun a b : Fin n => (X (a, b) : Pol n K)).det with hD
  have hDe : ∀ y : Matrix (Fin n) (Fin n) K, DualWeyl.evalAt y D = y.det := by
    intro y
    rw [hD, AlgHom.map_det]
    congr 1
    ext a b
    simp
  have hev : ∀ (v : Fin n × Fin n → K) (p : Pol n K),
      eval v p = DualWeyl.evalAt (Matrix.of fun a b => v (a, b)) p := by
    intro v p
    simp [DualWeyl.evalAt, aeval_eq_eval]
  have hQD : Q * D = 0 := by
    refine MvPolynomial.funext fun v => ?_
    rw [hev, map_mul, hDe, map_zero]
    by_cases hd : (Matrix.of fun a b => v (a, b)).det = 0
    · rw [hd, mul_zero]
    · rw [hQe, h _ hd, zero_mul]
  have hD0 : D ≠ 0 := by
    intro h0
    have := hDe 1
    rw [h0, map_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hQ0 : Q = 0 := (mul_eq_zero.mp hQD).resolve_right hD0
  funext i
  exact Fintype.linearIndependent_iff.mp (intVec_spec la K).1 c hQ0 i

theorem eq_zero_of_prod {T : Type} [Fintype T] [DecidableEq T] {ι : T → Type} [∀ t, Fintype (ι t)]
    {A : T → Type} {K : Type} [Field K] (g : ∀ t, ι t → A t → K) (a0 : ∀ t, A t)
    (H : ∀ t (c : ι t → K), (∀ b : A t, ∑ i, c i * g t i b = 0) → c = 0)
    (x : (∀ t, ι t) → K) (hx : ∀ a : ∀ t, A t, ∑ I, x I * ∏ t, g t (I t) (a t) = 0) : x = 0 := by
  classical
  have key : ∀ S : Finset T, ∀ x : (∀ t, ι t) → K,
      (∀ a : ∀ t, A t, ∑ I, x I * ∏ t ∈ S, g t (I t) (a t) = 0) →
      ∀ I : ∀ t, ι t, ∑ I' ∈ Finset.univ.filter (fun I' : ∀ t, ι t => ∀ t ∈ S, I' t = I t), x I' = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x hx I
      simpa using hx a0
    | insert s S hs IH =>
      intro x hx I
      have step : ∀ i : ι s, ∀ a : ∀ t, A t,
          ∑ I', (if I' s = i then x I' else 0) * ∏ t ∈ S, g t (I' t) (a t) = 0 := by
        intro i a
        have hc := H s (fun i => ∑ I', (if I' s = i then x I' else 0) * ∏ t ∈ S, g t (I' t) (a t)) (fun b => by
          have h1 := hx (Function.update a s b)
          have h2 : ∀ I' : ∀ t, ι t, ∏ t ∈ S, g t (I' t) (Function.update a s b t) = ∏ t ∈ S, g t (I' t) (a t) := by
            intro I'
            refine Finset.prod_congr rfl fun t ht => ?_
            have : t ≠ s := fun h => hs (h ▸ ht)
            rw [Function.update_of_ne this]
          simp only [Finset.prod_insert hs, Function.update_self, h2] at h1
          refine Eq.trans ?_ h1
          simp only [Finset.sum_mul, ite_mul, zero_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I' _ => ?_
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_univ, if_true]
          ring)
        exact congrFun hc i
      have h3 := IH _ (step (I s)) I
      rw [Finset.sum_filter] at h3
      rw [Finset.sum_filter]
      refine Eq.trans (Finset.sum_congr rfl fun I' _ => ?_) h3
      simp only [Finset.forall_mem_insert]
      by_cases h4 : I' s = I s <;> by_cases h5 : ∀ t ∈ S, I' t = I t <;> simp [h4, h5]
  funext I
  have h := key Finset.univ x (by simpa using hx) I
  have h6 : Finset.univ.filter (fun I' : ∀ t, ι t => ∀ t ∈ (Finset.univ : Finset T), I' t = I t) = {I} := by
    ext I'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, forall_const]
    exact ⟨fun h => funext h, fun h t => h ▸ rfl⟩
  rw [h6, Finset.sum_singleton] at h
  exact h

theorem eq_zero_of_tval_invertible : ∀ (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ)
    (K : Type) [Field K] [CharZero K] (x : TIdx la → K),
    (∀ y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K, (∀ t, (y t).det ≠ 0) → tval la x y = 0) → x = 0 := by
  intro T _ _ N la K _ _ x hx
  exact eq_zero_of_prod (ι := fun t => Idx (la t))
    (A := fun t => {M : Matrix (Fin (N t)) (Fin (N t)) K // M.det ≠ 0})
    (fun t i M => DualWeyl.evalAt M.1 (map (Int.castRingHom K) (intVec (la t) i))) (fun t => ⟨1, by simp⟩)
    (fun t c hc => coeff_eq_zero_of_evalAt (la t) K c fun y hy => hc ⟨y, hy⟩) x
    (fun a => hx (fun t => (a t).1) fun t => (a t).2)

end GlobalTheory.CoordVanish
