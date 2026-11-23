import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedDerivativeFamiliesModerateGrowthStatement

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.SmoothFrechet

variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ρ : Mx n → (E →L[ℂ] E)}

theorem continuous_eval (l : List (lie (Jm ε))) : Continuous fun v : Fam ε ρ => v.1 l :=
  (continuous_apply l).comp continuous_subtype_val

def der (ρ : Mx n → (E →L[ℂ] E)) (X : lie (Jm ε)) : Fam ε ρ →L[ℂ] Fam ε ρ where
  toFun v := ⟨fun l => v.1 (l ++ [X]), fun l Y => v.2.1 (l ++ [X]) Y,
    fun l₁ l₂ a Y Z => by simpa only [List.append_assoc, List.cons_append] using v.2.2.1 l₁ (l₂ ++ [X]) a Y Z,
    fun l₁ l₂ Y Z T h => by simpa only [List.append_assoc, List.cons_append] using v.2.2.2 l₁ (l₂ ++ [X]) Y Z T h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := Continuous.subtype_mk (continuous_pi fun _ => continuous_eval _) _

theorem der_apply (X : lie (Jm ε)) (v : Fam ε ρ) (l : List (lie (Jm ε))) : (der ρ X v).1 l = v.1 (l ++ [X]) := rfl

theorem rho_mul (h : ModRep ε ρ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (w : E) :
    ρ (a * b) w = ρ a (ρ b w) := by rw [h.2.1 a ha b hb]; rfl

theorem adInv_lin {g : Mx n} (hg : g ∈ UJset ε) (a : ℝ) (X Y : lie (Jm ε)) :
    adInv hg (a • X + Y) = a • adInv hg X + adInv hg Y :=
  Subtype.ext <| by simp [adInv, mul_add, add_mul]

theorem adInv_br {g : Mx n} (hg : g ∈ UJset ε) {X Y Z : lie (Jm ε)} (h : (Z : Mx n) = X * Y - Y * X) :
    (adInv hg Z : Mx n) = adInv hg X * adInv hg Y - adInv hg Y * adInv hg X := by
  have e : ∀ A : Mx n, g * (g⁻¹ * A) = A := fun A => by rw [← mul_assoc, mul_inv_UJ hg, one_mul]
  simp only [adInv, h, mul_sub, sub_mul, mul_assoc, e]

def act (h : ModRep ε ρ) {g : Mx n} (hg : g ∈ UJset ε) : Fam ε ρ →L[ℂ] Fam ε ρ where
  toFun v := ⟨fun l => ρ g (v.1 (l.map (adInv hg))), fun l X => by
      have h1 := ((ρ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (v.2.1 (l.map (adInv hg)) (adInv hg X))
      refine HasDerivAt.congr_of_eventuallyEq h1 (Eventually.of_forall fun t => ?_)
      show ρ _ (ρ g _) = ρ g (ρ _ _)
      rw [← rho_mul h (exp_mem_UJ X.2 t) hg, ← rho_mul h hg (exp_mem_UJ (adInv hg X).2 t),
        exp_mul_eq (isUnit_of_UJ hg)]
      rfl,
    fun l₁ l₂ a Y Z => by
      simp only [List.map_append, List.map_cons, adInv_lin, v.2.2.1, map_add, map_smul],
    fun l₁ l₂ Y Z T hT => by
      simp only [List.map_append, List.map_cons, ← map_sub, v.2.2.2 _ _ _ _ _ (adInv_br hg hT)]⟩
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add (ρ g) _ _
  map_smul' _ _ := Subtype.ext <| funext fun _ => map_smul (ρ g) _ _
  cont := Continuous.subtype_mk (continuous_pi fun _ => (ρ g).continuous.comp (continuous_eval _)) _

theorem act_apply (h : ModRep ε ρ) {g : Mx n} (hg : g ∈ UJset ε) (v : Fam ε ρ) (l : List (lie (Jm ε))) :
    (act h hg v).1 l = ρ g (v.1 (l.map (adInv hg))) := rfl

theorem act_one (h : ModRep ε ρ) {g : Mx n} (hg : g ∈ UJset ε) (e : g = 1) (v : Fam ε ρ) : act h hg v = v := by
  subst e
  refine Subtype.ext <| funext fun l => ?_
  have : adInv hg = id := funext fun X => Subtype.ext <| by simp [adInv]
  rw [act_apply, this, h.1, List.map_id]; rfl

theorem act_mul (h : ModRep ε ρ) {a b c : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hc : c ∈ UJset ε)
    (e : c = a * b) (v : Fam ε ρ) : act h hc v = act h ha (act h hb v) := by
  subst e
  refine Subtype.ext <| funext fun l => ?_
  have : adInv hc = adInv hb ∘ adInv ha := funext fun X => Subtype.ext <| by
    simp [adInv, Matrix.mul_inv_rev, mul_assoc]
  rw [act_apply, act_apply, act_apply, this, rho_mul h ha hb, List.map_map]

theorem der_act (h : ModRep ε ρ) {g : Mx n} (hg : g ∈ UJset ε) (X : lie (Jm ε)) (v : Fam ε ρ) :
    der ρ X (act h hg v) = act h hg (der ρ (adInv hg X) v) :=
  Subtype.ext <| funext fun l => by simp only [der_apply, act_apply, List.map_append, List.map_cons, List.map_nil]

theorem der_lin (a : ℝ) (X Y : lie (Jm ε)) (v : Fam ε ρ) : der ρ (a • X + Y) v = (a : ℂ) • der ρ X v + der ρ Y v :=
  Subtype.ext <| funext fun l => v.2.2.1 l [] a X Y

theorem der_sum {ι : Type} (s : Finset ι) (c : ι → ℝ) (b : ι → lie (Jm ε)) (v : Fam ε ρ) :
    der ρ (∑ j ∈ s, c j • b j) v = ∑ j ∈ s, (c j : ℂ) • der ρ (b j) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using der_lin 1 0 0 v
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, der_lin, ih]

theorem exists_frame (ε : Fin n → Bool) : ∃ (d : ℕ) (b : Fin d → lie (Jm ε)) (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)),
    ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X := by
  let b := Module.finBasis ℝ (lie (Jm ε))
  choose φ hφ using fun j => LinearMap.exists_extend (b.coord j)
  refine ⟨_, b, φ, fun X => ?_⟩
  conv_rhs => rw [← b.sum_repr X]
  exact Finset.sum_congr rfl fun j _ => by rw [show φ j X = _ from LinearMap.congr_fun (hφ j) X]; rfl

def ev (ρ : Mx n → (E →L[ℂ] E)) (l : List (lie (Jm ε))) : Fam ε ρ →ₗ[ℂ] E :=
  (LinearMap.proj l).comp (Fam ε ρ).subtype

variable {d : ℕ}

def sn (ρ : Mx n → (E →L[ℂ] E)) (b : Fin d → lie (Jm ε)) (k : ℕ) : Seminorm ℂ (Fam ε ρ) :=
  Nat.rec ((normSeminorm ℂ E).comp (ev ρ []))
    (fun _ q => ∑ j, q.comp (der ρ (b j) : Fam ε ρ →ₗ[ℂ] Fam ε ρ)) k

theorem sn_zero (b : Fin d → lie (Jm ε)) (v : Fam ε ρ) : sn ρ b 0 v = ‖v.1 []‖ := rfl

theorem sn_succ (b : Fin d → lie (Jm ε)) (k : ℕ) (v : Fam ε ρ) :
    sn ρ b (k + 1) v = ∑ j, sn ρ b k (der ρ (b j) v) := by
  show (∑ j, (sn ρ b k).comp (der ρ (b j) : Fam ε ρ →ₗ[ℂ] Fam ε ρ)) v = _
  simp

theorem continuous_sn (b : Fin d → lie (Jm ε)) (k : ℕ) : Continuous (sn ρ b k) := by
  induction k with
  | zero => exact (continuous_eval []).norm
  | succ k ih =>
    rw [show ⇑(sn ρ b (k + 1)) = _ from funext (sn_succ b k)]
    exact continuous_finset_sum _ fun j _ => ih.comp (der ρ (b j)).continuous

def sz (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)) (X : Mx n) : ℝ := ∑ j, |φ j X|

theorem sz_nonneg (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)) (X : Mx n) : 0 ≤ sz φ X := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem continuous_sz (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)) : Continuous (sz φ) :=
  continuous_finset_sum _ fun j _ => (φ j).continuous_of_finiteDimensional.abs

theorem exists_sz_le (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)) : ∃ C, 0 ≤ C ∧ ∀ X, sz φ X ≤ C * (1 + hs X) := by
  letI : NormedAddCommGroup (Mx n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mx n) := Matrix.normedSpace
  have h1 : ∀ X : Mx n, ‖X‖ ≤ 1 + hs X := fun X =>
    (Matrix.norm_le_iff (by linarith [hs_nonneg X])).2 fun i j => by
      have : ‖X i j‖ ^ 2 ≤ hs X :=
        (Finset.single_le_sum (f := fun j => ‖X i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
      nlinarith [sq_nonneg (‖X i j‖ - 1), norm_nonneg (X i j)]
  have h2 : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] ℝ),
      ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C * ‖x‖ := fun V _ _ _ f =>
    ⟨‖LinearMap.toContinuousLinearMap f‖, norm_nonneg _, (LinearMap.toContinuousLinearMap f).le_opNorm⟩
  choose C hC h using fun j => h2 (Mx n) (φ j)
  refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ => hC j, fun X => ?_⟩
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ => (h j X).trans (mul_le_mul_of_nonneg_left (h1 X) (hC j))

variable {b : Fin d → lie (Jm ε)} {φ : Fin d → (Mx n →ₗ[ℝ] ℝ)}

theorem der_eq (hb : ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X) (X : lie (Jm ε)) (v : Fam ε ρ) :
    der ρ X v = ∑ j, (φ j X : ℂ) • der ρ (b j) v := by rw [← der_sum, hb]

theorem sn_der_le (hb : ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X) (k : ℕ) (X : lie (Jm ε)) (v : Fam ε ρ) :
    sn ρ b k (der ρ X v) ≤ sz φ X * sn ρ b (k + 1) v := by
  rw [der_eq hb, sz, Finset.sum_mul]
  refine (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)
  rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, sn_succ]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun j => sn ρ b k (der ρ (b j) v))
    (fun _ _ => apply_nonneg _ _) (Finset.mem_univ j)) (abs_nonneg _)

theorem norm_le_sn (hb : ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X) (l : List (lie (Jm ε))) :
    ∃ C, 0 ≤ C ∧ ∀ v : Fam ε ρ, ‖v.1 l‖ ≤ C * sn ρ b l.length v := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨1, zero_le_one, fun v => by rw [one_mul]; rfl⟩
  | append_singleton l X ih =>
    obtain ⟨C, hC, h⟩ := ih
    refine ⟨C * sz φ X, mul_nonneg hC (sz_nonneg _ _), fun v => (h (der ρ X v)).trans ?_⟩
    rw [mul_assoc, List.length_append]
    exact mul_le_mul_of_nonneg_left (sn_der_le hb _ X v) hC

theorem withSeminorms_sn (hb : ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X) : WithSeminorms (sn ρ b) := by
  have h1 : WithSeminorms fun l : List (lie (Jm ε)) => (normSeminorm ℂ E).comp (ev ρ l) := by
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, nhds_subtype, nhds_pi, Filter.pi, comap_iInf]
    refine iInf_congr fun l => ?_
    rw [comap_comap]
    show comap (fun v : Fam ε ρ => v.1 l) (𝓝 0) = comap (norm ∘ fun v : Fam ε ρ => v.1 l) (𝓝 0)
    rw [← comap_comap, comap_norm_nhds_zero]
  refine h1.congr (fun k => ?_) (fun l => ?_)
  · obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous h1 _ (continuous_sn (ρ := ρ) b k)
    exact ⟨s, C, h⟩
  · obtain ⟨C, hC, h⟩ := norm_le_sn (ρ := ρ) hb l
    refine ⟨{l.length}, ⟨C, hC⟩, fun v => ?_⟩
    rw [Finset.sup_singleton]
    exact h v

theorem sn_act_le (h : ModRep ε ρ) (hb : ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X) (k : ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (g : Mx n) (hg : g ∈ UJset ε) (v : Fam ε ρ),
      sn ρ b k (act h hg v) ≤ C * (1 + hs g) ^ N * sn ρ b k v := by
  induction k with
  | zero =>
    obtain ⟨C, N, hC⟩ := h.2.2
    refine ⟨|C|, N, abs_nonneg _, fun g hg v => ((ρ g).le_opNorm _).trans ?_⟩
    have := hs_nonneg g
    exact mul_le_mul_of_nonneg_right ((hC g hg).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))) (norm_nonneg _)
  | succ k ih =>
    obtain ⟨C, N, hC, ih⟩ := ih
    obtain ⟨A, hA, hsz⟩ := exists_sz_le φ
    refine ⟨∑ j, C * (A * (1 + hs (b j : Mx n))), N + 2,
      Finset.sum_nonneg fun j _ => by have := hs_nonneg (b j : Mx n); positivity, fun g hg v => ?_⟩
    rw [sn_succ, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have hg0 := hs_nonneg g
    have h1 : 1 + hs (adInv hg (b j) : Mx n) ≤ (1 + hs g) * (1 + hs (b j : Mx n)) * (1 + hs g) := by
      refine (one_add_hs_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [← hs_inv hg]
      exact one_add_hs_mul_le _ _
    rw [der_act]
    refine (ih g hg _).trans ((mul_le_mul_of_nonneg_left ((sn_der_le hb k _ v).trans
      (mul_le_mul_of_nonneg_right ((hsz _).trans (mul_le_mul_of_nonneg_left h1 hA)) (apply_nonneg _ _)))
      (by positivity)).trans_eq ?_)
    ring

theorem hasDerivAt_conj (f : Mx n →ₗ[ℝ] ℝ) (X Y : Mx n) :
    HasDerivAt (fun t : ℝ => f ((NormedSpace.exp (t • X))⁻¹ * Y * NormedSpace.exp (t • X))) (f (Y * X - X * Y)) 0 := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  have h2 : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] ℝ)
      (c : ℝ → V) (c' : V), HasDerivAt c c' 0 → HasDerivAt (fun t => f (c t)) (f c') 0 := fun V _ _ _ f c c' h =>
    (LinearMap.toContinuousLinearMap f).hasFDerivAt.comp_hasDerivAt 0 h
  refine h2 (Mx n) f _ _ ?_
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0).mul_const Y).fun_mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  have e : ∀ t : ℝ, (NormedSpace.exp (t • X))⁻¹ = NormedSpace.exp (t • (-X)) := fun t => by
    rw [smul_neg, Matrix.exp_neg]
  rw [show (fun t : ℝ => (NormedSpace.exp (t • X))⁻¹ * Y * NormedSpace.exp (t • X)) =
    fun t : ℝ => NormedSpace.exp (t • (-X)) * Y * NormedSpace.exp (t • X) from funext fun t => by rw [e]]
  exact h1.congr_deriv (by simp [sub_eq_add_neg, add_comm])

theorem br_mem (X Y : lie (Jm ε)) : (Y * X - X * Y : Mx n) ∈ lie (Jm ε) := by
  have h1 : (X : Mx n)ᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left X.2
  have h2 : (Y : Mx n)ᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left Y.2
  show (Y * X - X * Y : Mx n)ᴴ * Jm ε + Jm ε * (Y * X - X * Y) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2, mul_neg, mul_neg,
    ← mul_assoc, ← mul_assoc, h1, h2]
  noncomm_ring

theorem map_der_eq (hb : ∀ X : lie (Jm ε), ∑ j, φ j X • b j = X) (T : Fam ε ρ →L[ℂ] Fam ε ρ) (X : lie (Jm ε))
    (v : Fam ε ρ) (l : List (lie (Jm ε))) : (T (der ρ X v)).1 l = ∑ j, φ j X • (T (der ρ (b j) v)).1 l := by
  rw [der_eq hb, map_sum]
  simp only [map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply]
  simp only [Complex.coe_smul]

theorem hasDerivAt_act_zero (h : ModRep ε ρ) (X : lie (Jm ε)) (l : List (lie (Jm ε))) (v : Fam ε ρ) :
    HasDerivAt (fun t : ℝ => (act h (exp_mem_UJ X.2 t) v).1 l) ((der ρ X v).1 l) 0 := by
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  induction l using List.reverseRecOn generalizing v with
  | nil => exact v.2.1 [] X
  | append_singleton l Y ih =>
    have e : ∀ t : ℝ, (act h (exp_mem_UJ X.2 t) v).1 (l ++ [Y]) = ∑ j,
        φ j ((NormedSpace.exp (t • (X : Mx n)))⁻¹ * Y * NormedSpace.exp (t • (X : Mx n))) •
          (act h (exp_mem_UJ X.2 t) (der ρ (b j) v)).1 l := fun t => by
      rw [← der_apply, der_act, map_der_eq hb]
      rfl
    simp only [e]
    convert HasDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) =>
      (hasDerivAt_conj (φ j) X Y).fun_smul (ih (der ρ (b j) v)) using 1
    have e1 : v.1 (l ++ [⟨_, br_mem X Y⟩]) = ∑ j, φ j (Y * X - X * Y) • (der ρ (b j) v).1 l :=
      map_der_eq hb 1 ⟨_, br_mem X Y⟩ v l
    have e2 := map_der_eq hb (der ρ X) Y v l
    have e3 := v.2.2.2 l [] Y X ⟨_, br_mem X Y⟩ rfl
    have e4 : ∀ hg : NormedSpace.exp ((0 : ℝ) • (X : Mx n)) ∈ UJset ε, ∀ w, act h hg w = w := fun hg =>
      act_one h hg (by simp)
    simp only [e4]
    simp only [zero_smul, NormedSpace.exp_zero, inv_one, one_mul, mul_one, Finset.sum_add_distrib, ← e1, ← e2]
    simp only [der_apply, List.append_assoc, List.cons_append, List.nil_append, ← e3]
    abel

theorem hasDerivAt_act (h : ModRep ε ρ) (X : lie (Jm ε)) (l : List (lie (Jm ε))) (v : Fam ε ρ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (act h (exp_mem_UJ X.2 t) v).1 l) ((act h (exp_mem_UJ X.2 s) (der ρ X v)).1 l) s := by
  have h1 := hasDerivAt_act_zero h X l (act h (exp_mem_UJ X.2 s) v)
  have e : adInv (exp_mem_UJ X.2 s) X = X := Subtype.ext <| by
    have hc : Commute (X : Mx n) (NormedSpace.exp (s • (X : Mx n))) := ((Commute.refl _).smul_right s).exp_right
    show _ * _ * _ = _
    rw [mul_assoc, hc.eq, ← mul_assoc, inv_mul_UJ (exp_mem_UJ X.2 s), one_mul]
  rw [der_act, e] at h1
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Eventually.of_forall fun t => ?_)
  exact congrArg (fun w : Fam ε ρ => w.1 l) (act_mul h _ _ _ (by rw [← exp_add_smul, sub_add_cancel]) v)

theorem continuous_mexp : Continuous (NormedSpace.exp : Mx n → Mx n) := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin n) (α := ℂ)
  exact continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt

open Classical in

def piOp (h : ModRep ε ρ) (g : Mx n) : Fam ε ρ →L[ℂ] Fam ε ρ := if hg : g ∈ UJset ε then act h hg else 1

open Classical in

def dpiOp (ε : Fin n → Bool) (ρ : Mx n → (E →L[ℂ] E)) (X : Mx n) : Fam ε ρ →L[ℂ] Fam ε ρ :=
  if hX : X ∈ lie (Jm ε) then der ρ ⟨X, hX⟩ else 0

theorem piOp_eq (h : ModRep ε ρ) {g : Mx n} (hg : g ∈ UJset ε) : piOp h g = act h hg := dif_pos hg

theorem dpiOp_eq (X : lie (Jm ε)) : dpiOp ε ρ X = der ρ X := dif_pos X.2

theorem tendsto_piOp_one (h : ModRep ε ρ) (v : Fam ε ρ) :
    Tendsto (fun g => piOp h g v) (𝓝[UJset ε] 1) (𝓝 v) := by
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  obtain ⟨L, hL, hL1, hLe⟩ := GlobalTheory.LocalLog.local_log_UJ n ε
  refine tendsto_subtype_rng.2 (tendsto_pi_nhds.2 fun l => ?_)
  obtain ⟨A, hA, h1⟩ := norm_le_sn (ρ := ρ) hb l
  obtain ⟨C, N, hC, h2⟩ := sn_act_le h hb l.length
  have h3 : ∀ᶠ X in 𝓝 (0 : Mx n), ∀ t ∈ Set.Icc (0 : ℝ) 1, hs (NormedSpace.exp (t • X)) < hs (1 : Mx n) + 1 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hc : Continuous fun z : Mx n × ℝ => hs (NormedSpace.exp (z.2 • z.1)) :=
      continuous_hs.comp (continuous_mexp.comp (continuous_snd.smul continuous_fst))
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  have hL0 : Tendsto L (𝓝 1) (𝓝 0) := hL1 ▸ hL.tendsto
  have h4 : Tendsto (fun g => A * (C * (1 + (hs (1 : Mx n) + 1)) ^ N * (sz φ (L g) * sn ρ b (l.length + 1) v)))
      (𝓝 1) (𝓝 0) := by
    have := ((((continuous_sz φ).tendsto 0).comp hL0).mul_const (sn ρ b (l.length + 1) v)).const_mul
      (C * (1 + (hs (1 : Mx n) + 1)) ^ N) |>.const_mul A
    simpa [sz] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (h4.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hLe, nhdsWithin_le_nhds (hL0.eventually h3)]
    with g hg h5 h6
  obtain ⟨hX, hg'⟩ := h5 hg
  have h7 := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hasDerivAt_act h ⟨L g, hX⟩ l v t).hasDerivWithinAt)
    (C := A * (C * (1 + (hs (1 : Mx n) + 1)) ^ N * (sz φ (L g) * sn ρ b (l.length + 1) v))) fun t ht => by
      refine (h1 _).trans (mul_le_mul_of_nonneg_left ((h2 _ _ _).trans ?_) hA)
      have := hs_nonneg (NormedSpace.exp (t • L g))
      have := hs_nonneg (1 : Mx n)
      have := (h6 t (Set.Ico_subset_Icc_self ht)).le
      exact mul_le_mul (by gcongr) (sn_der_le hb _ _ v) (apply_nonneg _ _) (by positivity)
  rw [act_one h (exp_mem_UJ hX 0) (by simp), ← piOp_eq] at h7
  simpa only [one_smul, hg'] using h7

theorem continuousOn_piOp (h : ModRep ε ρ) (v : Fam ε ρ) : ContinuousOn (fun g => piOp h g v) (UJset ε) := by
  intro a ha
  have h1 : Tendsto (fun g => a⁻¹ * g) (𝓝[UJset ε] a) (𝓝[UJset ε] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun g hg => mul_mem_UJ (inv_mem_UJ ha) hg⟩
    rw [← inv_mul_UJ ha]
    exact ((continuous_const.mul continuous_id).tendsto a).mono_left nhdsWithin_le_nhds
  refine (((piOp h a).continuous.tendsto v).comp ((tendsto_piOp_one h v).comp h1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with g hg
  simp only [Function.comp, piOp_eq h ha, piOp_eq h hg, piOp_eq h (mul_mem_UJ (inv_mem_UJ ha) hg)]
  exact (act_mul h _ _ _ (by rw [← mul_assoc, mul_inv_UJ ha, one_mul]) v).symm

theorem hasDRep_piOp (h : ModRep ε ρ) (X : lie (Jm ε)) (v : Fam ε ρ) : HasDRep (piOp h) X v (der ρ X v) := by
  refine tendsto_subtype_rng.2 (tendsto_pi_nhds.2 fun l => ?_)
  refine (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_act_zero h X l v)).congr fun t => ?_
  rw [act_one h (exp_mem_UJ X.2 0) (by simp), piOp_eq h (exp_mem_UJ X.2 t), ← Complex.ofReal_inv]
  simp only [zero_add, Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sub, Pi.sub_apply]
  simp only [Complex.coe_smul]

theorem smooth_frechet_rep (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)) (h : ModRep ε ρ) :
    IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) ∧
      ∃ (p : ℕ → Seminorm ℂ (Fam ε ρ)) (π dπ : Mx n → (Fam ε ρ →L[ℂ] Fam ε ρ)), IsSmoothModRep ε p π dπ ∧
        (∀ (g : Mx n) (hg : g ∈ UJset ε) (v : Fam ε ρ) (l : List (lie (Jm ε))),
          (π g v).1 l = ρ g (v.1 (l.map (adInv hg)))) ∧
        (∀ (X : lie (Jm ε)) (v : Fam ε ρ) (l : List (lie (Jm ε))), (dπ (X : Mx n) v).1 l = v.1 (l ++ [X])) ∧
        ∀ v : Fam ε ρ, ‖v.1 []‖ ≤ p 0 v := by
  obtain ⟨d, b, φ, hb⟩ := exists_frame ε
  refine ⟨GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε E ρ h, sn ρ b, piOp h, dpiOp ε ρ, ⟨withSeminorms_sn hb, ?_, fun a ha c hc => ?_,
    continuousOn_piOp h, fun X hX v => ?_, fun k => ?_⟩, fun g hg v l => by rw [piOp_eq h hg]; rfl,
    fun X v l => by rw [dpiOp_eq]; rfl, fun v => le_rfl⟩
  · exact ContinuousLinearMap.ext fun v => by rw [piOp_eq h (one_mem_UJ ε), act_one h _ rfl]; rfl
  · exact ContinuousLinearMap.ext fun v => by
      rw [piOp_eq h ha, piOp_eq h hc, piOp_eq h (mul_mem_UJ ha hc)]
      exact act_mul h _ _ _ rfl v
  · rw [dpiOp_eq ⟨X, hX⟩]
    exact hasDRep_piOp h ⟨X, hX⟩ v
  · obtain ⟨C, N, hC, h1⟩ := sn_act_le h hb k
    lift C to NNReal using hC
    refine ⟨C • sn ρ b k, N, (continuous_sn b k).const_smul C, fun g hg v => ?_⟩
    rw [piOp_eq h hg]
    refine (h1 g hg v).trans_eq ?_
    show _ = _ * ((C : ℝ) * _)
    ring

end GlobalTheory.TypeSum.SmoothFrechet

end
