import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory

namespace CentralStepEigen

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem aeval_sub_mem (T : Module.End ℂ V) (A : Submodule ℂ V) (hA : ∀ x ∈ A, T x ∈ A) (a : ℂ)
    (w : V) (hw : T w - a • w ∈ A) (f : Polynomial ℂ) :
    Polynomial.aeval T f w - f.eval a • w ∈ A := by
  have hpow : ∀ n : ℕ, (T ^ n) w - a ^ n • w ∈ A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (T ^ (n + 1)) w - a ^ (n + 1) • w = T ((T ^ n) w - a ^ n • w) + a ^ n • (T w - a • w) := by
        rw [pow_succ', Module.End.mul_apply, map_sub, map_smul, smul_sub, pow_succ, mul_smul]
        abel
      rw [e]
      exact A.add_mem (hA _ ih) (A.smul_mem _ hw)
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    have e : Polynomial.aeval T (p + q) w - (p + q).eval a • w =
        (Polynomial.aeval T p w - p.eval a • w) + (Polynomial.aeval T q w - q.eval a • w) := by
      rw [map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul]
      abel
    rw [e]
    exact A.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, mul_smul, ← smul_sub]
    exact A.smul_mem c (hpow n)

theorem aeval_apply_comm (T U : Module.End ℂ V) (h : U * T = T * U) (f : Polynomial ℂ) (v : V) :
    Polynomial.aeval T f (U v) = U (Polynomial.aeval T f v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    have hc : Commute U (T ^ n) := (Commute.pow_right h n)
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, ← Module.End.mul_apply,
      ← Module.End.mul_apply, hc.eq]

end CentralStepEigen

open CentralStepEigen in

theorem exists_intertwining_bijOn_eigen_of_central_step :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G X) (N : ℕ) (S : Fin (N + 1) → Subrepresentation ρ),
    Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ → ∀ (z : G), (∀ g, g * z = z * g) → ∀ (t₀ : Fin N) (a : ℂ),
    Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv σ) → (∀ y, σ z y = a • y) →
    (∀ t, t ≠ t₀ → ∃ q : Polynomial ℂ, q.eval a ≠ 0 ∧
      ∀ w ∈ (S t.succ).toSubmodule, Polynomial.aeval (ρ z) q w ∈ (S t.castSucc).toSubmodule) →
    ∃ p : ρ.IntertwiningMap σ, (∀ y, ∃ v, ρ z v = a • v ∧ p v = y) ∧
      ∀ v, ρ z v = a • v → p v = 0 → v = 0 := by
  intro G V X _ _ _ _ _ ρ σ N S hmono hbot htop z hz t₀ a hΨ hσ hq
  obtain ⟨Ψ⟩ := hΨ
  have ht0 := t₀.isLt
  set B := S t₀.succ with hBdef
  set A := S t₀.castSucc with hAdef
  set T : Module.End ℂ V := ρ z with hT
  have hq' : ∀ t : Fin N, ∃ q : Polynomial ℂ, q.eval a ≠ 0 ∧ (t ≠ t₀ →
      ∀ w ∈ (S t.succ).toSubmodule, Polynomial.aeval T q w ∈ (S t.castSucc).toSubmodule) := by
    intro t
    by_cases ht : t = t₀
    · exact ⟨1, by simp, fun h => (h ht).elim⟩
    · obtain ⟨q, h1, h2⟩ := hq t ht
      exact ⟨q, h1, fun _ => h2⟩
  choose q hq1 hq2 using hq'
  let qn : ℕ → Polynomial ℂ := fun i => if h : i < N then q ⟨i, h⟩ else 1
  have hqn : ∀ i, (qn i).eval a ≠ 0 := by
    intro i
    by_cases h : i < N
    · simp only [qn, dif_pos h]; exact hq1 _
    · simp [qn, h]

  have hZ : ∀ y, subQuot B A z y = a • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hσ, map_smul,
      Representation.Equiv.toLinearEquiv_apply]
  have hkey : ∀ w ∈ B.toSubmodule, T w - a • w ∈ A.toSubmodule := by
    intro w hw
    have h := hZ (Submodule.Quotient.mk ⟨w, hw⟩)
    have e2 : subQuot B A z (Submodule.Quotient.mk ⟨w, hw⟩) =
        Submodule.Quotient.mk ⟨ρ z w, B.apply_mem_toSubmodule z hw⟩ := rfl
    rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h
    simpa using h
  have hBf : ∀ f : Polynomial ℂ, ∀ w ∈ B.toSubmodule,
      Polynomial.aeval T f w - f.eval a • w ∈ A.toSubmodule := fun f w hw =>
    aeval_sub_mem T A.toSubmodule (fun x hx => A.apply_mem_toSubmodule z hx) a w (hkey w hw) f
  have hEig : ∀ f : Polynomial ℂ, ∀ v, T v = a • v → Polynomial.aeval T f v = f.eval a • v := by
    intro f v hv
    have h := aeval_sub_mem T ⊥ (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; simp [hx]) a v
      (by rw [hv, sub_self]; exact Submodule.zero_mem _) f
    rw [Submodule.mem_bot, sub_eq_zero] at h
    exact h

  have L1 : ∀ j (hj : j ≤ t₀.val), ∀ v ∈ (S ⟨j, by omega⟩).toSubmodule,
      Polynomial.aeval T (∏ i ∈ Finset.range j, qn i) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro hj v hv
      have e : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
      rw [e, hbot] at hv
      have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
      simp [hv0]
    | succ j ih =>
      intro hj v hv
      let t : Fin N := ⟨j, by omega⟩
      have ht : t ≠ t₀ := fun e => by
        have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨j + 1, by omega⟩ := by ext; simp [t]
        rw [this]; exact hv
      have h2 := hq2 t ht v hvs
      have e3 : qn j = q t := by
        show (if h : j < N then q ⟨j, h⟩ else 1) = q t
        rw [dif_pos (show j < N by omega)]
      rw [Finset.prod_range_succ, Polynomial.aeval_mul, Module.End.mul_apply, e3]
      exact ih (by omega) _ h2

  have L2 : ∀ m (h : t₀.val + 1 + m < N + 1), ∀ v ∈ (S ⟨t₀.val + 1 + m, h⟩).toSubmodule,
      Polynomial.aeval T (∏ i ∈ Finset.range m, qn (t₀.val + 1 + i)) v ∈ B.toSubmodule := by
    intro m
    induction m with
    | zero =>
      intro h v hv
      have e : (⟨t₀.val + 1 + 0, h⟩ : Fin (N + 1)) = t₀.succ := by ext; simp
      rw [e] at hv
      simpa using hv
    | succ m ih =>
      intro h v hv
      let t : Fin N := ⟨t₀.val + 1 + m, by omega⟩
      have ht : t ≠ t₀ := fun e => by
        have := congrArg Fin.val e; simp only [t] at this; omega
      have hvs : v ∈ (S t.succ).toSubmodule := by
        have : t.succ = ⟨t₀.val + 1 + (m + 1), h⟩ := by ext; simp [t]; omega
        rw [this]; exact hv
      have h2 := hq2 t ht v hvs
      have e3 : qn (t₀.val + 1 + m) = q t := by
        show (if h : t₀.val + 1 + m < N then q ⟨t₀.val + 1 + m, h⟩ else 1) = q t
        rw [dif_pos (show t₀.val + 1 + m < N by omega)]
      rw [Finset.prod_range_succ, Polynomial.aeval_mul, Module.End.mul_apply, e3]
      exact ih (by omega) _ h2
  set M := N - (t₀.val + 1) with hMdef
  set Qg := ∏ i ∈ Finset.range M, qn (t₀.val + 1 + i) with hQgdef
  set Qs := ∏ i ∈ Finset.range t₀.val, qn i with hQsdef
  have hQg : Qg.eval a ≠ 0 := by
    rw [hQgdef, Polynomial.eval_prod]; exact Finset.prod_ne_zero_iff.2 (fun i _ => hqn _)
  have hQs : Qs.eval a ≠ 0 := by
    rw [hQsdef, Polynomial.eval_prod]; exact Finset.prod_ne_zero_iff.2 (fun i _ => hqn _)
  have hM : ∀ v, Polynomial.aeval T Qg v ∈ B.toSubmodule := by
    intro v
    refine L2 M (by omega) v ?_
    have e : (⟨t₀.val + 1 + M, by omega⟩ : Fin (N + 1)) = Fin.last N := by ext; simp; omega
    rw [e, htop]
    trivial
  have hcomm : ∀ (f : Polynomial ℂ) g v, Polynomial.aeval T f (ρ g v) = ρ g (Polynomial.aeval T f v) := by
    intro f g v
    refine aeval_apply_comm T (ρ g) ?_ f v
    rw [hT, ← map_mul, ← map_mul, hz]
  let plin : V →ₗ[ℂ] X := Ψ.toLinearMap ∘ₗ (A.toSubmodule.comap B.toSubmodule.subtype).mkQ ∘ₗ
    LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM
  have hφ : ∀ g v, plin (ρ g v) = σ g (plin v) := by
    intro g v
    have e6 : (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM) (ρ g v) =
        B.toRepresentation g (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM v) :=
      Subtype.ext (hcomm Qg g v)
    show Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ _ hM (ρ g v))) =
      σ g (Ψ.toIntertwiningMap (Submodule.mkQ _ (LinearMap.codRestrict _ _ hM v)))
    have e8 : Submodule.mkQ (A.toSubmodule.comap B.toSubmodule.subtype)
        (B.toRepresentation g (LinearMap.codRestrict B.toSubmodule (Polynomial.aeval T Qg) hM v)) =
        subQuot B A g (Submodule.mkQ _ (LinearMap.codRestrict B.toSubmodule _ hM v)) := rfl
    rw [e6, e8]
    exact Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap g _
  let p : ρ.IntertwiningMap σ := plin.intertwiningMap_of_isIntertwiningMap ρ σ hφ
  have hp : ∀ v, p v = Ψ.toLinearEquiv (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg v, hM v⟩) :=
    fun v => rfl
  refine ⟨p, ?_, ?_⟩
  · intro y
    obtain ⟨⟨b, hb⟩, hx⟩ := Submodule.Quotient.mk_surjective _ (Ψ.toLinearEquiv.symm y)
    set u := Polynomial.aeval T Qs b with hudef
    have hu : T u = a • u := by
      have h1 : Polynomial.aeval T Qs (T b - a • b) = 0 := L1 t₀.val le_rfl _ (hkey b hb)
      have h2 : Polynomial.aeval T Qs (T b) = T (Polynomial.aeval T Qs b) :=
        aeval_apply_comm T T rfl Qs b
      rw [map_sub, map_smul, h2] at h1
      exact sub_eq_zero.1 h1
    set c := (Qg * Qs).eval a with hcdef
    have hc : c ≠ 0 := by rw [hcdef, Polynomial.eval_mul]; exact mul_ne_zero hQg hQs
    have hpu : p u = c • y := by
      have e1 : Polynomial.aeval T Qg u = Polynomial.aeval T (Qg * Qs) b := by
        rw [Polynomial.aeval_mul, Module.End.mul_apply]
      have e2 := hBf (Qg * Qs) b hb
      rw [hp]
      have e3 : (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg u, hM u⟩ :
          B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) =
          c • Submodule.Quotient.mk ⟨b, hb⟩ := by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
        show Polynomial.aeval T Qg u - c • b ∈ A.toSubmodule
        rw [e1]
        exact e2
      rw [e3, map_smul, hx, LinearEquiv.apply_symm_apply]
    refine ⟨c⁻¹ • u, ?_, ?_⟩
    · rw [map_smul, hu, smul_comm]
    · rw [map_smul, hpu, smul_smul, inv_mul_cancel₀ hc, one_smul]
  · intro v hv hpv
    have hQgv := hEig Qg v hv
    have hvA : v ∈ A.toSubmodule := by
      rw [hp] at hpv
      have h1 : (Submodule.Quotient.mk ⟨Polynomial.aeval T Qg v, hM v⟩ :
          B.toSubmodule ⧸ A.toSubmodule.comap B.toSubmodule.subtype) = 0 :=
        (LinearEquiv.map_eq_zero_iff _).1 hpv
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
      have h1' : Polynomial.aeval T Qg v ∈ A.toSubmodule := h1
      rw [hQgv] at h1'
      exact (A.toSubmodule.smul_mem_iff hQg).1 h1'
    have h := L1 t₀.val le_rfl v hvA
    rw [hEig Qs v hv] at h
    exact (smul_eq_zero.1 h).resolve_left hQs

end GlobalTheory
