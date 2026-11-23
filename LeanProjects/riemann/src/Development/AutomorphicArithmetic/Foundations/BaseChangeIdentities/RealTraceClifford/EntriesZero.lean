import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewExp

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

namespace UpperTheory.RealTr.DerivativeAtIdentity

variable {n : ℕ}

private def dX {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → Module.End ℂ V) (X : Mat n) :
    Module.End ℂ V := ∑ a, ∑ b, X a b • F a b

private theorem dX_apply {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → Module.End ℂ V) (X : Mat n) (w : V) :
    dX F X w = ∑ a, ∑ b, X a b • F a b w := by
  simp [dX, LinearMap.sum_apply]

private theorem gam (X : Mat n) (hX : Xᴴ = -X) :
    ∃ γ : ℝ → UK n, (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) ∧ (∀ s h, γ (h + s) = γ h * γ s) ∧ γ 0 = 1 := by
  have hs : ∀ t : ℝ, ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) := fun t => by
    simp [Matrix.conjTranspose_smul, hX]
  refine ⟨fun t => ⟨NormedSpace.exp ((t : ℂ) • X), ((skewExp n).1 _ (hs t))⟩, fun t => rfl, fun s h => ?_, ?_⟩
  · apply Subtype.ext
    show NormedSpace.exp (((h + s : ℝ) : ℂ) • X) = NormedSpace.exp ((h : ℂ) • X) * NormedSpace.exp ((s : ℂ) • X)
    rw [← Matrix.exp_add_of_commute]
    · congr 1
      push_cast
      rw [add_smul]
    · exact ((Commute.refl X).smul_left _).smul_right _
  · apply Subtype.ext
    show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
    simp

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : UK n →* (V →ₗ[ℂ] V)}
  {F : Fin n → Fin n → Module.End ℂ V}

private theorem der0 (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (w : V) : HasDerivAt (fun t : ℝ => σ (γ t) w) (dX F X w) 0 := by
  obtain ⟨S, -, hw, -, -, hd⟩ := h.2 w
  rw [dX_apply]
  exact hd X γ hγ w hw

private theorem derS (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (hm : ∀ s h, γ (h + s) = γ h * γ s) (w : V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => σ (γ t) w) (dX F X (σ (γ s) w)) s := by
  have h0 := der0 h hγ (σ (γ s) w)
  have h1 : HasDerivAt (fun t : ℝ => σ (γ (t - s)) (σ (γ s) w)) (dX F X (σ (γ s) w)) s := by
    have : HasDerivAt (fun t : ℝ => σ (γ t) (σ (γ s) w)) (dX F X (σ (γ s) w)) (s - s) := by
      simpa using h0
    exact HasDerivAt.comp_sub_const s s this
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show σ (γ t) w = σ (γ (t - s)) (σ (γ s) w)
  have := hm s (t - s)
  rw [sub_add_cancel] at this
  rw [this, map_mul]
  rfl

private theorem skw (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (h0 : γ 0 = 1) (u : V) : ⟪u, dX F X u⟫_ℂ + ⟪dX F X u, u⟫_ℂ = 0 := by
  have hu := der0 h hγ u
  have hi := hu.inner ℂ hu
  have hc : (fun t : ℝ => ⟪σ (γ t) u, σ (γ t) u⟫_ℂ) = fun _ => ⟪u, u⟫_ℂ := funext fun t => h.1 _ _ _
  have h1 : σ (γ 0) u = u := by rw [h0, map_one]; rfl
  rw [hc, h1] at hi
  exact hi.unique (hasDerivAt_const _ _)

private theorem zero_of (h : IsDerivK σ F) {X : Mat n} {γ : ℝ → UK n} (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X))
    (h0 : γ 0 = 1) (d : ℝ → V) (hd : ∀ s, HasDerivAt d (dX F X (d s)) s) (hz : d 0 = 0) (s : ℝ) : d s = 0 := by
  have hder : ∀ r, HasDerivAt (fun t : ℝ => ⟪d t, d t⟫_ℂ) 0 r := fun r => by
    have := (hd r).inner ℂ (hd r)
    rwa [skw h hγ h0] at this
  have hc := is_const_of_deriv_eq_zero (fun r => (hder r).differentiableAt) (fun r => (hder r).deriv) s 0
  simp only [hz, inner_zero_left] at hc
  exact inner_self_eq_zero.1 hc

end

end UpperTheory.RealTr.DerivativeAtIdentity

open UpperTheory.RealTr.DerivativeAtIdentity in
private theorem single_dX {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (D : Fin n → Fin n → V) (a b : Fin n) (z : ℂ) :
    ∑ c, ∑ d, (Matrix.single a b z : Mat n) c d • D c d = z • D a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro d _ hd
    simp [Matrix.single_apply, hd.symm]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun d _ => ?_
    simp [Matrix.single_apply, hc.symm]
  · simp

open UpperTheory.RealTr.DerivativeAtIdentity in
private theorem entries_zero {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (D : Fin n → Fin n → V)
    (h : ∀ X : Mat n, Xᴴ = -X → ∑ c, ∑ d, X c d • D c d = 0) (a b : Fin n) : D a b = 0 := by
  have h1 := h (Matrix.single a b 1 - Matrix.single b a 1) (by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single])
  have h2 := h (Matrix.single a b Complex.I + Matrix.single b a Complex.I) (by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_single, Complex.star_def, Complex.conj_I, add_comm]
    ext c d
    simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
    split_ifs <;> simp [add_comm])
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    single_dX] at h1 h2
  have h3 : D a b + D b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) h2
    simpa [smul_add, smul_smul] using this
  simp only [one_smul] at h1
  have h4 : (2 : ℂ) • D a b = 0 := by
    rw [two_smul]
    calc D a b + D a b = (D a b - D b a) + (D a b + D b a) := by abel
      _ = 0 := by rw [h1, h3, add_zero]
  exact (smul_eq_zero.1 h4).resolve_left two_ne_zero

open UpperTheory.RealTr.DerivativeAtIdentity in
theorem UpperTheory.RealTr.derAt :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : UK n →* (V →ₗ[ℂ] V)) (F : Fin n → Fin n → Module.End ℂ V), IsDerivK σ F →
      (∀ (μ θ : Wt n) (k : UK n) (v : V), k.1 = diagonal (fun a => Complex.exp (Complex.I * θ a)) → v ∈ wsp F μ → σ k v = evT θ (ex μ) • v) ∧
      ∀ (N : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] (σ' : UK n →* (N →ₗ[ℂ] N))
        (F' : Fin n → Fin n → Module.End ℂ N), IsDerivK σ' F' → ∀ t : N →ₗ[ℂ] V, (∀ k x, t (σ' k x) = σ k (t x)) ↔ t ∈ homL F' F := by
  intro n V _ _ σ F hF
  refine ⟨?_, ?_⟩
  · intro μ θ k v hk hv
    set X : Mat n := diagonal (fun a => Complex.I * (θ a : ℂ)) with hXd
    have hXs : Xᴴ = -X := by
      have hst : (star fun a => Complex.I * (θ a : ℂ)) = fun a => -(Complex.I * (θ a : ℂ)) := by
        ext a
        simp
      rw [hXd, Matrix.diagonal_conjTranspose, hst, ← Matrix.diagonal_neg]
    obtain ⟨γ, hγ, hm, h0⟩ := gam X hXs
    set c : ℂ := Complex.I * ∑ a, (θ a : ℂ) * (μ a : ℂ) with hc
    have hdv : dX F X v = c • v := by
      rw [dX_apply]
      have : ∀ a, ∑ b, X a b • F a b v = (Complex.I * (θ a : ℂ) * (μ a : ℂ)) • v := fun a => by
        rw [Finset.sum_eq_single a]
        · rw [hXd, Matrix.diagonal_apply_eq, hv a, smul_smul]
        · intro b _ hb
          simp [hXd, Matrix.diagonal_apply_ne _ hb.symm]
        · simp
      simp only [this, ← Finset.sum_smul, hc, Finset.mul_sum, mul_assoc]
    have hexp : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t) • v) ((Complex.exp (c * s) * c) • v) s := fun s => by
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul c
      exact h1.cexp.smul_const v
    have hz := zero_of hF hγ h0 (fun s => σ (γ s) v - Complex.exp (c * s) • v)
      (fun s => by
        have := (derS hF hγ hm v s).fun_sub (hexp s)
        convert this using 1
        rw [map_sub, map_smul, hdv, smul_smul]) (by
        simp [h0]) 1
    have hg : γ 1 = k := by
      apply Subtype.ext
      rw [hγ, hk, hXd]
      simp [Matrix.exp_diagonal]
      intro i
      rw [Complex.exp_eq_exp_ℂ]
    have e := sub_eq_zero.1 hz
    rw [hg] at e
    rw [e]
    congr 1
    simp [evT, ex, hc]
  · intro N _ _ _ σ' F' hF' t
    let tc : N →L[ℝ] V := (LinearMap.toContinuousLinearMap t).restrictScalars ℝ
    have htc : ∀ x, tc x = t x := fun _ => rfl
    have hcomp : ∀ {X : Mat n} {γ : ℝ → UK n} (x : N) (s : ℝ) (y : N),
        HasDerivAt (fun r : ℝ => σ' (γ r) x) y s → HasDerivAt (fun r : ℝ => t (σ' (γ r) x)) (t y) s := fun x s y h =>
      tc.hasFDerivAt.comp_hasDerivAt s h
    constructor
    · intro hk a b x
      have := entries_zero (fun a b => t (F' a b x) - F a b (t x)) (fun X hX => by
        obtain ⟨γ, hγ, hm, h0⟩ := gam X hX
        have h1 := hcomp (X := X) x 0 _ (der0 hF' hγ x)
        simp only [hk] at h1
        have h2 := h1.unique (der0 hF hγ (t x))
        rw [dX_apply, dX_apply, map_sum] at h2
        simp only [map_sum, map_smul] at h2
        simp only [smul_sub, Finset.sum_sub_distrib]
        exact sub_eq_zero.2 h2) a b
      exact sub_eq_zero.1 this
    · intro ht k x
      obtain ⟨X, hX, hkX⟩ := (skewExp n).2 k
      obtain ⟨γ, hγ, hm, h0⟩ := gam X hX
      have hI : ∀ y : N, t (dX F' X y) = dX F X (t y) := fun y => by
        rw [dX_apply, dX_apply, map_sum]
        simp only [map_sum, map_smul]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [ht a b y]
      have hz := zero_of hF hγ h0 (fun s => t (σ' (γ s) x) - σ (γ s) (t x))
        (fun s => by
          have := (hcomp (X := X) x s _ (derS hF' hγ hm x s)).fun_sub (derS hF hγ hm (t x) s)
          convert this using 1
          rw [map_sub, hI]) (by
          simp [h0]) 1
      have hg : γ 1 = k := by
        apply Subtype.ext
        rw [hγ, ← hkX]
        simp
      rw [hg] at hz
      exact sub_eq_zero.1 hz
