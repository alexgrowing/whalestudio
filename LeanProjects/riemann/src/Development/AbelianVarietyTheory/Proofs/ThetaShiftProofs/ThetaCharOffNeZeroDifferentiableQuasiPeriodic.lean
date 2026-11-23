import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

noncomputable section

open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaBlock

variable {g : ℕ} {S : Finset (Fin g)}

def offEquiv (S : Finset (Fin g)) : {n : Fin g → ℤ // ∀ k ∈ S, n k = 0} ≃ ({k // k ∉ S} → ℤ) where
  toFun n i := n.1 i
  invFun l := ⟨fun k => if h : k ∈ S then 0 else l ⟨k, h⟩, fun k hk => dif_pos hk⟩
  left_inv n := by
    refine Subtype.ext (funext fun k => ?_)
    by_cases h : k ∈ S
    · simp [h, n.2 k h]
    · simp [h]
  right_inv l := by
    funext i
    simp [i.2]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem submatrix_mem_siegelH_of_posDef_im (S : Finset (Fin g)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    τ.submatrix (Subtype.val : {k // k ∉ S} → Fin g) Subtype.val ∈ _root_.ReciprocityTheory.PTheta.SiegelH {k // k ∉ S} := by
  unfold _root_.ReciprocityTheory.PTheta.SiegelH
  exact ⟨hs.submatrix _, hp.submatrix Subtype.val_injective⟩

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem ofReal_re_eq_self_of_eq_zero_or_half {c : ℂ} (h : c = 0 ∨ c = 1 / 2) :
    ((c.re : ℝ) : ℂ) = c := by
  rcases h with rfl | rfl
  · simp
  · apply Complex.ext <;> simp

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem dotProduct_eq_restrict_of_vanishing (S : Finset (Fin g)) {v : Fin g → ℂ}
    (hv : ∀ k ∈ S, v k = 0) (w : Fin g → ℂ) :
    v ⬝ᵥ w = (fun i : {k // k ∉ S} => v i) ⬝ᵥ (fun i : {k // k ∉ S} => w i) := by
  unfold dotProduct
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => k ∉ S)]
  have h0 : ∑ i : {k // ¬ k ∉ S}, v i * w i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hv i (not_not.1 i.2), zero_mul]
  rw [h0, add_zero]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem mulVec_restrict_eq_submatrix_mulVec_of_vanishing (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    {v : Fin g → ℂ} (hv : ∀ k ∈ S, v k = 0) :
    (fun i : {k // k ∉ S} => (τ *ᵥ v) i) =
      τ.submatrix Subtype.val Subtype.val *ᵥ (fun i : {k // k ∉ S} => v i) := by
  funext i
  simp only [mulVec, submatrix_apply]
  rw [dotProduct_comm, dotProduct_eq_restrict_of_vanishing S hv, dotProduct_comm]

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in
private theorem thetaCharOff_eq_theta_submatrix (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ)
    (c₁ c₂ : Fin g → ℂ) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2)
    (hS : ∀ k ∈ S, c₁ k = 0) (z : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z = _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff _root_.ReciprocityTheory.PTheta.theta _root_.ReciprocityTheory.PTheta.thetaTerm _root_.ReciprocityTheory.PTheta.eC _root_.ReciprocityTheory.PTheta.shiftVec _root_.ReciprocityTheory.PTheta.ofRealVec
  rw [← (_root_.GlobalTheory.ThetaBlock.offEquiv S).tsum_eq]
  congr 1
  funext n
  have hv : ∀ k ∈ S, ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) k = 0 := fun k hk => by
    simp [n.2 k hk, hS k hk]
  have hw : (fun i : {k // k ∉ S} =>
      (((_root_.GlobalTheory.ThetaBlock.offEquiv S n) i : ℤ) : ℂ) + (((c₁ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => ((fun i => ((n.1 i : ℤ) : ℂ)) + c₁) i := by
    funext i
    rw [ofReal_re_eq_self_of_eq_zero_or_half (h₁ i)]
    rfl
  have hz : (fun i : {k // k ∉ S} => z i) + (fun i : {k // k ∉ S} => (((c₂ i).re : ℝ) : ℂ)) =
      fun i : {k // k ∉ S} => (z + c₂) i := by
    funext i
    simp [ofReal_re_eq_self_of_eq_zero_or_half (h₂ i)]
  rw [hw, hz, dotProduct_eq_restrict_of_vanishing S hv (τ *ᵥ _), mulVec_restrict_eq_submatrix_mulVec_of_vanishing S τ hv,
    dotProduct_eq_restrict_of_vanishing S hv (z + c₂)]
  congr 1
  ring

open Matrix in
variable {g : ℕ} {S : Finset (Fin g)} in

theorem _root_.GlobalTheory.ThetaBlock.thetaCharOff_ne_zero_differentiable_quasiPeriodic (g : ℕ) (S : Finset (Fin g))
    (τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (h₁ : ∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2)
    (h₂ : ∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) (hS : ∀ k ∈ S, c₁ k = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ ≠ 0 ∧ Differentiable ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂) ∧
      ∀ m n : Fin g → ℤ, (∀ k ∈ S, n k = 0) → ∃ a : ℂ, a ≠ 0 ∧ ∀ z,
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
          a * Complex.exp (-(2 * Real.pi * Complex.I) * ((fun i => (n i : ℂ)) ⬝ᵥ z)) *
            _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ z := by
  have hτ := submatrix_mem_siegelH_of_posDef_im S hs hp
  have hfun : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff S τ c₁ c₂ = fun z => _root_.ReciprocityTheory.PTheta.theta (fun i : {k // k ∉ S} => (c₁ i).re)
      (fun i : {k // k ∉ S} => (c₂ i).re) (fun i : {k // k ∉ S} => z i)
      (τ.submatrix Subtype.val Subtype.val) :=
    funext (thetaCharOff_eq_theta_submatrix S τ c₁ c₂ h₁ h₂ hS)
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    obtain ⟨w, hw⟩ := Function.ne_iff.1
      (_root_.GlobalTheory.theta_ne_zero hτ (fun i : {k // k ∉ S} => (c₁ i).re)
        (fun i : {k // k ∉ S} => (c₂ i).re))
    apply hw
    have h := congrFun h0 (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩)
    rw [hfun] at h
    have hr : (fun i : {k // k ∉ S} => (fun k => if h : k ∈ S then 0 else w ⟨k, h⟩) i.1) = w := by
      funext i
      simp [i.2]
    simp only [Pi.zero_apply] at h
    rwa [hr] at h
  · rw [hfun]
    exact (_root_.GlobalTheory.differentiable_theta hτ _ _).comp (by fun_prop)
  · intro m n hn
    set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
    set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
    have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
      intro x y
      rw [dotProduct_mulVec, ← mulVec_transpose, hs.eq, dotProduct_comm]
    refine ⟨Complex.exp (2 * Real.pi * Complex.I * (c₁ ⬝ᵥ M) -
      Real.pi * Complex.I * (N ⬝ᵥ τ *ᵥ N) - 2 * Real.pi * Complex.I * (N ⬝ᵥ c₂)),
      Complex.exp_ne_zero _, fun z => ?_⟩
    let e : {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} ≃ {p : Fin g → ℤ // ∀ k ∈ S, p k = 0} :=
      { toFun := fun p => ⟨p.1 - n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        invFun := fun p => ⟨p.1 + n, fun k hk => by simp [p.2 k hk, hn k hk]⟩
        left_inv := fun p => by ext; simp
        right_inv := fun p => by ext; simp }
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaCharOff
    rw [← e.tsum_eq, ← tsum_mul_left]
    congr 1
    funext p
    have hQ : (fun i => (((e p).1 i : ℤ) : ℂ)) = (fun i => ((p.1 i : ℤ) : ℂ)) - N := by
      funext i
      simp [e, hN]
    rw [hQ, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨∑ i, (p.1 i - n i) * m i, ?_⟩
    have hcast : ((∑ i, (p.1 i - n i) * m i : ℤ) : ℂ) =
        (fun i => ((p.1 i : ℤ) : ℂ)) ⬝ᵥ M - N ⬝ᵥ M := by
      simp [dotProduct, hM, hN, Finset.sum_sub_distrib, sub_mul]
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, mulVec_add,
      mulVec_sub]
    linear_combination (Real.pi * Complex.I) * hsym (fun i => ((p.1 i : ℤ) : ℂ)) N +
      (Real.pi * Complex.I) * hsym c₁ N - (2 * Real.pi * Complex.I) * hcast

end GlobalTheory.ThetaBlock
