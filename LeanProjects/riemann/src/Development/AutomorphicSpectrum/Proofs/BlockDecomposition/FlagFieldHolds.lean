import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold

noncomputable section

open Matrix
open scoped ContDiff ComplexConjugate ComplexOrder

namespace GlobalTheory.CompanionTheory.FlagHerm

open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def im (x : Mat n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) := (fun v => x *ᵥ v) '' U

structure IsPr (P : Mat n) (U : Set (Fin n → ℂ)) : Prop where
  herm : Pᴴ = P
  idem : P * P = P
  mem : ∀ v, v ∈ U ↔ P *ᵥ v = v

theorem one_sub_idem {Q : Mat n} (h : Q * Q = Q) : (1 - Q) * (1 - Q) = 1 - Q := by
  rw [sub_mul, mul_sub, mul_sub, h, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  abel

theorem mat_ext {A B : Mat n} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B :=
  Matrix.mulVec_injective (funext h)

theorem exists_isPr (W : Submodule ℂ (Fin n → ℂ)) : ∃ Q : Mat n, IsPr Q (W : Set (Fin n → ℂ)) := by
  let e := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let U : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := W.comap e.toLinearMap
  let p : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := U.starProjection
  let Φ := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
  have hΦ : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ), e (Φ A (e.symm v)) = A *ᵥ v := fun A v => rfl
  have hsp : IsStarProjection p := isStarProjection_starProjection
  have hpp : p * p = p := hsp.isIdempotentElem
  have hps : star p = p := hsp.isSelfAdjoint
  refine ⟨Φ.symm p, ?_, ?_, fun v => ?_⟩
  · rw [← star_eq_conjTranspose, ← map_star, hps]
  · rw [← map_mul, hpp]
  · have h1 : (Φ.symm p) *ᵥ v = e (p (e.symm v)) := by
      rw [← hΦ, Φ.apply_symm_apply]
    have h2 : v ∈ (W : Set (Fin n → ℂ)) ↔ e.symm v ∈ U := by
      simp [U]
    rw [h1, h2, ← Submodule.starProjection_eq_self_iff (K := U)]
    exact ⟨fun h => by rw [show p (e.symm v) = e.symm v from h]; simp, fun h => by
      rw [← e.symm_apply_apply (p (e.symm v)), h]⟩

theorem IsPr.mul_of_sub {P P' : Mat n} {U U' : Set (Fin n → ℂ)} (h : IsPr P U) (h' : IsPr P' U') (hs : U ⊆ U') :
    P' * P = P :=
  mat_ext fun v => by
    rw [← mulVec_mulVec]
    exact (h'.mem _).1 (hs ((h.mem _).2 (by rw [mulVec_mulVec, h.idem])))

theorem IsPr.unique {P P' : Mat n} {U : Set (Fin n → ℂ)} (h : IsPr P U) (h' : IsPr P' U) : P = P' := by
  have h1 := h.mul_of_sub h' subset_rfl
  have h2 := h'.mul_of_sub h subset_rfl
  have h3 : P * P' = P := by
    have := congrArg conjTranspose h1
    rwa [conjTranspose_mul, h.herm, h'.herm] at this
  rw [← h3, h2]

theorem IsPr.perp {Q : Mat n} {W : Submodule ℂ (Fin n → ℂ)} (h : IsPr Q (W : Set (Fin n → ℂ))) :
    IsPr (1 - Q) (perp W) := by
  refine ⟨by rw [conjTranspose_sub, conjTranspose_one, h.herm], one_sub_idem h.idem, fun v => ?_⟩
  have hadj : ∀ a b : Fin n → ℂ, star (Q *ᵥ a) ⬝ᵥ b = star a ⬝ᵥ (Q *ᵥ b) := fun a b => by
    rw [star_mulVec, h.herm, dotProduct_mulVec]
  have hfix : ∀ a, Q *ᵥ (Q *ᵥ a) = Q *ᵥ a := fun a => by rw [mulVec_mulVec, h.idem]
  rw [sub_mulVec, one_mulVec]
  constructor
  · intro hv
    have h0 : star (Q *ᵥ v) ⬝ᵥ v = 0 := hv _ ((h.mem _).2 (hfix v))
    have h1 : star (Q *ᵥ v) ⬝ᵥ (Q *ᵥ v) = 0 := by
      have := hadj (Q *ᵥ v) v
      rwa [hfix, h0, eq_comm] at this
    rw [dotProduct_star_self_eq_zero] at h1
    rw [h1, sub_zero]
  · intro hv w hw
    have h0 : Q *ᵥ v = 0 := by simpa using hv
    have := hadj w v
    rwa [(h.mem _).1 hw, h0, dotProduct_zero] at this

theorem IsPr.unitary {P k : Mat n} {V : Set (Fin n → ℂ)} (h : IsPr P V) (h1 : kᴴ * k = 1) (h2 : k * kᴴ = 1) :
    IsPr (kᴴ * P * k) (im kᴴ V) := by
  refine ⟨by simp [conjTranspose_mul, h.herm, Matrix.mul_assoc], ?_, fun v => ?_⟩
  · calc kᴴ * P * k * (kᴴ * P * k) = kᴴ * P * (k * kᴴ) * P * k := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (P * P) * k := by rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [h.idem]
  · constructor
    · rintro ⟨w, hw, rfl⟩
      have := (h.mem w).1 hw
      simp only [mulVec_mulVec] at *
      rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← mulVec_mulVec, this]
    · intro hv
      refine ⟨k *ᵥ v, (h.mem _).2 ?_, ?_⟩
      · have := congrArg (fun u => k *ᵥ u) hv
        simp only [mulVec_mulVec] at this ⊢
        rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul] at this
      · simp only [mulVec_mulVec, h1, one_mulVec]

def Cm (Q x : Mat n) : Mat n := (x⁻¹ * Q)ᴴ * (x⁻¹ * Q) + (1 - Q)

def prF (Q x : Mat n) : Mat n := (x⁻¹ * Q) * (Cm Q x)⁻¹ * (x⁻¹ * Q)ᴴ

theorem Cm_mem {Q x : Mat n} (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) (hx : x ∈ GLs n) : Cm Q x ∈ GLs n := by
  by_contra hdet
  have hdet' : (Cm Q x).det = 0 := by simpa [GLs] using hdet
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet'
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  set B := x⁻¹ * Q with hB
  have hQB : Q * Bᴴ = Bᴴ := by
    rw [hB, conjTranspose_mul, hQ, ← Matrix.mul_assoc, hQ2]
  have hRB : (1 - Q) * Bᴴ = 0 := by rw [sub_mul, hQB, Matrix.one_mul, sub_self]
  have hRC : (1 - Q) * Cm Q x = 1 - Q := by
    rw [Cm, ← hB, mul_add, ← Matrix.mul_assoc, hRB, Matrix.zero_mul, zero_add, one_sub_idem hQ2]
  have hQC : Q * Cm Q x = Bᴴ * B := by
    rw [Cm, ← hB, mul_add, ← Matrix.mul_assoc, hQB]
    have : Q * (1 - Q) = 0 := by rw [mul_sub, hQ2, Matrix.mul_one, sub_self]
    rw [this, add_zero]
  have e1 : (1 - Q) *ᵥ v = 0 := by
    have := congrArg (fun u => (1 - Q) *ᵥ u) h0
    simpa only [mulVec_mulVec, hRC, mulVec_zero] using this
  have e2 : (Bᴴ * B) *ᵥ v = 0 := by
    have := congrArg (fun u => Q *ᵥ u) h0
    simpa only [mulVec_mulVec, hQC, mulVec_zero] using this
  have e3 : B *ᵥ v = 0 := Matrix.conjTranspose_mul_self_mulVec_eq_zero _ _ |>.1 e2
  have e4 : Q *ᵥ v = 0 := by
    have := congrArg (fun u => x *ᵥ u) e3
    simpa only [hB, mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hxu, Matrix.one_mul, mulVec_zero] using this
  apply hv
  have : v = (1 - Q) *ᵥ v + Q *ᵥ v := by rw [sub_mulVec, one_mulVec]; abel
  rw [this, e1, e4, add_zero]

theorem prF_isPr {Q x : Mat n} {U : Set (Fin n → ℂ)} (h : IsPr Q U) (hx : x ∈ GLs n) : IsPr (prF Q x) (im x⁻¹ U) := by
  have hQ := h.herm
  have hQ2 := h.idem
  have hC : IsUnit (Cm Q x).det := isUnit_iff_ne_zero.2 (Cm_mem hQ hQ2 hx)
  have hCh : (Cm Q x)ᴴ = Cm Q x := by
    simp only [Cm, conjTranspose_add, conjTranspose_sub, conjTranspose_one, hQ, conjTranspose_mul, conjTranspose_conjTranspose]
  have hCD := Matrix.mul_nonsing_inv _ hC
  have hDC := Matrix.nonsing_inv_mul _ hC
  have hDh : ((Cm Q x)⁻¹)ᴴ = (Cm Q x)⁻¹ := by rw [conjTranspose_nonsing_inv, hCh]
  unfold prF
  have hCdef : Cm Q x = (x⁻¹ * Q)ᴴ * (x⁻¹ * Q) + (1 - Q) := rfl
  generalize (Cm Q x)⁻¹ = D at *
  generalize Cm Q x = C at *
  have hBQ : (x⁻¹ * Q) * Q = x⁻¹ * Q := by rw [Matrix.mul_assoc, hQ2]
  have hQB : Q * (x⁻¹ * Q)ᴴ = (x⁻¹ * Q)ᴴ := by
    rw [conjTranspose_mul, hQ, ← Matrix.mul_assoc, hQ2]
  generalize hB : x⁻¹ * Q = B at *
  have hR : (1 - Q) * Q = 0 := by rw [sub_mul, hQ2, Matrix.one_mul, sub_self]
  have hR' : Q * (1 - Q) = 0 := by rw [mul_sub, hQ2, Matrix.mul_one, sub_self]
  have hCQ : C * Q = Bᴴ * B := by
    rw [hCdef, add_mul, hR, add_zero, Matrix.mul_assoc, hBQ]
  have hQC : Q * C = Bᴴ * B := by
    rw [hCdef, mul_add, hR', add_zero, ← Matrix.mul_assoc, hQB]
  have hDB : D * (Bᴴ * B) = Q := by rw [← hCQ, ← Matrix.mul_assoc, hDC, Matrix.one_mul]
  have hQD : Q * D = D * Q := by
    calc Q * D = D * (C * Q) * D := by rw [← Matrix.mul_assoc, hDC, Matrix.one_mul]
      _ = D * (Q * C) * D := by rw [hCQ, hQC]
      _ = D * Q * (C * D) := by simp only [Matrix.mul_assoc]
      _ = D * Q := by rw [hCD, Matrix.mul_one]
  have hPB : B * D * Bᴴ * B = B := by
    calc B * D * Bᴴ * B = B * (D * (Bᴴ * B)) := by simp only [Matrix.mul_assoc]
      _ = B := by rw [hDB, hBQ]
  refine ⟨by simp [conjTranspose_mul, hDh, Matrix.mul_assoc], ?_, fun v => ?_⟩
  · calc B * D * Bᴴ * (B * D * Bᴴ) = (B * D * Bᴴ * B) * D * Bᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPB]
  · constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' := (h.mem w).1 hw
      have : x⁻¹ *ᵥ w = B *ᵥ w := by rw [← hB, ← mulVec_mulVec, hw']
      simp only [this, mulVec_mulVec, hPB]
    · intro hv
      refine ⟨Q *ᵥ ((D * Bᴴ) *ᵥ v), (h.mem _).2 (by rw [mulVec_mulVec, hQ2]), ?_⟩
      show x⁻¹ *ᵥ (Q *ᵥ ((D * Bᴴ) *ᵥ v)) = v
      conv_rhs => rw [← hv]
      simp only [mulVec_mulVec, ← hB, Matrix.mul_assoc]

theorem cd_of_ent {f : Mat n → Mat n} {s : Set (Mat n)} (h : ∀ a b, ContDiffOn ℝ ∞ (fun x => f x a b) s) :
    ContDiffOn ℝ ∞ f s :=
  contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => h a b

theorem cd_ent {f : Mat n → Mat n} {s : Set (Mat n)} (h : ContDiffOn ℝ ∞ f s) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun x => f x a b) s :=
  (GlobalTheory.CompanionTheory.LengthGL.contDiff_ent a b).comp_contDiffOn h

theorem cd_mul {f g : Mat n → Mat n} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) :
    ContDiffOn ℝ ∞ (fun x => f x * g x) s :=
  cd_of_ent fun a b => by
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun c _ => (cd_ent hf a c).mul (cd_ent hg c b)

theorem cd_ct {f : Mat n → Mat n} {s : Set (Mat n)} (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun x => (f x)ᴴ) s :=
  cd_of_ent fun a b => by
    simp only [conjTranspose_apply]
    exact Complex.conjCLE.contDiff.comp_contDiffOn (cd_ent hf b a)

theorem prF_smooth {Q : Mat n} (hQ : Qᴴ = Q) (hQ2 : Q * Q = Q) : ContDiffOn ℝ ∞ (prF Q) (GLs n) := by
  have hi : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv
  have hB : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹ * Q) (GLs n) := cd_mul hi contDiffOn_const
  have hC : ContDiffOn ℝ ∞ (Cm Q) (GLs n) := (cd_mul (cd_ct hB) hB).add contDiffOn_const
  have hD : ContDiffOn ℝ ∞ (fun x => (Cm Q x)⁻¹) (GLs n) := hi.comp hC fun x hx => Cm_mem hQ hQ2 hx
  exact cd_mul (cd_mul hB hD) (cd_ct hB)

theorem im_mul (a b : Mat n) (U : Set (Fin n → ℂ)) : im (a * b) U = im a (im b U) := by
  simp only [im, Set.image_image, mulVec_mulVec]

theorem im_one (U : Set (Fin n → ℂ)) : im (1 : Mat n) U = U := by
  simp [im]

theorem im_cancel {a : Mat n} (ha : a ∈ GLs n) (U : Set (Fin n → ℂ)) : im a⁻¹ (im a U) = U := by
  rw [← im_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 ha), im_one]

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem mul_mem_GLs {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simpa [GLs, det_mul] using And.intro ha hb

theorem prF_one {Q : Mat n} {U : Set (Fin n → ℂ)} (h : IsPr Q U) : prF Q 1 = Q :=
  (prF_isPr h one_mem_GLs).unique (by simpa only [inv_one, im_one] using h)

theorem im_of_map {q : Mat n} {W : Submodule ℂ (Fin n → ℂ)} (h : W.map (Matrix.mulVecLin q) = W) :
    im q (W : Set (Fin n → ℂ)) = W := by
  have := congrArg (fun S : Submodule ℂ (Fin n → ℂ) => (S : Set (Fin n → ℂ))) h
  simp only [Submodule.map_coe] at this
  exact this

theorem flagField_holds : PositivityTheory.RgBcC.FlagField := by
  intro n W₁ W₂ hW hne
  obtain ⟨Q₁, h₁⟩ := exists_isPr W₁
  obtain ⟨Q₂, h₂⟩ := exists_isPr W₂
  have hH1 : prF Q₁ 1 - (1 - prF Q₂ 1) = Q₁ - (1 - Q₂) := by rw [prF_one h₁, prF_one h₂]
  refine ⟨fun x => prF Q₁ x - (1 - prF Q₂ x), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (prF_smooth h₁.herm h₁.idem).sub (contDiffOn_const.sub (prF_smooth h₂.herm h₂.idem))
  · intro x hx
    simp only [IsHermitian, conjTranspose_sub, conjTranspose_one, (prF_isPr h₁ hx).herm, (prF_isPr h₂ hx).herm]
  · show ((prF Q₁ 1 - (1 - prF Q₂ 1)) * (prF Q₁ 1 - (1 - prF Q₂ 1))).trace ≠ 0
    rw [hH1]
    intro ht
    have hherm : (Q₁ - (1 - Q₂))ᴴ = Q₁ - (1 - Q₂) := by
      simp only [conjTranspose_sub, conjTranspose_one, h₁.herm, h₂.herm]
    have h0 : Q₁ - (1 - Q₂) = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 (by rwa [hherm])
    have h3 : Q₁ = 1 - Q₂ := sub_eq_zero.1 h0
    have h4 : Q₂ * Q₁ = Q₁ := h₁.mul_of_sub h₂ hW
    have h5 : Q₁ = 0 := by
      have h6 : Q₁ * Q₁ = Q₁ - Q₂ * Q₁ := by
        conv_lhs => rw [h3]
        rw [sub_mul, Matrix.one_mul, ← h3]
      rw [h₁.idem, h4, sub_self] at h6
      exact h6
    apply hne
    rw [eq_bot_iff]
    intro v hv
    have := (h₁.mem v).1 hv
    rw [h5, zero_mulVec] at this
    simp [← this]
  · intro x hx k
    have h1 : k.1ᴴ * k.1 = 1 := by
      rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 k.2
    have h2 : k.1 * k.1ᴴ = 1 := by
      rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 k.2
    have hk : k.1 ∈ GLs n := by
      have : k.1.det * k.1ᴴ.det = 1 := by rw [← det_mul, h2, det_one]
      exact left_ne_zero_of_mul_eq_one this
    have hinv : k.1⁻¹ = k.1ᴴ := Matrix.inv_eq_left_inv h1
    have hp : ∀ {Q : Mat n} {U : Set (Fin n → ℂ)}, IsPr Q U → prF Q (x * k.1) = k.1ᴴ * prF Q x * k.1 := fun h =>
      (prF_isPr h (mul_mem_GLs hx hk)).unique (by
        rw [Matrix.mul_inv_rev, hinv, im_mul]
        exact (prF_isPr h hx).unitary h1 h2)
    show prF Q₁ (x * k.1) - (1 - prF Q₂ (x * k.1)) = k.1ᴴ * (prF Q₁ x - (1 - prF Q₂ x)) * k.1
    rw [hp h₁, hp h₂, mul_sub, sub_mul, mul_sub, sub_mul, Matrix.mul_one, h1]
  · intro q hq hq₁ hq₂ x hx
    have hp : ∀ {Q : Mat n} {W : Submodule ℂ (Fin n → ℂ)}, IsPr Q (W : Set (Fin n → ℂ)) →
        W.map (Matrix.mulVecLin q) = W → prF Q (q * x) = prF Q x := fun {Q W} h hm =>
      (prF_isPr h (mul_mem_GLs hq hx)).unique (by
        have hi : im q⁻¹ (W : Set (Fin n → ℂ)) = W := by
          conv_lhs => rw [← im_of_map hm]
          exact im_cancel hq _
        rw [Matrix.mul_inv_rev, im_mul, hi]
        exact prF_isPr h hx)
    show prF Q₁ (q * x) - (1 - prF Q₂ (q * x)) = prF Q₁ x - (1 - prF Q₂ x)
    rw [hp h₁ hq₁, hp h₂ hq₂]
  · intro d hd hd₁ hd₂
    have e₁ : prF Q₁ d = 1 - Q₂ :=
      (prF_isPr h₁ hd).unique (by
        have : im d⁻¹ (W₁ : Set (Fin n → ℂ)) = perp W₂ := by
          rw [← hd₁]; exact im_cancel hd _
        rw [this]; exact h₂.perp)
    have e₂ : prF Q₂ d = 1 - Q₁ :=
      (prF_isPr h₂ hd).unique (by
        have : im d⁻¹ (W₂ : Set (Fin n → ℂ)) = perp W₁ := by
          rw [← hd₂]; exact im_cancel hd _
        rw [this]; exact h₁.perp)
    show prF Q₁ d - (1 - prF Q₂ d) = -(prF Q₁ 1 - (1 - prF Q₂ 1))
    rw [hH1, e₁, e₂]
    abel

end GlobalTheory.CompanionTheory.FlagHerm
