import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeUnipRad
open Matrix NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RealUnipFrame

variable {n ρ : ℕ}

theorem mem_span_image_iff (g : Fin ρ → Fin n → ℂ) (S : Set (Fin ρ)) (w : Fin n → ℂ) :
    w ∈ Submodule.span ℂ (g '' S) ↔ ∃ t : Fin ρ → ℂ, (∀ b, b ∉ S → t b = 0) ∧ ∑ b, t b • g b = w := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 h
    refine ⟨l, fun b hb => ?_, ?_⟩
    · by_contra h0
      exact hb (hl (Finsupp.mem_support_iff.2 h0))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨t, ht, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [ht b hb, zero_smul]; exact Submodule.zero_mem _

theorem mem_span_image_mulVec (Q P : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (g : Fin ρ → Fin n → ℂ)
    (S : Set (Fin ρ)) (w : Fin n → ℂ) :
    Q *ᵥ w ∈ Submodule.span ℂ ((fun b => Q *ᵥ g b) '' S) ↔ w ∈ Submodule.span ℂ (g '' S) := by
  rw [mem_span_image_iff, mem_span_image_iff]
  have hinj : ∀ u u' : Fin n → ℂ, Q *ᵥ u = Q *ᵥ u' → u = u' := by
    intro u u' h
    have := congrArg (P *ᵥ ·) h
    simpa only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec] using this
  have hsum : ∀ t : Fin ρ → ℂ, ∑ b, t b • Q *ᵥ g b = Q *ᵥ ∑ b, t b • g b := by
    intro t
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  refine exists_congr fun t => and_congr Iff.rfl ?_
  rw [hsum]
  exact ⟨hinj _ _, fun h => by rw [h]⟩

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

variable {n ρ : ℕ}

theorem cols_iff (f : Fin ρ → Fin n → ℂ) (d : Fin ρ → ℂ) (hd : ∀ a, d a ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ) :
    (∃ T : Matrix (Fin ρ) (Fin ρ) ℂ, GlobalTheory.BesselChar.StrictUp T ∧
      N * Matrix.of (fun k a => d a * f a k) = Matrix.of (fun k a => d a * f a k) + Matrix.of (fun k a => d a * f a k) * T) ↔
    ∀ i : Fin ρ, (N - 1) *ᵥ f i ∈ Submodule.span ℂ (f '' {b | b.1 < i.1}) := by
  have e1 : ∀ i k, d i * (N *ᵥ f i) k = ∑ j, N k j * (d i * f i j) := by
    intro i k
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · rintro ⟨T, hT, h⟩ i
    rw [mem_span_image_iff]
    refine ⟨fun j => d j * T j i / d i, fun j hj => ?_, ?_⟩
    · have : i ≤ j := by
        simp only [Set.mem_setOf_eq, not_lt] at hj
        exact Fin.le_def.2 hj
      show d j * T j i / d i = 0
      rw [hT j i this]; simp
    · funext k
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply] at hk
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      have hdi := hd i
      have key : d i * (N *ᵥ f i) k = d i * f i k + ∑ j, d j * T j i * f j k := by
        have e2 : ∑ j, d j * T j i * f j k = ∑ j, d j * f j k * T j i :=
          Finset.sum_congr rfl fun j _ => by ring
        rw [e1, hk, e2]
      have e4 : ∑ x, d x * T x i / d i * f x k = (∑ j, d j * T j i * f j k) / d i := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e4, div_eq_iff hdi]
      linear_combination -key
  · intro h
    choose t ht hts using fun i => (mem_span_image_iff f _ _).1 (h i)
    refine ⟨Matrix.of fun j i => d i * t i j / d j, fun j i hij => ?_, ?_⟩
    · have : ¬ j.1 < i.1 := by rw [Fin.le_def] at hij; omega
      simp [ht i j (by simpa using this)]
    · ext k i
      have hk := congrFun (hts i) k
      rw [Finset.sum_apply] at hk
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply] at hk
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply]
      have e3 : ∑ j, d j * f j k * (d i * t i j / d j) = d i * ∑ j, t i j * f j k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := hd j
        field_simp
      rw [← e1, e3, hk]
      ring

theorem colspan_iff (f : Fin ρ → Fin n → ℂ) (d : Fin ρ → ℂ) (hd : ∀ a, d a ≠ 0) (N : Matrix (Fin n) (Fin n) ℂ)
    (y : Fin n → ℂ) :
    (∃ a, N *ᵥ y = y + Matrix.of (fun k a => d a * f a k) *ᵥ a) ↔
      (N - 1) *ᵥ y ∈ Submodule.span ℂ (f '' {b | b.1 < ρ}) := by
  have hE : ∀ a : Fin ρ → ℂ, Matrix.of (fun k a => d a * f a k) *ᵥ a = ∑ b, (a b * d b) • f b := by
    intro a; funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [mem_span_image_iff, Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨fun b => a b * d b, fun b hb => absurd b.2 (by simpa using hb), ?_⟩
    rw [← hE, ha, add_sub_cancel_left]
  · rintro ⟨t, -, ht⟩
    refine ⟨fun b => t b / d b, ?_⟩
    rw [hE]
    have : ∀ b, t b / d b * d b = t b := fun b => div_mul_cancel₀ _ (hd b)
    simp only [this, ht, add_sub_cancel]

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

open Formalism.L2.SG.HidaSetting

variable {n ρ : ℕ}

theorem conj_sub_mulVec (Q P N : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (w : Fin n → ℂ) :
    (Q * N * P - 1) *ᵥ (Q *ᵥ w) = Q *ᵥ ((N - 1) *ᵥ w) := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hPQ, Matrix.mul_one]

theorem hJ_frame (ε : Fin n → Bool) (P Q Jc : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1)
    (hspec : Pᴴ * Jc * P = Formalism.REAL.Jm ε) (f y : Fin n → ℂ) :
    hJ ε (Q *ᵥ f) (Q *ᵥ y) = star f ⬝ᵥ (Jc *ᵥ y) := by
  unfold hJ
  rw [← hspec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hPQ, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, hPQ,
    Matrix.conjTranspose_one, Matrix.one_mulVec]

theorem emb_hform (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x z : Fin I.n → I.E) :
    I.φ v (Formalism.UG.hform (starRingEnd I.E) I.J x z) =
      star (fun i => I.φ v (x i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (z i)) := by
  rw [← Formalism.MainNotions.BridgeUnipRad.hform_eq]
  simp only [Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, starRingEnd_apply,
    Formalism.MainNotions.BridgeUnipRad.emb_star]

theorem perp_mulVec (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (y : Fin I.n → ℂ) :
    (Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v) *ᵥ y =
      fun a => starRingEnd ℂ (I.φ v (c a)) * (star (fun i => I.φ v (x a i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ y)) := by
  funext a
  rw [Matrix.map_mul]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, map_mul, starRingEnd_apply, Formalism.MainNotions.BridgeUnipRad.emb_star,
    Pi.star_apply, star_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.RealUnipFrame

namespace GlobalTheory.RealUnipFrame

open Formalism.L2.SG.HidaSetting

theorem unip_iff_inN : ∀ (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E)
    (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) →
    ∀ (N : Matrix (Fin I.n) (Fin I.n) ℂ), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v))
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔
      Formalism.L2.SG.HidaSetting.InN (I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv I v (x a)) (Formalism.L2.SG.HidaSetting.rv I v z)
        ((I.P v)⁻¹ * N * I.P v) := by
  intro I v ρ x c z hc hz N
  have hu : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hQP : (I.P v)⁻¹ * I.P v = 1 := Matrix.nonsing_inv_mul _ hu
  set f : Fin ρ → Fin I.n → ℂ := fun a k => I.φ v (x a k) with hf
  set d : Fin ρ → ℂ := fun a => I.φ v (c a) with hdd
  have hd : ∀ a, d a ≠ 0 := fun a => (map_ne_zero (I.φ v)).2 (hc a)
  have hE : (Matrix.of fun k a => c a * x a k).map (I.φ v) = Matrix.of fun k a => d a * f a k := by
    ext k a; simp [hf, hdd]
  have hrv : ∀ w : Fin I.n → I.E, rv I v w = (I.P v)⁻¹ *ᵥ fun i => I.φ v (w i) := fun _ => rfl
  have hrx : (fun a => rv I v (x a)) = fun b => (I.P v)⁻¹ *ᵥ f b := rfl
  have hspan : ∀ (w : Fin I.n → ℂ) (S : Set (Fin ρ)),
      ((I.P v)⁻¹ * N * I.P v - 1) *ᵥ ((I.P v)⁻¹ *ᵥ w) ∈ Submodule.span ℂ ((fun a => rv I v (x a)) '' S) ↔
        (N - 1) *ᵥ w ∈ Submodule.span ℂ (f '' S) := by
    intro w S
    rw [conj_sub_mulVec _ _ _ hPQ, hrx]
    exact mem_span_image_mulVec _ _ hPQ f S _
  have hperp : ∀ y : Fin I.n → ℂ,
      ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) *ᵥ y = 0 ↔
        ∀ a, hJ (I.ε v) (rv I v (x a)) ((I.P v)⁻¹ *ᵥ y) = 0 := by
    intro y
    rw [perp_mulVec]
    simp only [hrv, hJ_frame (I.ε v) (I.P v) _ (I.J.map (I.φ v)) hPQ (I.P_spec v)]
    constructor
    · intro h a
      have := congrFun h a
      exact (mul_eq_zero.1 this).resolve_left ((map_ne_zero _).2 (hd a))
    · intro h
      funext a
      simp [h a]
  unfold GlobalTheory.BesselChar.Unip InN InS spanLt
  rw [hE, cols_iff f d hd N]
  have hB : (∀ y, ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) *ᵥ y = 0 →
        ∃ a, N *ᵥ y = y + (Matrix.of fun k a => d a * f a k) *ᵥ a) ↔
      ∀ y, (∀ a, hJ (I.ε v) (rv I v (x a)) y = 0) →
        ((I.P v)⁻¹ * N * I.P v - 1) *ᵥ y ∈ Submodule.span ℂ ((fun a => rv I v (x a)) '' {b | b.1 < ρ}) := by
    constructor
    · intro h y' hy'
      have hy : y' = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ y') := by rw [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
      rw [hy] at hy' ⊢
      rw [hspan, ← colspan_iff f d hd]
      exact h _ ((hperp _).2 hy')
    · intro h y hy
      rw [colspan_iff f d hd, ← hspan]
      exact h _ ((hperp y).1 hy)
  rw [hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun a => (hspan (f a) _).2 (h1 a), ?_⟩, h2⟩
    refine h2 _ fun a => ?_
    rw [hrv, hrv, hJ_frame (I.ε v) (I.P v) _ (I.J.map (I.φ v)) hPQ (I.P_spec v), ← emb_hform, hz a, map_zero]
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨fun a => (hspan (f a) _).1 (h1 a), h2⟩

end GlobalTheory.RealUnipFrame
