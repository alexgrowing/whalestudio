import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.Qk

section Per
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}

theorem cv_add (M Nn : Fin g → ℤ) : cv (M + Nn) = cv M + cv Nn := by funext i; simp [cv]
theorem cv_sub (M Nn : Fin g → ℤ) : cv (M - Nn) = cv M - cv Nn := by funext i; simp [cv]
theorem cv_nsmul (k : ℕ) (M : Fin g → ℤ) : cv ((k : ℤ) • M) = k • cv M := by funext i; simp [cv]

theorem perV_add (M Nn M' Nn' : Fin g → ℤ) : perV τ (M + M') (Nn + Nn') = perV τ M Nn + perV τ M' Nn' := by
  simp only [perV, cv_add, mulVec_add]; abel

theorem perV_sub (M Nn M' Nn' : Fin g → ℤ) : perV τ (M - M') (Nn - Nn') = perV τ M Nn - perV τ M' Nn' := by
  simp only [perV, cv_sub, mulVec_sub]; abel

theorem perV_nsmul (k : ℕ) (M Nn : Fin g → ℤ) : perV τ ((k : ℤ) • M) ((k : ℤ) • Nn) = k • perV τ M Nn := by
  simp only [perV, cv_nsmul, mulVec_smul, smul_add]

theorem perV_eq_zero (hp : (τ.map Complex.im).PosDef) {M Nn : Fin g → ℤ} (h : perV τ M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have hN : Nn = 0 := by
    by_contra hne
    have hx : (fun i => (Nn i : ℝ)) ≠ 0 := fun e => hne (funext fun i => by simpa using congrFun e i)
    have h1 := hp.dotProduct_mulVec_pos hx
    have h2 : (τ.map Complex.im) *ᵥ (fun i => (Nn i : ℝ)) = 0 := by
      funext i
      have := congrArg Complex.im (congrFun h i)
      simpa [perV, cv, mulVec, dotProduct, Complex.im_sum] using this
    rw [h2] at h1
    simp at h1
  subst hN
  refine ⟨funext fun i => ?_, rfl⟩
  have := congrFun h i
  simpa [perV, cv, mulVec, dotProduct] using this

end Per

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X}

theorem eq_zero_of_perV_full (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r) {M Nn : Fin g → ℤ} (h0 : tP σ Nn = 0)
    (h : perV (d.full σ 0) M Nn = 0) : M = 0 ∧ Nn = 0 := by
  have h1 : perV d.τ (zP σ M) (zP σ Nn) = 0 := by
    have := congrArg (zP σ) h
    rw [Exp.leftComponent_periodVector, h0, Exp.cv_zero, mulVec_zero, add_zero] at this
    exact this
  obtain ⟨a, b⟩ := perV_eq_zero d.pos h1
  have h2 : tP σ M = 0 := by
    have := congrArg (tP σ) h
    rw [Exp.secondBlock_periodVector, h0, b, Exp.cv_zero, Exp.cv_zero, mulVec_zero, mulVec_zero, add_zero, add_zero] at this
    funext l
    have := congrFun this l
    simpa [cv, tP] using this
  exact ⟨Exp.ext_zP_tP σ a h2, Exp.ext_zP_tP σ b h0⟩

def yv (bX : Module.Basis (Fin r) ℤ N.X) (σ : Fin g ≃ Fin g' ⊕ Fin r) (Nn : Fin g → ℤ) : N.X := ∑ l, tP σ Nn l • bX l

theorem yv_add (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a + b) = yv bX σ a + yv bX σ b := by
  simp [yv, tP, add_smul, Finset.sum_add_distrib]

theorem yv_sub (σ : Fin g ≃ Fin g' ⊕ Fin r) (a b : Fin g → ℤ) : yv bX σ (a - b) = yv bX σ a - yv bX σ b := by
  simp [yv, tP, sub_smul, Finset.sum_sub_distrib]

theorem yv_nsmul (σ : Fin g ≃ Fin g' ⊕ Fin r) (k : ℕ) (a : Fin g → ℤ) : yv bX σ ((k : ℤ) • a) = k • yv bX σ a := by
  simp [yv, tP, Finset.smul_sum, mul_smul]

theorem yv_of_tP (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : tP σ a = 0) : yv bX σ a = 0 := by
  simp [yv, h]

theorem tP_of_yv (σ : Fin g ≃ Fin g' ⊕ Fin r) {a : Fin g → ℤ} (h : yv bX σ a = 0) : tP σ a = 0 := by
  have := Exp.co_sum (bX := bX) (tP σ a)
  change co bX (yv bX σ a) = _ at this
  rw [h] at this
  funext l
  have := congrFun this l
  simpa [co, cv] using this.symm

theorem yv_surj (σ : Fin g ≃ Fin g' ⊕ Fin r) (z : N.X) : ∃ a, yv bX σ a = z :=
  ⟨Exp.asm σ 0 (bX.repr z), by rw [yv, Exp.secondBlock_assemble]; exact bX.sum_repr z⟩

end GlobalTheory.MBLow.Cl.Qk

namespace GlobalTheory.MBLow.Cl
open Qk

theorem torsion_eq_periods_mod : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → (∀ p, ∃ M Nn, d.Rep σ k M Nn p) ∧ (∀ M Nn, ∃! p, d.Rep σ k M Nn p) ∧ (∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → d.Rep σ k (M + M') (Nn + Nn') (p * p')) ∧ ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p → d.Rep σ k M' Nn' p' → (N.QEq p p' ↔ ∃ M₁ N₁, M' = M + (k : ℤ) • M₁ ∧ Nn' = Nn + (k : ℤ) • N₁) := by
  intro N g' r g bX d σ k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := exp_onto_torusExt N g' r g bX d σ
  choose E hE hU using h1
  have hiff : ∀ v h, d.IsPt σ v h ↔ h = E v := fun v h => ⟨hU v h, fun e => e ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ M Nn, E (perV (d.full σ 0) M Nn) = N.io (yv bX σ Nn) := fun M Nn => (hU _ _ (h5 M Nn)).symm
  have hker : ∀ v v', E v = E v' → ∃ M Nn, tP σ Nn = 0 ∧ v = v' + perV (d.full σ 0) M Nn := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨M, Nn, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨M, Nn, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : Fin g → ℂ, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : Fin g → ℂ, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ M Nn (p : N.QT k), d.Rep σ k M Nn p ↔
      p.1.1.toAdd = yv bX σ Nn ∧ p.1.2 = E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn) :=
    fun M Nn p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun M Nn => ?_, fun M Nn M' Nn' p p' h h' => ?_, fun M Nn M' Nn' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    obtain ⟨a, ha⟩ := yv_surj (bX := bX) σ p.1.1.toAdd
    have e : E (k • v) = E (perV (d.full σ 0) 0 a) := by
      rw [hpow, hper, ← hv', ha]
      exact N.mem_QT.1 p.2
    obtain ⟨M, Nn, hy, hl⟩ := hker _ _ e
    refine ⟨0 + M, a + Nn, (hrep _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [yv_add, yv_of_tP σ hy, add_zero, ha]
    · rw [perV_add, ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (yv bX σ Nn), E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)), ?_⟩,
      (hrep _ _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    refine (hrep _ _ _).2 ⟨?_, ?_⟩
    · rw [yv_add, ← a, ← a']
      rfl
    · rw [perV_add, smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      obtain ⟨z₀, hz⟩ := yv_surj (bX := bX) σ z
      have e : E ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') =
          E ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn + perV (d.full σ 0) 0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨M₀, N₀, hy, hl⟩ := hker _ _ e
      have key := eq_zero_of_perV_full d σ (M := M' - (M + (k : ℤ) • (0 + M₀)))
        (Nn := Nn' - (Nn + (k : ℤ) • (z₀ + N₀))) ?_ ?_
      · exact ⟨0 + M₀, z₀ + N₀, sub_eq_zero.1 key.1, sub_eq_zero.1 key.2⟩
      · apply tP_of_yv (bX := bX)
        rw [yv_sub, yv_add, yv_nsmul, yv_add, yv_of_tP σ hy, add_zero, hz, ← a, ← a', c, sub_self]
      · rw [perV_sub, perV_add, perV_nsmul, perV_add, ← hc2 (perV (d.full σ 0) M' Nn'), hl, add_assoc, smul_add, hc2,
          sub_self]
    · rintro ⟨M₁, N₁, rfl, rfl⟩
      refine ⟨yv bX σ N₁, ?_, ?_⟩
      · rw [a, a', yv_add, yv_nsmul]
      · rw [b, b', perV_add, perV_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.MBLow.Cl
end
