import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.OmDec

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_sub_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g)
    (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f - h) g v = fderiv ℝ f g v - fderiv ℝ h g v := by
  rw [fderiv_sub hf hh]; rfl

theorem fderiv_zero_apply' (g v : E) : fderiv ℝ (0 : E → F) g v = 0 := by
  have h : fderiv ℝ (0 : E → F) g = 0 := by
    simpa using (fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : F))
  rw [h]; rfl

end General

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_left (A B : Mat n) (h : Mat n → V) : Rd (A - B) h = Rd A h - Rd B h := by
  funext g; simp [Rd, mul_sub]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  exact fderiv_zero_apply' _ _

theorem Rd_add_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a + b) g = Rd X a g + Rd X b g :=
  RCalc.fderiv_add_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_sub_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a - b) g = Rd X a g - Rd X b g :=
  fderiv_sub_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_smul_right (c : ℂ) (X : Mat n) {a : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (c • a) g = c • Rd X a g :=
  RCalc.fderiv_csmul_apply (RCalc.differentiableAt_of_smooth ha hg) c _

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  show ∑ d, Eu s c d (Epow s 0 d a f) = _
  rw [Finset.sum_eq_single a]
  · simp [Epow]
  · intro d _ hd
    simp [Epow, hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) :
    gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  show ∑ c, Eu s a c (Epow s 1 c a f) = _
  simp only [Epow_one]

theorem Eu_Eu_apply (s : Bool) (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) (ε : ℂ)
    (hε : ε = if s then -Complex.I else Complex.I) :
    Eu s a b (Eu s c d f) g = (1 / 4 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        + ε • Rd (Matrix.single a b 1) (Rd (Matrix.single c d Complex.I) f) g
        + ε • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d 1) f) g
        + (ε * ε) • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  have hX := RCalc.Rd_contDiffOn (Matrix.single c d (1 : ℂ)) hf
  have hY := RCalc.Rd_contDiffOn (Matrix.single c d Complex.I) hf
  have hS : ContDiffOn ℝ ∞ (ε • Rd (Matrix.single c d Complex.I) f) (GLs n) := hY.const_smul ε
  have key : ∀ Z : Mat n, Rd Z (Eu s c d f) g =
      (1 / 2 : ℂ) • (Rd Z (Rd (Matrix.single c d 1) f) g
        + ε • Rd Z (Rd (Matrix.single c d Complex.I) f) g) := by
    intro Z
    have e : Eu s c d f = (1 / 2 : ℂ) • (Rd (Matrix.single c d 1) f
        + ε • Rd (Matrix.single c d Complex.I) f) := by
      rw [hε]; rfl
    have hA : ContDiffOn ℝ ∞ (Rd (Matrix.single c d 1) f + ε • Rd (Matrix.single c d Complex.I) f)
        (GLs n) := hX.add hS
    rw [e, Rd_smul_right _ _ hA hg, Rd_add_right _ hX hS hg, Rd_smul_right _ _ hY hg]
  have e2 : Eu s a b (Eu s c d f) g = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) (Eu s c d f) g
      + ε • Rd (Matrix.single a b Complex.I) (Eu s c d f) g) := by
    rw [hε]; rfl
  rw [e2, key, key]
  module

theorem Eu_pair_apply (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Eu true a b (Eu true c d f) g + Eu false a b (Eu false c d f) g = (1 / 2 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  rw [Eu_Eu_apply true a b c d hf hg (-Complex.I) (by simp),
    Eu_Eu_apply false a b c d hf hg Complex.I (by simp)]
  have h1 : (-Complex.I) * (-Complex.I) = -1 := by simp
  have h2 : Complex.I * Complex.I = -1 := by simp
  rw [h1, h2]
  module

theorem Om_apply {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om f g = ∑ a, ∑ b, (Rd (Matrix.single a b 1) (Rd (Matrix.single b a 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single b a Complex.I) f) g) := by
  have h : Om f g = (2 : ℂ) • ∑ a, ∑ b,
      (Eu true a b (Eu true b a f) g + Eu false a b (Eu false b a f) g) := by
    simp only [Om, gel_two, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib]
  rw [h]
  simp only [Eu_pair_apply _ _ _ _ hf hg, Finset.smul_sum, smul_smul]
  norm_num

theorem Rd_sq_add (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A + B) (Rd (A + B) f) g =
      Rd A (Rd A f) g + Rd A (Rd B f) g + Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [RCalc.Rd_add_left A B f, RCalc.Rd_add_left A B (Rd A f + Rd B f)]
  simp only [Pi.add_apply]
  rw [Rd_add_right _ dA dB hg, Rd_add_right _ dA dB hg]
  abel

theorem Rd_sq_sub (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A - B) (Rd (A - B) f) g =
      Rd A (Rd A f) g - Rd A (Rd B f) g - Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [Rd_sub_left A B f, Rd_sub_left A B (Rd A f - Rd B f)]
  simp only [Pi.sub_apply]
  rw [Rd_sub_right _ dA dB hg, Rd_sub_right _ dA dB hg]
  abel

theorem sum_Ix (F : Ix n → V) :
    ∑ p, F p = ∑ a, ∑ b, (F (true, a, b) + F (false, a, b)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]

theorem sum_reindex (x y : Fin n → Fin n → V) :
    ∑ a, ∑ b, (x a b - y a b) = (1 / 4 : ℂ) • ∑ a, ∑ b,
      ((2 : ℂ) • (x a b + x b a) - (2 : ℂ) • (y a b + y b a)) := by
  have hx : ∑ a, ∑ b, x b a = ∑ a, ∑ b, x a b := Finset.sum_comm
  have hy : ∑ a, ∑ b, y b a = ∑ a, ∑ b, y a b := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hx, hy]
  module

theorem Om_eq_squares {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) :
    ContDiffOn ℝ ∞ f (GLs n) → ∀ g ∈ GLs n,
      Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g
        - (1 / 4 : ℂ) • ∑ p : Ix n, Rd (sk p) (Rd (sk p) f) g := by
  intro hf g hg
  rw [Om_apply hf hg, sum_reindex, sum_Ix, sum_Ix, ← smul_sub]
  congr 1
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e1 : hm (n := n) (true, a, b) = Matrix.single a b 1 + Matrix.single b a 1 := by simp [hm]
  have e2 : hm (n := n) (false, a, b) =
      Matrix.single a b Complex.I - Matrix.single b a Complex.I := by simp [hm]
  have e3 : sk (n := n) (true, a, b) = Matrix.single a b 1 - Matrix.single b a 1 := by simp [sk]
  have e4 : sk (n := n) (false, a, b) =
      Matrix.single a b Complex.I + Matrix.single b a Complex.I := by simp [sk]
  rw [e1, e2, e3, e4, Rd_sq_add _ _ hf hg, Rd_sq_sub _ _ hf hg, Rd_sq_add _ _ hf hg,
    Rd_sq_sub _ _ hf hg]
  module

end GlobalTheory.CompanionTheory.WaveSpd.OmDec
