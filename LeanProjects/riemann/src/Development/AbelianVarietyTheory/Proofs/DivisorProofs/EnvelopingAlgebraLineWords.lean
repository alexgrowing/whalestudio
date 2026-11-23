import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin.WordSpan

variable {n : ℕ} {G : Type} [Group G]

theorem map_one_of_isMulOn {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) : s 1 = 1 := by
  have h1 : IsUni J (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [IsUni]
  have h := hs 1 1 h1 h1
  rw [mul_one] at h
  exact mul_left_cancel (a := s 1) (by rw [mul_one]; exact h.symm)

theorem lineOf_zero {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) (Z : Matrix (Fin n) (Fin n) ℂ) : lineOf s Z 0 = 1 := by
  simp [lineOf, map_one_of_isMulOn hs]

theorem rho_skew_apply {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)}
    (hρ : IsRightDer J s ρ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (f : smLoc J s) :
    (ρ Z f).1 = rder (lineOf s Z) f.1 := by
  funext g
  have h := hρ Z hZ f g 0
  rw [lineOf_zero hs, mul_one] at h
  exact h.deriv.symm

theorem prod_apply {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G}
    (hs : IsMulOn J s) {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)}
    (hρ : IsRightDer J s ρ) (L : List (Matrix (Fin n) (Fin n) ℂ)) (hL : ∀ Z ∈ L, IsSkew J Z)
    (f : smLoc J s) : ((L.map ρ).prod f).1 = (L.map (lineOf s)).foldr rder f.1 := by
  induction L with
  | nil => simp
  | cons Z L ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, Module.End.mul_apply]
    rw [rho_skew_apply hs hρ (hL Z (by simp)), ih (fun Y hY => hL Y (by simp [hY]))]

theorem skew_decomp {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ Z₁ Z₂, IsSkew J Z₁ ∧ IsSkew J Z₂ ∧ Y = Z₁ + Complex.I • Z₂ := by
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hdet
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hdet
  set Ys := J⁻¹ * Yᴴ * J with hYs
  have hYsH : Ysᴴ * J = J * Y := by
    rw [hYs, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ,
      conjTranspose_nonsing_inv, hJ, Matrix.mul_assoc, Matrix.mul_assoc, hJiJ, Matrix.mul_one]
  have hJYs : J * Ys = Yᴴ * J := by
    rw [hYs, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  refine ⟨(1 / 2 : ℂ) • (Y - Ys), (1 / (2 * Complex.I)) • (Y + Ys), ?_, ?_, ?_⟩
  · simp only [IsSkew, conjTranspose_smul, conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, hYsH, hJYs]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]; simp
  · simp only [IsSkew, conjTranspose_smul, conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, hYsH, hJYs]
    have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.ext_iff]
    rw [this, neg_smul, add_comm (J * Y), neg_add_cancel]
  · rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
    module

end GlobalTheory.TorFin.WordSpan

namespace GlobalTheory.TorFin.WordSpan

variable {n : ℕ} {G : Type} [Group G]

theorem wop_single (l : List (ℝ → G)) (f : G → ℂ) : wop (Finsupp.single l 1) f = l.foldr rder f := by
  funext g; simp [wop, Finsupp.sum_single_index]

theorem wop_zero (f : G → ℂ) : wop (0 : List (ℝ → G) →₀ ℂ) f = 0 := by
  funext g; simp [wop]

theorem wop_add (z z' : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : wop (z + z') f = wop z f + wop z' f := by
  funext g
  simp only [wop, Pi.add_apply]
  rw [Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

theorem wop_smul (c : ℂ) (z : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : wop (c • z) f = c • wop z f := by
  funext g
  simp only [wop, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), Finsupp.mul_sum]
  simp [smul_eq_mul, mul_assoc]

def words (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G)
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) : Set (Module.End ℂ (smLoc J s)) :=
  {T | ∃ L : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ L, IsSkew J Z) ∧ T = (L.map ρ).prod}

theorem adjoin_le_span {J : Matrix (Fin n) (Fin n) ℂ} (hJ : Jᴴ = J) (hdet : IsUnit J.det)
    {s : Matrix (Fin n) (Fin n) ℂ → G} (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) :
    ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), T ∈ Submodule.span ℂ (words J s ρ) := by
  have hone : (1 : Module.End ℂ (smLoc J s)) ∈ Submodule.span ℂ (words J s ρ) :=
    Submodule.subset_span ⟨[], by simp, by simp⟩
  have hmul : ∀ x y, x ∈ Submodule.span ℂ (words J s ρ) → y ∈ Submodule.span ℂ (words J s ρ) →
      x * y ∈ Submodule.span ℂ (words J s ρ) := by
    intro x y hx hy
    have hxy := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine Submodule.span_le.mpr ?_ hxy
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨L', hL', rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨L ++ L', ?_, by simp [List.prod_append]⟩
    intro Z hZ
    rcases List.mem_append.mp hZ with h | h
    · exact hL Z h
    · exact hL' Z h
  let S : Subalgebra ℂ (Module.End ℂ (smLoc J s)) :=
    (Submodule.span ℂ (words J s ρ)).toSubalgebra hone hmul
  have hle : Algebra.adjoin ℂ (Set.range ρ) ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨Y, rfl⟩
    obtain ⟨Z₁, Z₂, h₁, h₂, rfl⟩ := skew_decomp hJ hdet Y
    show ρ (Z₁ + Complex.I • Z₂) ∈ Submodule.span ℂ (words J s ρ)
    rw [map_add, map_smul]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨[Z₁], by simpa using h₁, by simp⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨[Z₂], by simpa using h₂, by simp⟩))
  intro T hT
  exact hle hT

theorem exists_wop_of_mem_adjoin : ∀ (n : ℕ) (G : Type) [Group G] (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G), Jᴴ = J → IsUnit J.det → IsMulOn J s → ∀ ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s), IsRightDer J s ρ → ∀ T ∈ Algebra.adjoin ℂ (Set.range ρ), ∃ z : List (ℝ → G) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, ∃ Z, IsSkew J Z ∧ γ = lineOf s Z) ∧ ∀ f : smLoc J s, (T f).1 = wop z f.1 := by
  intro n G _ J s hJ hdet hs ρ hρ T hT
  classical
  have hS := adjoin_le_span hJ hdet ρ T hT
  clear hT
  induction hS using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨L, hL, rfl⟩ := hx
    refine ⟨Finsupp.single (L.map (lineOf s)) 1, ?_, ?_⟩
    · intro l hl γ hγ
      have hl' : l = L.map (lineOf s) := by
        by_contra hne
        simp [Finsupp.single_apply, Ne.symm hne] at hl
        exact hne hl
      subst hl'
      obtain ⟨Z, hZ, rfl⟩ := List.mem_map.mp hγ
      exact ⟨Z, hL Z hZ, rfl⟩
    · intro f
      rw [prod_apply hs hρ L hL f, wop_single]
  | zero =>
    exact ⟨0, by simp, fun f => by rw [wop_zero]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, hzf⟩ := hx
    obtain ⟨z', hz', hzf'⟩ := hy
    refine ⟨z + z', ?_, ?_⟩
    · intro l hl
      rcases Finset.mem_union.mp (Finsupp.support_add hl) with h | h
      · exact hz l h
      · exact hz' l h
    · intro f
      rw [wop_add, ← hzf, ← hzf']
      rfl
  | smul c x _ hx =>
    obtain ⟨z, hz, hzf⟩ := hx
    refine ⟨c • z, fun l hl => hz l (Finsupp.support_smul hl), ?_⟩
    intro f
    rw [wop_smul, ← hzf]
    rfl

end GlobalTheory.TorFin.WordSpan
