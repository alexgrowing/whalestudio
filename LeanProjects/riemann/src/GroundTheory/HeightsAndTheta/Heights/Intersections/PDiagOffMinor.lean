import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagOffPair
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalOffMinor

variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

def lineSubst (ι ν κ : Type) : (Σ b, T.wwIdx ι ν κ b) → Polynomial (MRing (T.wwIdx ι ν κ))
  | ⟨.base, i⟩ => Polynomial.C (X ⟨.base, i⟩)
  | ⟨.det, l⟩ => Polynomial.C (X ⟨.det, l⟩)
  | ⟨.line0, p⟩ => Polynomial.C (X ⟨.line0, p⟩)
  | ⟨.line1, p⟩ => Polynomial.C (X ⟨.line0, p⟩) * Polynomial.X

def blockSubst : T.WBlk → Polynomial (MvPolynomial T.WBlk Φ)
  | .line1 => Polynomial.C (X .line0) * Polynomial.X
  | b => Polynomial.C (X b)

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem map_comp_subst (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    (Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁))).comp
        (eval₂Hom (Int.castRingHom _) (lineSubst ι ν κ)) =
      (eval₂Hom (Polynomial.C.comp C) (blockSubst (Φ := Φ))).comp
        (T.multiConeMap (T.wwCoord x δ e φ a₀ a₀)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [T.multiConeMap]
  · rintro ⟨b, q⟩
    cases b <;> simp [T.multiConeMap, T.wwCoord, lineSubst, blockSubst]
    ring

omit [Fintype ι] [Fintype ν] [Fintype κ] in

theorem diag_le_of_prop (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) (W : Ideal (MRing (T.wwIdx ι ν κ))) [W.IsPrime] (hW : T.wwIdeal x δ e φ a₀ a₁ ≤ W) (m : κ)
    (hm : (X ⟨.line0, m⟩ : MRing (T.wwIdx ι ν κ)) ∉ W)
    (hprop : ∀ q : κ, (X ⟨.line0, m⟩ * X ⟨.line1, q⟩ - X ⟨.line1, m⟩ * X ⟨.line0, q⟩ :
      MRing (T.wwIdx ι ν κ)) ∈ W) :
    T.wwIdeal x δ e φ a₀ a₀ ≤ W := by
  classical
  let K := FractionRing (MRing (T.wwIdx ι ν κ) ⧸ W)
  let π : MRing (T.wwIdx ι ν κ) →+* K := (algebraMap _ K).comp (Ideal.Quotient.mk W)
  have hπ : ∀ g, π g = 0 ↔ g ∈ W := fun g => by
    simp only [π, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  let σ := eval₂Hom (Int.castRingHom (Polynomial (MRing (T.wwIdx ι ν κ)))) (lineSubst ι ν κ)
  have hm' : π (X ⟨.line0, m⟩) ≠ 0 := fun h => hm ((hπ _).1 h)
  have hσ : (Polynomial.eval₂RingHom π (π (X ⟨.line1, m⟩) / π (X ⟨.line0, m⟩))).comp σ = π := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [σ]
    · rintro ⟨b, q⟩
      cases b
      · simp [σ, lineSubst]
      · simp [σ, lineSubst]
      · simp [σ, lineSubst]
      · have h := (hπ _).2 (hprop q)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
        simp only [σ, RingHom.comp_apply, eval₂Hom_X', lineSubst, Polynomial.coe_eval₂RingHom,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [mul_div_assoc', div_eq_iff hm']
        linear_combination -h
  intro g hg
  rw [T.wwIdeal, RingHom.mem_ker] at hg
  have h1 : Polynomial.mapRingHom (T.multiConeMap (T.wwCoord x δ e φ a₀ a₁)) (σ g) = 0 := by
    rw [← RingHom.comp_apply, map_comp_subst, RingHom.comp_apply, hg, map_zero]
  have h2 : (σ g).map π = 0 := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, hπ]
    refine hW ?_
    rw [T.wwIdeal, RingHom.mem_ker]
    have := congrArg (fun f => Polynomial.coeff f n) h1
    simpa [Polynomial.coeff_map] using this
  rw [← hπ, ← hσ, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_eval_map, h2,
    Polynomial.eval_zero]

theorem frame_rel (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (B : ChartBundle ℤ x 2 E) (hsec : T.IsTwistedDualSec B φ) (hdet : T.IsTwistedDetGen B e δ) (a₀ a₁ : Φ)
    (i : ι) (hi : x i ≠ 0) (l : ν) (k k' : κ) (N : ℕ) (F : MRing (T.wwIdx ι ν κ))
    (hF : IsMultiHomog F (T.wwDeg (N + 3) 0))
    (hFv : aeval (T.wwCoord x δ e φ a₀ a₁) F = algebraMap Ω Φ (x i ^ N * δ l * dualMinor e φ k k')) (p : κ) :
    ∃ (n : ℕ) (α β : MRing (T.wwIdx ι ν κ)),
      X ⟨.base, i⟩ ^ n * F * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ ∧
        X ⟨.base, i⟩ ^ n * F * X ⟨.line1, p⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩ ∈
          T.wwIdeal x δ e φ a₀ a₁ := by
  classical
  obtain ⟨r₁, hr₁, h₁⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi p k' ((hdet i hi).1 l)
  obtain ⟨r₂, hr₂, h₂⟩ := DiagonalForms.mul_dForm_mem B e φ hsec i hi k p ((hdet i hi).1 l)
  obtain ⟨n₁, G, hG, hGv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) x δ e φ a₀ a₁ i hi hr₁
  obtain ⟨n₂, H, hH, hHv⟩ := DiagonalForms.exists_form (ν := ν) (κ := κ) x δ e φ a₀ a₁ i hi hr₂
  have hXp : ∀ M, IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ M) (T.wwDeg M 0) := fun M =>
    DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_pow (DiagonalForms.isMultiHomog_X
      (ι := T.wwIdx ι ν κ) T.WBlk.base i) M) (by funext b; cases b <;> simp [T.wwDeg])
  have hdeg : ∀ {A B C : ℕ} {f : MRing (T.wwIdx ι ν κ)}, A + B = C → IsMultiHomog f (T.wwDeg B 0) →
      IsMultiHomog ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ A * f) (T.wwDeg C 0) := fun hABC hf =>
    DiagonalForms.isMultiHomog_of_eq (DiagonalForms.isMultiHomog_mul (hXp _) hf)
      (by funext b; cases b <;> simp [T.wwDeg, ← hABC])
  have hu := hdeg (A := n₁ + n₂) (C := N + 3 + n₁ + n₂) (by omega) hF
  have hα := hdeg (A := N + 3 + n₂) (C := N + 3 + n₁ + n₂) (by omega) hG
  have hβ := hdeg (A := N + 3 + n₁) (C := N + 3 + n₁ + n₂) (by omega) hH
  set c := T.wwCoord x δ e φ a₀ a₁
  set s := x i ^ (N + n₁ + n₂) * δ l
  have hxi : aeval c (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) = algebraMap Ω Φ (x i) := by
    rw [aeval_X]; rfl
  have hUv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (n₁ + n₂) * F) =
      algebraMap Ω Φ (s * dualMinor e φ k k') := by
    rw [map_mul, map_pow, hxi, hFv, ← map_pow, ← map_mul]; congr 1; ring
  have hAv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (N + 3 + n₂) * G) =
      algebraMap Ω Φ (s * dualMinor e φ p k') := by
    rw [map_mul, map_pow, hxi, hGv, ← map_pow, ← map_mul]; congr 1
    simp only [s, dualMinor]; linear_combination (-(x i ^ (N + n₁ + n₂))) * h₁
  have hBv : aeval c ((X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ (N + 3 + n₁) * H) =
      algebraMap Ω Φ (s * dualMinor e φ k p) := by
    rw [map_mul, map_pow, hxi, hHv, ← map_pow, ← map_mul]; congr 1
    simp only [s, dualMinor]; linear_combination (-(x i ^ (N + n₁ + n₂))) * h₂
  have hcr : ∀ a : Φ, algebraMap Ω Φ (s * dualMinor e φ k k') * T.lineVal e (φ p) a -
      algebraMap Ω Φ (s * dualMinor e φ p k') * T.lineVal e (φ k) a -
      algebraMap Ω Φ (s * dualMinor e φ k p) * T.lineVal e (φ k') a = 0 := fun a => by
    simp only [T.lineVal, dualMinor, map_mul, map_sub]; ring
  have hC : ∀ a : Φ, (C (algebraMap Ω Φ (s * dualMinor e φ k k')) * C (T.lineVal e (φ p) a) -
      C (algebraMap Ω Φ (s * dualMinor e φ p k')) * C (T.lineVal e (φ k) a) -
      C (algebraMap Ω Φ (s * dualMinor e φ k p)) * C (T.lineVal e (φ k') a) : MvPolynomial T.WBlk Φ) = 0 :=
    fun a => by rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_sub, hcr, map_zero]
  have hX0 : ∀ q : κ, T.multiConeMap c (X ⟨T.WBlk.line0, q⟩) = C (T.lineVal e (φ q) a₀) * X T.WBlk.line0 :=
    fun q => by simp [T.multiConeMap, c, T.wwCoord]
  have hX1 : ∀ q : κ, T.multiConeMap c (X ⟨T.WBlk.line1, q⟩) = C (T.lineVal e (φ q) a₁) * X T.WBlk.line1 :=
    fun q => by simp [T.multiConeMap, c, T.wwCoord]
  refine ⟨n₁ + n₂, X ⟨T.WBlk.base, i⟩ ^ (N + 3 + n₂) * G, X ⟨T.WBlk.base, i⟩ ^ (N + 3 + n₁) * H, ?_, ?_⟩
  all_goals
    rw [T.wwIdeal, RingHom.mem_ker, map_sub, map_sub, map_mul _ (_ ^ (n₁ + n₂) * F),
      map_mul _ (_ ^ (N + 3 + n₂) * G), map_mul _ (_ ^ (N + 3 + n₁) * H),
      DiagRAux.multiConeMap_of_homog c _ _ hu, DiagRAux.multiConeMap_of_homog c _ _ hα,
      DiagRAux.multiConeMap_of_homog c _ _ hβ, hUv, hAv, hBv]
  · rw [hX0, hX0, hX0]
    linear_combination ((∏ b, X b ^ T.wwDeg (N + 3 + n₁ + n₂) 0 b) * X T.WBlk.line0) * hC a₀
  · rw [hX1, hX1, hX1]
    linear_combination ((∏ b, X b ^ T.wwDeg (N + 3 + n₁ + n₂) 0 b) * X T.WBlk.line1) * hC a₁

end DiagonalOffMinor

open DiagonalOffMinor in

theorem DiagOffMinor.proof : DiagOffMinor.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec _ hdet _ a _ W hWp hrel hW i l k k' hfr hQ
  obtain ⟨hXi, -, N, F, hF, hFv, hFW⟩ := hfr
  classical
  have hi : x i ≠ 0 := by
    intro h0
    apply hXi
    apply hW
    rw [T.wwIdeal, RingHom.mem_ker]
    simp [T.multiConeMap, T.wwCoord, h0]
  have hrel' : ∀ p : κ, ∃ u α β : MRing (T.wwIdx ι ν κ), u ∉ W ∧
      u * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ ∈ W ∧
      u * X ⟨.line1, p⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩ ∈ W := fun p => by
    obtain ⟨n, α, β, h0, h1⟩ := frame_rel x δ e φ B hsec hdet (a 0) (a 1) i hi l k k' N F hF hFv p
    refine ⟨X ⟨T.WBlk.base, i⟩ ^ n * F, α, β, ?_, ?_, ?_⟩
    · intro h
      rcases hWp.mem_or_mem h with h' | h'
      · have hXn : ∀ m : ℕ, (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ m ∉ W := by
          intro m
          induction m with
          | zero => rw [pow_zero]; exact (Ideal.ne_top_iff_one W).1 hWp.ne_top
          | succ m ihm => rw [pow_succ]; exact fun hm => (hWp.mem_or_mem hm).elim ihm hXi
        exact hXn n h'
      · exact hFW h'
    · exact hW h0
    · exact hW h1
  have hQ' : (X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩ : MRing (T.wwIdx ι ν κ)) ∈ W := hQ
  obtain ⟨p, hp⟩ := hrel T.WBlk.line0
  by_cases hk : (X ⟨.line0, k⟩ : MRing (T.wwIdx ι ν κ)) ∈ W
  · have hk' : (X ⟨.line0, k'⟩ : MRing (T.wwIdx ι ν κ)) ∉ W := by
      intro hk'
      obtain ⟨u, α, β, hu, h0, -⟩ := hrel' p
      have h := add_mem (add_mem h0 (W.mul_mem_left α hk)) (W.mul_mem_left β hk')
      rw [show u * X ⟨.line0, p⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩ + α * X ⟨.line0, k⟩ +
        β * X ⟨.line0, k'⟩ = u * (X ⟨.line0, p⟩ : MRing (T.wwIdx ι ν κ)) by ring] at h
      exact (hWp.mem_or_mem h).elim hu hp
    have := hWp
    refine diag_le_of_prop x δ e φ (a 0) (a 1) W hW k' hk' fun q => ?_
    obtain ⟨u, α, β, hu, h0, h1⟩ := hrel' q
    refine (hWp.mem_or_mem ?_).resolve_left hu
    rw [show u * (X ⟨.line0, k'⟩ * X ⟨.line1, q⟩ - X ⟨.line1, k'⟩ * X ⟨.line0, q⟩) =
      X ⟨.line0, k'⟩ * (u * X ⟨.line1, q⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩) -
        X ⟨.line1, k'⟩ * (u * X ⟨.line0, q⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩) -
        α * (X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩) by ring]
    exact sub_mem (sub_mem (W.mul_mem_left _ h1) (W.mul_mem_left _ h0)) (W.mul_mem_left _ hQ')
  · have := hWp
    refine diag_le_of_prop x δ e φ (a 0) (a 1) W hW k hk fun q => ?_
    obtain ⟨u, α, β, hu, h0, h1⟩ := hrel' q
    refine (hWp.mem_or_mem ?_).resolve_left hu
    rw [show u * (X ⟨.line0, k⟩ * X ⟨.line1, q⟩ - X ⟨.line1, k⟩ * X ⟨.line0, q⟩) =
      X ⟨.line0, k⟩ * (u * X ⟨.line1, q⟩ - α * X ⟨.line1, k⟩ - β * X ⟨.line1, k'⟩) -
        X ⟨.line1, k⟩ * (u * X ⟨.line0, q⟩ - α * X ⟨.line0, k⟩ - β * X ⟨.line0, k'⟩) +
        β * (X ⟨.line0, k⟩ * X ⟨.line1, k'⟩ - X ⟨.line0, k'⟩ * X ⟨.line1, k⟩) by ring]
    exact add_mem (sub_mem (W.mul_mem_left _ h1) (W.mul_mem_left _ h0)) (W.mul_mem_left _ hQ')

end

end GroundTheory.Heights₂.Heights.Inter
