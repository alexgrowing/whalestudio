import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LinearIndependentSingleAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors Matrix

noncomputable section

namespace GlobalTheory.EqCovol.IsoPlane

open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem selfD_of_isSelfDualTr {r : ℕ} (Y : Data E r) (h : IsSelfDualTr Y) : GlobalTheory.SW.SelfD Y Y.Λ := by
  refine ⟨Y.Λ_fg, fun x => (h x).trans (forall₂_congr fun y _ => ?_)⟩
  rw [GlobalTheory.ThFr.EF_def]
  rcases Y.κ0_xi with hk | hk
  · rw [hk, show (2 * Y.ξ0) / 2 = Y.ξ0 by ring]
  · have e : -(-(2 * Y.ξ0) / 2) * herm Y.Gm x y = -(-Y.ξ0 * herm Y.Gm x y) := by ring
    rw [hk, e, map_neg]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn, Int.cast_neg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩

def hypG : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem hypG_herm (a b : Fin 2) : cc (hypG (E := E) a b) = hypG b a := by
  fin_cases a <;> fin_cases b <;> simp [hypG, cc]

theorem hypG_det : (hypG (E := E)).det ≠ 0 := by
  simp [hypG, Matrix.det_fin_two_of]

theorem herm_hypG (x y : Fin 2 → E) : herm hypG x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
  simp [herm, hypG, Fin.sum_univ_two]

def hypLat (J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 2 → E) :=
  ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).comap (LinearMap.proj 0) ⊓
    (J : Submodule (𝓞 E) E).comap (LinearMap.proj 1)

theorem mem_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} {x : Fin 2 → E} :
    x ∈ hypLat J ↔ x 0 ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ∧ x 1 ∈ J := Iff.rfl

theorem isLattice_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (hypLat J) := by
  classical
  constructor
  · refine Submodule.FG.of_le ((Submodule.fg_span_singleton (Pi.single 0 1 : Fin 2 → E)).sup
      ((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map
        (LinearMap.single (𝓞 E) (fun _ : Fin 2 => E) 1))) fun x hx => ?_
    obtain ⟨h0, h1⟩ := mem_hypLat.1 hx
    let z : 𝓞 E := ⟨x 0, mem_one_fractionalIdeal_iff.1 h0⟩
    refine Submodule.mem_sup.2 ⟨z • Pi.single 0 1, Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _),
      Pi.single 1 (x 1), ⟨x 1, h1, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · simp [Algebra.smul_def]; rfl
    · simp
  · obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (mt FractionalIdeal.coeToSubmodule_eq_bot.1 hJ0)
    have e0 : (Pi.single 0 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
    have e1' : (Pi.single 1 j : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by simpa using hj⟩)
    have e1 : (Pi.single 1 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) := by
      have := Submodule.smul_mem _ j⁻¹ e1'
      rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hj0] at this
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → E) + v 1 • Pi.single 1 1 := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ e0) (Submodule.smul_mem _ _ e1)

theorem modular_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) (hJc : ∀ z ∈ J, cc z ∈ J)
    (x : Fin 2 → E) : x ∈ hypLat J ↔ ∀ y ∈ hypLat J, herm hypG x y ∈ J := by
  constructor
  · intro hx y hy
    obtain ⟨hx0, hx1⟩ := mem_hypLat.1 hx
    obtain ⟨hy0, hy1⟩ := mem_hypLat.1 hy
    rw [herm_hypG]
    refine (J : Submodule (𝓞 E) E).add_mem ?_ ?_
    · simpa using FractionalIdeal.mul_mem_mul hx0 (hJc _ hy1)
    · have : cc (y 0) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
        mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hy0))
      simpa using FractionalIdeal.mul_mem_mul hx1 this
  · intro h
    have h1 : x 1 ∈ J := by
      have := h (Pi.single 0 1) (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
      simpa [herm_hypG, cc] using this
    have h0 : ∀ j ∈ J, x 0 * j ∈ J := fun j hj => by
      have := h (Pi.single 1 (cc j)) (mem_hypLat.2 ⟨by simp, by simpa using hJc j hj⟩)
      simpa [herm_hypG, cc] using this
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J ≤ J := by
      refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact (J : Submodule (𝓞 E) E).smul_mem a (h0 j hj)
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0)
          = J⁻¹ * (FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J) := by
            rw [mul_left_comm, inv_mul_cancel₀ hJ0, mul_one]
        _ ≤ J⁻¹ * J := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hJ0
    exact ⟨hle1 (FractionalIdeal.mem_spanSingleton_self _ _), h1⟩

theorem hypG_signature (τ : E →+* ℂ) : ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
    gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  refine ⟨!![1, 1; 1 / 2, -1 / 2], by simp [Matrix.det_fin_two_of]; norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, hypG, sgn, Fin.sum_univ_two, map_ofNat] <;> norm_num

theorem iso_rank_two (H : Host E) (Y : Data E 2) (hp : Y.p0 = 1) (hY : IsSelfDualTr Y) :
    ∃ z : Fin 2 → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  haveI := H.unram
  obtain ⟨J, hJ0, hJc, hJ⟩ := GlobalTheory.Ker.OntoLat.exists_valueIdeal Y
  have HN := GlobalTheory.QNorm.hasseNormSt
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ (Y.Ψ : Set (E →+* ℂ)) ∨ ComplexEmbedding.conjugate τ ∈ (Y.Ψ : Set (E →+* ℂ)) := by
    intro τ
    by_cases h : ComplexEmbedding.conjugate τ ∈ Y.Ψ
    · exact Or.inr h
    · exact Or.inl ((Y.cmType τ).mpr h)
  have hs : ∀ τ ∈ (Y.Ψ : Set (E →+* ℂ)), ∃ p : ℕ,
      (∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ Y.Gm Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ hτ
    obtain ⟨Q, hQ, hg⟩ := Y.signature ⟨τ, hτ⟩
    rw [hp] at hg
    exact ⟨1, ⟨Q, hQ, hg⟩, hypG_signature τ⟩
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := hypG) (L := Y.Λ)
    (L' := hypLat J) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt HN) HN hJ0 hJc Y.Gm_herm hypG_herm Y.Gm_det
    hypG_det ⟨Y.Λ_fg, Y.Λ_span⟩ (isLattice_hypLat hJ0) (hJ Y.Λ (selfD_of_isSelfDualTr Y hY))
    (modular_hypLat hJ0 hJc) (GlobalTheory.Published.Landherr.congr_of_signature _ hΨ hs)
  refine ⟨P *ᵥ Pi.single 0 1, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_hypG]
    simp

end GlobalTheory.EqCovol.IsoPlane

namespace GlobalTheory.EqCovol

theorem exists_isotropic_of_isSelfDualTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ)
    (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  intro E _ _ _ H r Y h1 h2 hY
  by_cases hr : 3 ≤ r
  · obtain ⟨cu⟩ := GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt E r 1 Y h1 (by omega) (by omega)
    exact ⟨cu.e 0, cu.ind.ne_zero 0, cu.iso 0 0⟩
  · obtain rfl : r = 2 := by omega
    exact IsoPlane.iso_rank_two H Y (by omega) hY

end GlobalTheory.EqCovol
