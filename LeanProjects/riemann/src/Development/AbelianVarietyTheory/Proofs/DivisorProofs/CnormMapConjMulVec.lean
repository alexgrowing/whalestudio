import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.GramFrame

open Matrix Module
open scoped ComplexOrder InnerProductSpace

variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def gramOf {n : ℕ} (w : Fin n → Hs) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => ⟪w i, w j⟫_ℂ

theorem norm_sum_sq {n : ℕ} (w : Fin n → Hs) (c : Fin n → ℂ) :
    ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ (gramOf w *ᵥ c) := by
  have h1 : ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = ⟪∑ i, c i • w i, ∑ i, c i • w i⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, dotProduct, mulVec, gramOf, of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem gramOf_posDef {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) : (gramOf w).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun c hc => ?_⟩
  · ext i j
    simp [gramOf, conjTranspose_apply]
  · rw [← norm_sum_sq]
    have h0 : ∑ i, c i • w i ≠ 0 := fun h => hc (funext fun i => Fintype.linearIndependent_iff.1 hw c h i)
    exact Complex.zero_lt_real.2 (by positivity)

theorem exists_frame {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ ∀ c, Formalism.HermitianLatticesTheory.cnorm (B *ᵥ c) = ‖∑ i, c i • w i‖ := by
  obtain ⟨B, hB, hG⟩ := exists_unit_factor (gramOf_posDef hw)
  refine ⟨B, hB, fun c => ?_⟩
  have key : star (B *ᵥ c) ⬝ᵥ (B *ᵥ c) = star c ⬝ᵥ ((Bᴴ * B) *ᵥ c) := by
    have e0 : star c ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ c)) = (star c ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ c) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ((∑ i, ‖(B *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_norm_sq_eq, norm_sum_sq, hG, key]
  simp only [Formalism.HermitianLatticesTheory.cnorm, Complex.ofReal_injective e, Real.sqrt_sq (norm_nonneg _)]

theorem cnorm_map_conj_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (B.map (starRingEnd ℂ) *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ star u) := by
  have e : B.map (starRingEnd ℂ) *ᵥ u = star (B *ᵥ star u) := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [e]
  simp [Formalism.HermitianLatticesTheory.cnorm]

end GlobalTheory.HSApp.GramFrame

open GlobalTheory.HSApp.GramFrame Matrix Module in

theorem GlobalTheory.HSApp.hasGram_of_inner : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ), (∀ v : InfinitePlace K, ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (Φ : V →+ Hs), ((∀ (a : K) (x : V), Φ (a • x) = v.embedding a • Φ x) ∨ (∀ (a : K) (x : V), Φ (a • x) = starRingEnd ℂ (v.embedding a) • Φ x)) ∧ (∀ x, N v.embedding x = ‖Φ x‖) ∧ ∀ (n : ℕ) (e : Fin n → V), LinearIndependent K e → LinearIndependent ℂ (fun i => Φ (e i))) → GlobalTheory.AllWt.HasGram N := by
  intro K V _ _ _ _ _ N h
  classical
  let b := Module.finBasis K V
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K V)) (Fin (finrank K V)) ℂ, IsUnit Y.det ∧
      ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x) = N v.embedding x := by
    intro v
    obtain ⟨Hs, i1, i2, Φ, hlin, hN, hli⟩ := h v
    obtain ⟨B, hB, hBn⟩ := exists_frame (hli _ b b.linearIndependent)
    have hsum : ∀ x, Φ x = ∑ i, Φ (b.repr x i • b i) := fun x => by
      conv_lhs => rw [← b.sum_repr x]
      exact map_sum Φ _ _
    rcases hlin with hl | hl
    · refine ⟨B, hB, fun x => ?_⟩
      rw [hN, hBn, hsum]
      simp only [hl]
      rfl
    · refine ⟨B.map (starRingEnd ℂ), ?_, fun x => ?_⟩
      · have e := RingHom.map_det (starRingEnd ℂ) B
        change IsUnit ((starRingEnd ℂ).mapMatrix B).det
        rw [← e]
        exact hB.map _
      · rw [cnorm_map_conj_mulVec, hN, hBn, hsum]
        simp only [hl]
        rfl
  choose Y hY hYn using key
  refine GlobalTheory.AllWt.IsGram.hasGram (b := b) (X := fun v => (Y v)⁻¹) fun v => ⟨isUnit_nonsing_inv_det _ (hY v), fun x => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
  rw [nonsing_inv_nonsing_inv _ (hY v)]
  exact hYn v x
