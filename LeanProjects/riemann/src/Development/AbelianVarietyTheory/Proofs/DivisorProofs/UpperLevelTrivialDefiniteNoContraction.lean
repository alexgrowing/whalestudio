import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProofStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteLevel

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_comb_colP {r : ℕ} (X : Data E r) (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (v : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, v = ∑ a, K a • X.colP x τ a := by
  refine ⟨fun a => ((mat x τ)⁻¹ *ᵥ v) (Fin.castLE X.p0_le a), ?_⟩
  have h1 : v = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  have h2 : ∀ w : Fin r → ℂ, mat x τ *ᵥ w = ∑ j, w j • ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j := by
    intro w; funext k; simp [Matrix.mulVec, dotProduct, ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_apply, mul_comm]
  conv_lhs => rw [h1, h2]
  exact (Fintype.sum_equiv (finCongr hp) _ _ (fun a => rfl)).symm

theorem maj_mulVec_of_definite {r : ℕ} (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v)
    (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ (((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ u) = X.maj x τ u := by
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg' : ∀ w, g *ᵥ (g' *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hg'g : ∀ w, g' *ᵥ (g *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hiso := GlobalTheory.MajInv.hermC_stab X hγ τ.1
  have key := MajorantConjugateTransfer.maj_transfer X hx hx τ g g' hgg' hiso ?_ ?_ (g *ᵥ u)
  · rwa [hg'g] at key
  · intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · exact exists_comb_colP X hp x τ (hx τ).1 _
  · intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · obtain ⟨L, hL⟩ := exists_comb_colP X hp x τ (hx τ).1 (g' *ᵥ X.colP x τ a)
      refine ⟨L, ?_⟩
      calc X.colP x τ a = g *ᵥ (g' *ᵥ X.colP x τ a) := (hgg' _).symm
        _ = g *ᵥ ∑ c, L c • X.colP x τ c := by rw [hL]
        _ = ∑ c, L c • (g *ᵥ X.colP x τ c) := by
          rw [Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul]

theorem eq_one_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g →
    (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) →
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∀ γ ∈ G, γ = 1 := by
  intro E _ _ _ r X G g hg hgr hU hUn hp x hx hnc γ hγ
  refine GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hg hgr G hU hUn x hx hnc γ hγ fun τ u => ?_
  rw [maj_mulVec_of_definite X.toData hp hx γ (hU γ hγ).1 τ u]
  have h0 := MajorantConjugateTransfer.maj_nonneg X.toData hx τ u
  have h1 : 1 ≤ Real.exp (1 / (3 * (r : ℝ))) := Real.one_le_exp (by positivity)
  exact le_mul_of_one_le_left h0 (one_le_pow₀ h1)

end GlobalTheory.DefiniteLevel
