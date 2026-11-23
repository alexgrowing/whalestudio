import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def GamAt {D : D7} (T : Top D) : Prop :=
  ∀ (j : ℕ) (_hj : InR D j) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E), IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
    (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y) →
    γ ∈ ((T.U j σ).X k).Γ

def ModelGamSt : Prop := ∀ (D : D7) (T : Full D), LawsFull T → GamAt T.toTop

def HalfDiffNormSt : Prop :=
  ∀ D : D7, 0 < Ideal.absNorm D.host.𝔟 ∧
    2 * Real.log (Ideal.absNorm D.host.𝔟 : ℝ) ≤ Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)|

def ShortInvSt : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    ∃ (B : ℝ) (a : D.host.E), Real.log B ≤ 3 * large₂.sc.L ∧ a ≠ 0 ∧ a ∈ D.host.AA⁻¹ ∧
      ∀ τ : D.host.E →+* ℂ, ‖τ a‖ ≤ B

def ModelLatSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j),
    SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp,
    ∃ (L' : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (NA NC g M : ℕ),
      L'.FG ∧ (∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm ((T.U j σ).X k).Gm x y)) ∧
      (∀ x, (∀ y ∈ L', IsIntegral ℤ (herm ((T.U j σ).X k).Gm x y)) → x ∈ L') ∧
      ((T.U j σ).X k).Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ L', v = a • u} ∧
      0 < NA ∧ 0 < NC ∧ (∀ x ∈ ((T.U j σ).X k).Λ, (NA : D.host.E) • x ∈ L') ∧
      (∀ x ∈ L', (NC : D.host.E) • x ∈ ((T.U j σ).X k).Λ) ∧ g = T.Q.l.M ∧ 0 < g ∧
      (∀ γ : GL (Fin D.R.r) D.host.E, IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ →
        (∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
          Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (g : D.host.E) • y) →
        γ ∈ ((T.U j σ).X k).Γ) ∧
      0 < M ∧ Real.log NA ≤ D.R.f * lrd D ∧ Real.log NC ≤ 2 * large₂.sc.L ∧ Real.log M ≤ 23 * large₂.sc.L ∧
      (∃ B : ℝ, Real.log B ≤ 3 * large₂.sc.L ∧ ∀ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 →
        ∃ a : D.host.E, a ≠ 0 ∧ a • v ∈ L' ∧ ∀ τ : D.host.E →+* ℂ, ‖τ a‖ ≤ B) ∧
      (∀ v ∈ L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
        ∃ γ ∈ ((T.U j σ).X k).Γ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) =
          transvMat ((T.U j σ).X k).Gm v ((M : D.host.E) * b * ((T.U j σ).X k).κ0)) ∧
      NA = Ideal.absNorm D.host.𝔟 ∧ NC = Ideal.absNorm D.host.ccK

end ReciprocityTheory.ChartRestriction.G.PullbackSections
