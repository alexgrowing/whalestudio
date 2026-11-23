import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.ActRight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_bar (H : Host E) (s : 𝓞 E) : H.bar (H.bar s) = s := by
  apply Subtype.ext
  show ((H.bar (H.bar s) : 𝓞 E) : E) = (s : E)
  rw [H.bar_eq, H.bar_eq]
  simp

theorem weilEq_act_adj (H : Host E) (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ)
    (A : PAT H (Sp (𝓞 K))) (a : 𝓞 E) :
    WeilEq A.t.PP.L (A.t.act.act (H.bar a)) (𝟙 _) A.t.PP.L (𝟙 _) (A.t.act.act a)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have key := (GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hl (𝓞 K) A.pol A.pol A.pol A.pol
    (A.t.act.act (H.bar a)) (𝟙 _) (𝟙 _) (A.t.act.act a) (A.t.act.hom _) inferInstance inferInstance
    (A.t.act.hom a) ℂ (σ₁.comp (algebraMap (𝓞 K) K))).1
  apply key
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  have h := A.t.adj (H.bar a)
  rwa [bar_bar] at h

theorem weilEq_act_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g →
    ∀ r s : 𝓞 E,
    WeilEq B.t.PP.L f g A.t.PP.L (A.t.act.act r) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (A.t.act.act s ≫ g) A.t.PP.L (A.t.act.act (r * H.bar s)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g _ _ r s h n x y c hn hx hy
  haveI := A.t.act.hom s
  haveI := A.t.act.hom r
  have hy' : (y ≫ A.t.act.act s) ^ n = 1 := by rw [← MonObj.pow_comp, hy, MonObj.one_comp]
  have hx' : (x ≫ A.t.act.act r) ^ n = 1 := by rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  have h1 := h n x (y ≫ A.t.act.act s) c hn hx hy'
  have h2 := weilEq_act_adj H K σ₁ A s n (x ≫ A.t.act.act r) y c hn hx' hy
  rw [← Category.assoc, h1, A.t.act.mul, ← Category.assoc, h2]
  simp only [Category.comp_id]

end GlobalTheory.CM.ActRight
end
