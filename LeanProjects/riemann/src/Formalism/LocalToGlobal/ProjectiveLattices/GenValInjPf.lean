import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable (Xo c) in

def GenSpecSt (hG : GenFrEx Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (m : Ideal p.R) [m.IsMaximal],
    ∃ (Z : Comp Xo c) (q : TRing c.F) (yq : FrPt Xo c q.R),
      (∃ (p' : TRing c.F) (lam : p.R →ₐ[c.F] p'.R) (a : q.R →ₐ[c.F] p'.R)
          (μ : p'.R →ₐ[c.F] Localization.AtPrime m) (y' : FrPt Xo c p'.R),
        FrMap lam y y' ∧ FrMap a yq y' ∧ μ.comp lam = locM c.F m) ∧
      ∀ (p₀ : TRing c.F) (φ₀ : p₀.R →ₐ[c.F] Om Z) (y₀ : FrPt Xo c p₀.R), FrMap φ₀ y₀ (genFr hG Z) →
        ∃ (B : TRing c.F) (β : q.R →ₐ[c.F] B.R) (β₀ : p₀.R →ₐ[c.F] B.R) (yB y₀B : FrPt Xo c B.R)
          (tB : Ix Dw → (B.R)ˣ) (Ω : Type) (_ : Field Ω) (_ : Algebra c.F Ω)
          (κ : Om Z →ₐ[c.F] Ω) (γ : B.R →ₐ[c.F] Ω),
          FrMap β yq yB ∧ FrMap β₀ y₀ y₀B ∧ FrBor tB y₀B yB ∧ γ.comp β₀ = κ.comp φ₀ ∧
            Function.Injective (γ.comp β)

theorem evR_of_frMap (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra c.F S] {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y : FrPt Xo c p.R}
    {w : FrPt Xo c S} (hy : FrMap φ y w) : evR Xo c f w = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, φ, y, hy⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact hW f hf S _ _ _ _ _ _ w hT.choose_spec.choose_spec.choose_spec hy

theorem rule_eq_zero_of_genSpec (hW : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
    (hG : GenFrEx Xo c) (hA : AllTest Xo c) (hS : GenSpecSt Xo c hG) {e : Ix Dw → ℕ} {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    (hw : IsWeight (K := c.F) (fun S _ _ => FrPt Xo c S) (fun t y y' => FrBor t y y') e f)
    (h0 : ∀ Z : Comp Xo c, evC hG Z f = 0) : f = 0 := by
  funext p y
  show f p y = 0
  apply eq_of_locM (K := c.F)
  intro m hm
  obtain ⟨Z, q, yq, ⟨p', lam, a, μ, y', h1, h2, h3⟩, hgen⟩ := hS p y m
  have hq : f q yq = 0 := by
    obtain ⟨p₀, φ₀, y₀, h₀⟩ := hA (Om Z) (genFr hG Z)
    obtain ⟨B, β, β₀, yB, y₀B, tB, Ω, _, _, κ, γ, hβ, hβ₀, hb, hc, hinj⟩ := hgen p₀ φ₀ y₀ h₀
    have hz : φ₀ (f p₀ y₀) = 0 := by
      rw [← evR_of_frMap hW hf h₀]
      exact h0 Z
    apply hinj
    rw [map_zero, AlgHom.comp_apply, ← hf q B β yq yB hβ, hw B tB y₀B yB hb, map_mul,
      hf p₀ B β₀ y₀ y₀B hβ₀, ← AlgHom.comp_apply γ β₀, hc, AlgHom.comp_apply, hz, map_zero, mul_zero]
  have e1 : locM c.F m (f p y) = μ (lam (f p y)) := by
    rw [← AlgHom.comp_apply μ lam, h3]
  rw [e1, ← hf p p' lam y y' h1, hf q p' a yq y' h2, hq, map_zero, map_zero, map_zero]

end Gen

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D}

theorem genValInj (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hS : GenSpecSt (T.Q.Xo j) T.Q.c hG) : GenValInjSt h j hG := by
  intro w g hg
  have hC : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hC).1
  apply Subtype.ext
  exact rule_eq_zero_of_genSpec (h.evalWD j hj) hG (h.allTest j hj) hS hsec.1 hsec.2 hg

end Formalism.L2.Pj
