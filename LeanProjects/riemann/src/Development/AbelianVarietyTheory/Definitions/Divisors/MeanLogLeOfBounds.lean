import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

variable {F : Type} [Field F] [NumberField F]

def PointRes (X : Data F) (b J : ℝ) : Prop :=
  ∃ (m : ℕ) (θ : Fin m → X.V 0) (B : Fin m → (F →+* ℂ) → ℝ), (∀ i, θ i ∈ X.M 0) ∧ Submodule.span F (Set.range θ) = ⊤ ∧
    (∀ i σ, 0 < B i σ) ∧ (∀ i, meanLog F (B i) ≤ b) ∧
    ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E), (∀ i, s i ∈ X.latticeOver E) →
      ∀ (hs : (X.baseChange E).IsGood s) (x : RatPt (X.baseChange E).toGeo s),
        ∃ γ : (E →+* ℂ) → ℝ, (∀ τ, 0 < γ τ) ∧
          (∀ i τ, x.nrm 0 τ (hs.res 0 (X.toExtV E 0 (θ i)).1) ≤ B i (τ.comp (algebraMap F E)) / γ τ) ∧
          -meanLog E γ ≤ J + ((X.D : ℝ) + 3) * x.ht

theorem PointRes.mono {X : Data F} {b b' J J' : ℝ} (h : PointRes X b J) (hb : b ≤ b') (hJ : J ≤ J') : PointRes X b' J' := by
  obtain ⟨m, θ, B, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨m, θ, B, h₁, h₂, h₃, fun i => (h₄ i).trans hb, fun E _ _ _ s hm hs x => ?_⟩
  obtain ⟨γ, g₁, g₂, g₃⟩ := h₅ E s hm hs x
  exact ⟨γ, g₁, g₂, by linarith⟩

theorem PointRes.exists_coord {X : Data F} {b J : ℝ} (h : PointRes X b J) :
    ∃ (m : ℕ) (θ : Fin m → X.V 0) (B : Fin m → (F →+* ℂ) → ℝ), (∀ i, θ i ∈ X.M 0) ∧ Submodule.span F (Set.range θ) = ⊤ ∧
      (∀ i σ, 0 < B i σ) ∧ (∀ i, meanLog F (B i) ≤ b) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin X.D → Fin X.N → E), (∀ i, s i ∈ X.latticeOver E) →
        ∀ hs : (X.baseChange E).IsGood s, Split X.toTuple E s →
          ∃ Co : Coord (X.baseChange E).toGeo hs (X.geomPts E (X.linSection E s)).ncard,
            X.cycleHeight E (X.linSection E s) = (∑ p, vecHt (fun k => Co.gen k p) fun σ => Co.c₁ σ p) ∧
            ∀ p, ∃ γ : (E →+* ℂ) → ℝ, (∀ τ, 0 < γ τ) ∧
              (∀ i τ, ‖τ (Co.ev 0 (hs.res 0 (X.toExtV E 0 (θ i)).1) p)‖ / Co.c₂ τ p ≤
                B i (τ.comp (algebraMap F E)) / γ τ) ∧
              -meanLog E γ ≤ J + ((X.D : ℝ) + 3) * vecHt (fun k => Co.gen k p) fun τ => Co.c₁ τ p := by
  obtain ⟨m, θ, B, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨m, θ, B, h₁, h₂, h₃, h₄, fun E _ _ _ s hm hs hsp => ?_⟩
  obtain ⟨x, Co, hCo, e⟩ := Split.exists_coord (G := X.toGeo) hsp hs
  refine ⟨Co, e.trans (Finset.sum_congr rfl fun p _ => (hCo.vecHt_eq p).symm), fun p => ?_⟩
  obtain ⟨γ, g₁, g₂, g₃⟩ := h₅ E s hm hs (x p)
  exact ⟨γ, g₁, fun i τ => (hCo.norm_ev p τ _).trans_le (g₂ i τ),
    g₃.trans_eq (congrArg (J + _ * ·) (hCo.vecHt_eq p).symm)⟩

section Line

def linePt : RatPt ((Proj.geo ℚ (M := 1) le_rfl).baseChange ℚ) fun _ => ![1, 0] :=
  haveI : IsIso ((((Proj.geo ℚ (M := 1) le_rfl).baseChange ℚ).ideal fun _ => ![1, 0]).subschemeι ≫
    ((Proj.geo ℚ (M := 1) le_rfl).baseChange ℚ).str) := projTuple.isIso_cut_line
  ⟨inv _, (IsIso.inv_hom_id _).trans (Spec.map_id _).symm⟩

example : ∃ (δ : ℕ) (x : Fin δ ≃ RatPt ((Proj.geo ℚ (M := 1) le_rfl).baseChange ℚ) fun _ => ![1, 0])
    (Co : Coord ((Proj.geo ℚ (M := 1) le_rfl).baseChange ℚ)
      (Geo.isGood_baseChange_iff.2 projTuple.isGoodSection_line.1) δ), 0 < δ ∧ Co.AtPoints x := by
  obtain ⟨x, Co, h, -⟩ := Split.exists_coord (G := Proj.geo ℚ (M := 1) le_rfl) (E := ℚ) (s := fun _ => ![1, 0])
    (fun _ hx => ⟨@inv _ _ _ _ _ projTuple.isIso_cut_line, (@IsIso.eq_comp_inv _ _ _ _ _ _ projTuple.isIso_cut_line _ _).2 hx⟩)
    (Geo.isGood_baseChange_iff.2 projTuple.isGoodSection_line.1)
  exact ⟨_, x, Co, (x.symm linePt).pos, h⟩

example {K : Type} [Field K] [NumberField K] {G : Geo K} {s : Fin G.D → Fin G.N → K} (x : RatPt G s) (τ : K →+* ℂ)
    (g : G.SecOn s 0) : x.nrm 0 τ g = 0 ↔ x.val 0 g = 0 := by
  simp [x.nrm_eq, (x.c₂_pos τ).ne']

end Line

end GlobalTheory.HSCore
