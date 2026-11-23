import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.HTLat.OmegaRank GlobalTheory.EigenSplit GlobalTheory.Frames ReciprocityTheory.ChartRestriction.G.Pdiv Formalism.L2.Pj
open scoped CategoryTheory.Obj NNReal

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable (K) in

def detSpan (m : ℕ) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (⋀[K]^m V) :=
  Submodule.span (𝓞 K) {w | ∃ y : Fin m → V, (∀ i, y i ∈ L) ∧ w = exteriorPower.ιMulti K m y}

variable (K) in

def idx (m : ℕ) (L N : Submodule (𝓞 K) V) : Ideal (𝓞 K) := (detSpan K m N).colon (detSpan K m L)

example (m : ℕ) (L : Submodule (𝓞 K) V) : idx K m L L = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Submodule.mem_colon.2 fun _ h => by simpa using h)

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def phiP (a : Fin p) : (X.A true).t.G ⟶ X.B.t.G := X.φ (Sum.inl a)

def phiQ (a : Fin q) : (X.A false).t.G ⟶ X.B.t.G := X.φ (Sum.inr a)

def IsGram (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)) : Prop :=
  (∀ a b, WeilEq X.B.t.PP.L (phiP X a) (phiP X b) (X.A true).t.PP.L ((X.A true).t.act.act (gP a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))) ∧
  ∀ a b, WeilEq X.B.t.PP.L (phiQ X a) (phiQ X b) (X.A false).t.PP.L ((X.A false).t.act.act (gQ a b)) (𝟙 _)
    (spMap (σ₁.comp (algebraMap (𝓞 K) K)))

variable {X} (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
  (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))

def IsDiffs : Prop := (∀ a, FP.IsDiffOf FB (phiP X a) (MP a)) ∧ ∀ a, FQ.IsDiffOf FB (phiQ X a) (MQ a)

def subP (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FP.eigLat (X.A true).t.act τ).map ((MP a).restrictScalars (𝓞 K))

def subQ (τ : 𝓞 E →+* 𝓞 K) : Submodule (𝓞 K) (Fin FB.P₀.g → K) :=
  ⨆ a, (FQ.eigLat (X.A false).t.act τ).map ((MQ a).restrictScalars (𝓞 K))

def IdealSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H →
    ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q)
      (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)), IsGram X gP gQ →
      ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
        ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
          (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
          (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ →
          ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
            idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ) * Ideal.span {τ gQ.det} =
              𝔫.map τ * idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
                (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))

def PointShiftSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (τ : E →+* ℂ_[ℓ]), ∃ κ₁ κ₂ : ℝ,
      letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
      ∀ [IsAdicComplete (Ideal.span {(ℓ : 𝓞_ℂ_[ℓ])}) 𝓞_ℂ_[ℓ]]
        (P : Point ℓ (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) 𝓞_ℂ_[ℓ] (𝓞 E)) (p q : ℕ),
        (∀ φ : E →+* ℂ_[ℓ], Module.finrank ℂ_[ℓ] (P.eigW (embO P.integers φ)) =
          open Classical in if φ (H.rt : E) = τ (H.rt : E) then p else q) →
        ∀ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) ℂ_[ℓ])
          (g' : Matrix (Fin q) (Fin q) ℂ_[ℓ]),
          Submodule.span 𝓞_ℂ_[ℓ] (Set.range fun i => P.bLie (x i)) = P.wRec (embO P.integers τ) →
          Submodule.span 𝓞_ℂ_[ℓ] (Set.range fun i => P.bLie (x' i)) =
            P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))) →
          IsLatBasis ℂ_[ℓ] (open Classical in P.latTQuot (σ := fun φ : E →+* ℂ_[ℓ] => embO P.integers φ)
            (isSplitting_embO P.integers) τ) (fun i => ∑ j, g i j • P.bLie (x j)) →
          IsLatBasis ℂ_[ℓ] (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E))))
            (fun i => ∑ j, g' i j • P.bLie (x' j)) →
          Real.log ‖g.det‖ - Real.log ‖g'.det‖ = p * κ₁ + q * κ₂

end GlobalTheory.FlatCM

end
