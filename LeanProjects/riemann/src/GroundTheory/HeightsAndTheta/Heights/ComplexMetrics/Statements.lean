import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
  GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N)

structure ContinuousMetric (L : X.X.Modules) where

  norm : ∀ (ρ : A →+* ℂ) (x : X.complexPoints ρ), X.Fibre L x → ℝ

  norm_smul : ∀ (ρ : A →+* ℂ) (x : X.complexPoints ρ) (c : ℂ) (s : X.Fibre L x),
    norm ρ x (c • s) = ‖c‖ * norm ρ x s

  norm_pos : ∀ (ρ : A →+* ℂ) (x : X.complexPoints ρ) (s : X.Fibre L x), s ≠ 0 → 0 < norm ρ x s

  continuous_frame : ∀ (ρ : A →+* ℂ) (U : X.X.Opens) (e : ((preMod X.X).obj L).obj (op U)),
    IsBasisOn ((preMod X.X).obj L) U e →
      Continuous fun y : {x : X.complexPoints ρ // X.point x ∈ U} =>
        norm ρ y.1 (X.sectionValue y.1 y.2 e)

  norm_conj : ∀ (ρ : A →+* ℂ) (U : X.X.Opens) (s : ((preMod X.X).obj L).obj (op U))
    (x : X.complexPoints ρ) (hx : X.point x ∈ U) (hx' : X.point (X.conjPoint ρ x) ∈ U),
      norm ((starRingEnd ℂ).comp ρ) (X.conjPoint ρ x) (X.sectionValue _ hx' s) =
        norm ρ x (X.sectionValue x hx s)

structure HermitianLineBundle where

  L : X.X.Modules

  invertible : IsInvertibleSheaf L

  metric : X.ContinuousMetric L

end ProjScheme

namespace ComplexMetric

def ProjPointContinuous.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ) (ρ : A →+* ℂ),
    Continuous (projPoint ρ : CP N → projectiveSpace A N)

def FractionContinuous.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ) (ρ : A →+* ℂ) (d : ℕ)
    (a b : MvPolynomial (Fin (N + 1)) A), a ∈ ProjSpace.grading A N d →
      b ∈ ProjSpace.grading A N d →
        ContinuousOn (fun v : CP N => evalAt ρ v.rep a / evalAt ρ v.rep b)
          {v | evalAt ρ v.rep b ≠ 0}

def GermFraction.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ) (V : (projectiveSpace A N).Opens)
    (g : Γ(projectiveSpace A N, V)) (q : projectiveSpace A N), q ∈ V →
      ∃ (W : (projectiveSpace A N).Opens) (_ : q ∈ W) (hWV : W ≤ V) (d : ℕ)
        (a b : MvPolynomial (Fin (N + 1)) A), a ∈ ProjSpace.grading A N d ∧
          b ∈ ProjSpace.grading A N d ∧
          (∀ y : ProjectiveSpectrum (ProjSpace.grading A N), y ∈ W → b ∉ y.asHomogeneousIdeal) ∧
          ∀ (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (y : ProjectiveSpectrum (ProjSpace.grading A N))
            (hy : y ∈ W) (h : IsOver ρ w y),
              evalStalkProj h ((projectiveSpace A N).presheaf.germ V y (hWV hy) g) =
                evalAt ρ w a / evalAt ρ w b

def LocalLift.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ) (X : ProjScheme A N) (U : X.X.Opens) (f : ringOn X.X U)
    (p : X.X), p ∈ U →
      ∃ (V : (projectiveSpace A N).Opens) (g : Γ(projectiveSpace A N, V)) (W : X.X.Opens)
        (_ : p ∈ W) (hWU : W ≤ U) (hWV : W ≤ X.ι ⁻¹ᵁ V),
          ∀ (p' : X.X) (hp' : p' ∈ W),
            germR (hWU hp') f =
              (X.ι.stalkMap p').hom ((projectiveSpace A N).presheaf.germ V (X.ι.base p') (hWV hp') g)

def RegularContinuous.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N : ℕ) (X : ProjScheme A N) (ρ : A →+* ℂ) (U : X.X.Opens)
    (f : ringOn X.X U),
      Continuous fun y : {x : X.complexPoints ρ // X.point x ∈ U} =>
        X.evalAtPoint y.1 (germR y.2 f)

end ComplexMetric

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ} (X : ProjScheme A N) {ρ : A →+* ℂ}

def unitFibreEquiv (x : X.complexPoints ρ) : X.Fibre (𝟙_ X.X.Modules) x ≃ₗ[ℂ] ℂ :=
  fibreEquivComplex (X.evalAtPoint x) (show X.point x ∈ (⊤ : X.X.Opens) from trivial)
    (isBasisOn_one ⊤)

lemma unitFibreEquiv_sectionValue (x : X.complexPoints ρ) {U : X.X.Opens} (hx : X.point x ∈ U)
    (s : ((preMod X.X).obj (𝟙_ X.X.Modules)).obj (op U)) :
    X.unitFibreEquiv x (X.sectionValue x hx s) =
      X.evalAtPoint x (germR hx (show ringOn X.X U from s)) := by
  have h1 : resM ((preMod X.X).obj (𝟙_ X.X.Modules)) le_top (1 : ringOn X.X ⊤) =
      (1 : ringOn X.X U) := map_one (resR le_top)
  have e1 : s = (show ringOn X.X U from s) •
      resM ((preMod X.X).obj (𝟙_ X.X.Modules)) le_top (1 : ringOn X.X ⊤) := by
    rw [h1]
    exact (mul_one (show ringOn X.X U from s)).symm
  have hg : germM (L := 𝟙_ X.X.Modules) hx s =
      germR hx (show ringOn X.X U from s) •
        germM (L := 𝟙_ X.X.Modules) (show X.point x ∈ (⊤ : X.X.Opens) from trivial)
          (1 : ringOn X.X ⊤) := by
    conv_lhs => rw [e1]
    rw [germM_smul]
    congr 1
    exact germM_resM (L := 𝟙_ X.X.Modules) le_top hx _
  have key := fibreEquiv_fibreMk (φ := X.evalAtPoint x)
    (show X.point x ∈ (⊤ : X.X.Opens) from trivial) (isBasisOn_one ⊤) 1
    (germR hx (show ringOn X.X U from s))
  change (Via.ofComplex (X.evalAtPoint x)).symm (fibreEquiv (X.evalAtPoint x) _ (isBasisOn_one ⊤)
    (fibreMk _ _ 1 (germM hx s))) = _
  rw [hg, key, mul_one, RingEquiv.symm_apply_apply]

def standardMetric (hreg : ComplexMetric.RegularContinuous.Statement.{u}) :
    X.ContinuousMetric (𝟙_ X.X.Modules) where
  norm ρ x s := ‖X.unitFibreEquiv x s‖
  norm_smul ρ x c s := by rw [LinearEquiv.map_smul, smul_eq_mul, norm_mul]
  norm_pos ρ x s hs := norm_pos_iff.mpr (by
    intro h0
    exact hs ((X.unitFibreEquiv x).map_eq_zero_iff.mp h0))
  continuous_frame ρ U e _ := by
    have : (fun y : {x : X.complexPoints ρ // X.point x ∈ U} =>
        ‖X.unitFibreEquiv y.1 (X.sectionValue y.1 y.2 e)‖) =
        fun y => ‖X.evalAtPoint y.1 (germR y.2 (show ringOn X.X U from e))‖ := by
      funext y
      rw [unitFibreEquiv_sectionValue]
    exact this ▸ continuous_norm.comp (hreg A N X ρ U e)
  norm_conj ρ U s x hx hx' := by
    rw [unitFibreEquiv_sectionValue, unitFibreEquiv_sectionValue,
      X.evalAtPoint_conjPoint_germ x hx hx', Complex.norm_conj]

def trivialBundle (hreg : ComplexMetric.RegularContinuous.Statement.{u}) : X.HermitianLineBundle where
  L := 𝟙_ X.X.Modules
  invertible := isInvertibleSheaf_unit
  metric := X.standardMetric hreg

end ProjScheme

end

end GroundTheory.Heights₂.Heights
