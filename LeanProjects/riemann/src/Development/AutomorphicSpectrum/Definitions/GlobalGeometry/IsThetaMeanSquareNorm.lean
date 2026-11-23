import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def TorsVal (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G)
    (N : ℕ) (T : F) : Prop :=
  1 ≤ N ∧ y ^ N = 1 ∧
  ∃ (w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]))
    (i₀ i : P.L.ι), w.IsGen ∧ ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ P.L.U i₀ ∧ ⊤ ≤ y.left ⁻¹ᵁ P.L.U i ∧
    T * (valF (1 : Over.mk b ⟶ G).left _ (w.s ![i₀, i₀]).val *
        valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y.left _ (s.f fun _ => i) ^ (N ^ 2) * valF y.left _ (w.s ![i₀, i]).val ^ n

structure ArchFrame (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ G.left
  cart : IsGrpPullback A G z φ

  u : HolUnif A (P.L.pull φ) g

  Hm : Matrix (Fin g) (Fin g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ
  rig : ∀ i : P.L.ι, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
    u.fr (fun _ => i) 0 = valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val

attribute [instance] ArchFrame.grp

namespace ArchFrame

variable {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g)

def pt (w : Fin g → ℂ) : Sp ℂ ⟶ G.left := (a.u.ex w).left ≫ a.φ

def IsFn {n : ℕ} (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : P.L.ι) (w : Fin g → ℂ), ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i →
    valF (a.pt w) _ (s.f fun _ => i) = θ w * a.u.fr (fun _ => i) w ^ n

def herm (w w' : Fin g → ℂ) : ℂ := w ⬝ᵥ a.Hm.mulVec (star w')

def nrm (n : ℕ) (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) : ℝ :=
  ‖θ w‖ * Real.exp (-(Real.pi * n / 2) * (a.herm w w).re)

def IsTheta (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : a.u.Λ) (w : Fin g → ℂ),
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w

def IsThetaMeanSquareNorm (θ : (Fin g → ℂ) → ℂ) (b : ℝ) : Prop :=
  0 < b ∧ ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain a.u.Λ Fd volume →
    b ^ 2 = (∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal

def IsTan (c : Fin g → ℂ) (v : epsAt z ⟶ G) : Prop :=
  ∃ v' : epsR ℂ ⟶ a.A, v'.left ≫ a.φ = v.left ∧ a.u.IsDiff c v'

end ArchFrame

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure PPData (H : Host E) (L : Type) [Field L] [NumberField L] where

  t : SAB H (Sp (𝓞 L))

  tK : SAB H (Sp L)
  m : SABMap tK t (spMap (algebraMap (𝓞 L) L))
  princ : IsPrincipal tK

  B : HermitianBundle.{0} L
  MB : LieModel t.G (𝟙 _) B.carrier
  fib : IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB

abbrev emb {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) : Sp ℂ ⟶ Sp (𝓞 L) :=
  spMap (σ.comp (algebraMap (𝓞 L) L))

def mean (L : Type) [Field L] [NumberField L] (f : (L →+* ℂ) → ℝ) : ℝ := (∑ σ : L →+* ℂ, f σ) / Module.finrank ℚ L

namespace PPData

variable {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L)

def g : ℕ := Module.finrank (𝓞 L) D.B.carrier

def hp : ℝ := max (-D.B.normDegree ⊤) 0

abbrev Frame (σ : L →+* ℂ) := ArchFrame D.t.PP (emb σ) D.g

def len (σ : L →+* ℂ) (x : D.B.carrier) : ℝ :=
  Real.sqrt ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ).re

def IsVec {σ : L →+* ℂ} (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ) : Prop :=
  ∃ v : epsAt (emb σ) ⟶ D.t.G, D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) x v ∧ a.IsTan c v

abbrev Ext {L' : Type} [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') :=
  SABMap D'.t D.t (spMap (algebraMap (𝓞 L) (𝓞 L')))

def HasTheta (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) : Prop :=
  ∃ b : (L →+* ℂ) → ℝ, (∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn th θ → a.IsThetaMeanSquareNorm θ (b σ)) ∧
    mean L (fun σ => Real.log (b σ)) ≤ Φ

def SupLe {n : ℕ} (s : Out.H0 D.t.PP.L n) (M : (L →+* ℂ) → ℝ) : Prop :=
  ∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn s θ → ∀ w, a.nrm n θ w ≤ M σ

end PPData

def KeyDegSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L), 1 ≤ D.g →
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D')
      (th : Out.H0 D'.t.PP.L 1), D'.HasTheta th (D.hp / 2 + C * D.g)

def LineSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L) (x : D.B.carrier), x ≠ 0 →
    -mean L (fun σ => Real.log (D.len σ x)) ≤ C * Real.log (2 + D.g + D.hp)

end GlobalTheory.CompanionTheory.Ar.Sl
