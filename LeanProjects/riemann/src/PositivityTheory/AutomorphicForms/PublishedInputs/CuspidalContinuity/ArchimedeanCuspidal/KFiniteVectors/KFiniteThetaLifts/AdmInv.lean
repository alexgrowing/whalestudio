import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.QuadraticBaseChangeGL3Statement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable {K : Type} [Field K] [NumberField K]

structure Pk (DK : DatK K) (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (S : Finset (PlK K)) (I Z Id Zd : ℂ → ℂ) : Prop where
  dI : Differentiable ℂ I
  oI : Ord I (1 / 3)
  eu : ∀ s : ℂ, 1 < s.re → I s = Z s * eulK DK c S s
  nZ : ∀ s : ℂ, 1 / 4 < s.re → Z s ≠ 0
  dZ : DifferentiableOn ℂ (fun s => (Z s)⁻¹) {s | 1 / 4 < s.re}
  oZ : Ord (fun s => (Z s)⁻¹) (1 / 3)
  dId : DifferentiableOn ℂ Id {s | 1 / 4 < s.re}
  dZd : DifferentiableOn ℂ Zd {s | 1 / 4 < s.re}
  eud : ∀ s : ℂ, 1 < s.re → Id s = Zd s * eulK DK c⁻¹ S s
  fe : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → I s = Id (1 - s)
  lfe : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → Zd (1 - s) = gamSK DK c n t S s * Z s

variable (K) in

def AdmInv : Prop := ∀ (DK : DatK K) c n t S, AdmK DK c n t S → AdmK DK c⁻¹ (-n) (-t) S

variable (K) in

def Asm2 : Prop :=
  ∀ DK : DatK K, (∀ c n t S, AdmK DK c n t S → AdmK DK c⁻¹ (-n) (-t) S) →
    (∀ c n t S, AdmK DK c n t S → ∃ I Z Id Zd, Pk DK c n t S I Z Id Zd) → AnK DK

def pK (w : PlK K) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def Satd (S : Finset (PlK K)) : Prop := ∀ w ∈ S, ∀ w' : PlK K, pK w' = pK w → w' ∈ S

variable (K) in

def SatEx : Prop := ∀ S : Finset (PlK K), ∃ S', S ⊆ S' ∧ Satd S'

variable (K) in

def Sat : Prop :=
  ∀ (DK : DatK K) c n t (S S' : Finset (PlK K)), AdmK DK c n t S → S ⊆ S' →
    ∀ I Z Id Zd, Pk DK c n t S' I Z Id Zd → ∃ Z₁ Zd₁, Pk DK c n t S I Z₁ Id Zd₁

variable (K) in

def Out2 : Prop :=
  Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (D : Dat) (L : GP.Loc D), Explicit D L → ∀ hV : WhA (GP.VA L),
    QOut D (GP.VA L) hV → ∃ DK : DatK K, DK.k = D.k ∧ BCOf D DK ∧
      ∀ c n t S, AdmK DK c n t S → Satd S → ∃ I Z Id Zd, Pk DK c n t S I Z Id Zd

end Ad3.K.QuadraticBaseChangeGL3
