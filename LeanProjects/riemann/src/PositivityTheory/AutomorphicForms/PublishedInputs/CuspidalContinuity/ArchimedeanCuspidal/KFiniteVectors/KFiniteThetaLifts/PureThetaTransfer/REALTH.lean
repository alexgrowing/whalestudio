import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.PureTh
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic ComplexConjugate
open scoped ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

def RWKF : Prop := GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  addCharConductor χ = 0 → residueCard E = residueCard F ^ 2 →
  ∀ k : Matrix (Fin 2) (Fin 2) F, k.det = 1 → (∀ i j, k i j ∈ 𝒪[F]) →
    GL2LocalData.rWE E χ σ η k (Set.indicator {x : E | x ∈ 𝒪[E]} 1) = Set.indicator {x : E | x ∈ 𝒪[E]} 1

def RWKS : Prop := GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ =>
  addCharConductor χ = 0 → ∀ k : Matrix (Fin 2) (Fin 2) F, k.det = 1 → (∀ i j, k i j ∈ 𝒪[F]) →
    GL2LocalData.rWS χ k (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) =
      Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1

def PIKF : Prop := GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  addCharConductor χ = 0 → residueCard E = residueCard F ^ 2 → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c →
  ∀ k ∈ GLnLocal.integralGL F 2, GL2LocalData.piE E χ σ η c k (Set.indicator {x : E | x ∈ 𝒪[E]} 1) =
    Set.indicator {x : E | x ∈ 𝒪[E]} 1

def PIKS : Prop := GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ =>
  addCharConductor χ = 0 → ∀ c₁ : Fˣ →* ℂˣ, IsUnramifiedChar c₁ →
  ∀ k ∈ GLnLocal.integralGL F 2, GL2LocalData.piS χ c₁ k (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1) =
    Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1

def NORMU : Prop := GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _χ _σ _η =>
  residueCard E = residueCard F ^ 2 → ∀ u : Fˣ, (u : F) ∈ 𝒪[F] → ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] →
    ∃ t : Eˣ, Algebra.norm F (t : E) = u

def LAMU : Prop := GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ _σ η =>
  addCharConductor χ = 0 → residueCard E = residueCard F ^ 2 → GL2LocalData.lamE E χ η = 1 ∧ GL2LocalData.nsg E (-1 : F) = 1

def SPHF : Prop := GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
  addCharConductor χ = 0 → residueCard E = residueCard F ^ 2 → ∀ c : Eˣ →* ℂˣ, IsUnramifiedChar c →
    SphN (GL2LocalData.WcE E χ σ η c (Set.indicator {x : E | x ∈ 𝒪[E]} 1))

def SPHS : Prop := GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ =>
  addCharConductor χ = 0 → ∀ c₁ c₂ : Fˣ →* ℂˣ, IsUnramifiedChar c₁ → IsUnramifiedChar c₂ →
    SphN (GL2LocalData.WcS χ c₁ c₂ (Set.indicator {x : F × F | x.1 ∈ 𝒪[F] ∧ x.2 ∈ 𝒪[F]} 1))

def sgR (a : ℝ) : ℂ := if 0 < a then 1 else -1

def rWR (a b c d : ℝ) (Φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if c = 0 then
    Complex.exp (2 * Real.pi * Complex.I * ((a * b * Complex.normSq z : ℝ) : ℂ)) * sgR a * ((|a| : ℝ) : ℂ) * Φ ((a : ℂ) * z)
  else Complex.I * sgR (-c) * ((|c|⁻¹ : ℝ) : ℂ) *
    ∫ u, Complex.exp (2 * Real.pi * Complex.I *
      (((a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c : ℝ) : ℂ)) * Φ u ∂volC

def rWRm (g : Matrix (Fin 2) (Fin 2) ℝ) : (ℂ → ℂ) → ℂ → ℂ := rWR (g 0 0) (g 0 1) (g 1 0) (g 1 1)

def SchC : Set (ℂ → ℂ) := {Φ | ∃ f : SchwartzMap ℂ ℂ, ⇑f = Φ}

def WcR (cf : ℂˣ → ℂ) (Φ : ℂ → ℂ) (g : GL (Fin 2) ℝ) : ℂ :=
  if h : 0 < (g.val).det then
    cf (Units.mk0 ((Real.sqrt (g.val).det : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr h).ne')) *
      ((Real.sqrt (g.val).det : ℝ) : ℂ) *
      rWR (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun y => Φ (y * ((Real.sqrt (g.val).det : ℝ) : ℂ))) 1
  else 0

def PhiInf (n : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ n then conj z ^ n.natAbs else z ^ n.natAbs) * Complex.exp (-2 * Real.pi * ((Complex.normSq z : ℝ) : ℂ))

def RWRREP : Prop := ∀ g h : Matrix (Fin 2) (Fin 2) ℝ, g.det = 1 → h.det = 1 → ∀ Φ ∈ SchC,
  rWRm h Φ ∈ SchC ∧ rWRm (g * h) Φ = rWRm g (rWRm h Φ)

def REALTH : Prop := ∀ (n : ℤ) (t : ℝ) (g : GL (Fin 2) ℝ), WcR (chC n (Complex.I * t)) (PhiInf n) g = thR n t g

def PHIISO : Prop := ∀ n : ℤ, PhiInf n ∈ SchC ∧ ∀ (z u : ℂ), ‖u‖ = 1 → PhiInf n (z * u) = u ^ (-n) * PhiInf n z

end Ad3.K.QuadraticBaseChangeGL3.Th
