import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBaseModelSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimeToPartLevelExistsUniqueMono
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelRaises

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.SystemAmple

theorem exists_system_ampFrames : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → Out.Laws3 → TopAmpExists → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), 1 ≤ D.p + D.q → ToroidalLevelCompatibility (H := H) (D := D) → ∃ S : System Xo, ∀ i, ∃ k : ℕ, Nonempty (GlobalTheory.LN.AmpFrames (S.T i).t.G (S.T i).t.PP.L ((S.n i ^ k) ^ 2)) := by
  intro hx h1 h2 h3 htop E _ _ _ H D Xo hpq hN
  classical
  obtain ⟨⟨n₀, n₁, a₀, a₁, hne⟩, -⟩ := GlobalTheory.Models.exists_two_auxiliary_inert_odd_primes_coprime_level E H
  let n : Bool → ℕ := fun i => cond i n₁ n₀
  have aux : ∀ i, AuxiliaryInertOddPrime H (n i) := fun i => by cases i <;> assumption
  choose J k T hJ hamp using fun i => htop E H D hpq Xo (n i) (aux i)
  let B : ∀ i (l₀ : Level H), l₀.A = 1 → BaseModel (T i) l₀ := fun i l₀ h =>
    (GlobalTheory.T.exists_base_model_semiAbelian hx h1 h2 h3 E H D Xo hpq hN (n i) (J i) (T i) l₀ (aux i) (hJ i) h).some
  let ch : ℕ → Bool := fun p => decide (n₀ = p)
  have ch_ne : ∀ p, n (ch p) ≠ p := by
    intro p
    by_cases h : n₀ = p
    · have : ch p = true := by simp [ch, h]
      rw [this]
      exact fun h' => hne (h.trans h'.symm)
    · have : ch p = false := by simp [ch, h]
      rw [this]
      exact h
  have key : ∀ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (i : Idx H p),
      ∃ Y : Model (Xo i.l) i.c (i.c.V W).subtype, ∃ (l₀ : Level H) (h : IsPrimeToPart l₀ i.l p),
        Raises (B (ch p) l₀ h.1) Y := by
    intro p W hp hW i
    obtain ⟨hex, hsp, -⟩ := GlobalTheory.Models.primeToPart_spec E H p hp
    obtain ⟨l₀, h⟩ := hex i.l i.good
    obtain ⟨hdvd, hcop, -⟩ := hsp i.l l₀ h
    obtain ⟨hded, -, hb⟩ := (GlobalTheory.CoeffRings.coeff_isDedFrac E H i.l i.c).2.2.2 p W hp hW
    have hnp : (n (ch p)).Coprime p := (Nat.coprime_primes (aux _).1 hp).2 (ch_ne p)
    have hz : zeta 1 ∈ i.c.F := by
      have : zeta 1 = 1 := by simp [zeta]
      rw [this]; exact one_mem _
    obtain ⟨b, hbi⟩ := hb (n (ch p) * l₀.M) 1 (Nat.Coprime.mul_left hnp hcop) one_pos hz
    obtain ⟨Y, hY⟩ := GlobalTheory.LocalModelExists.exists_model_raises h1 h2 h3 E H D Xo _ _ (T (ch p)) hN l₀ i.l
      (B (ch p) l₀ h.1) i.c _ (i.c.V W).subtype b (aux _).1.pos hdvd hded hbi
    exact ⟨Y, l₀, h, hY⟩
  choose Y hY using key
  exact ⟨⟨n, J, aux, hJ, T, B, ch, ch_ne, Y, hY⟩, fun i => ⟨k i, hamp i⟩⟩

end GlobalTheory.SystemAmple
