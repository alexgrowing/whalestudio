import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem isLogEqn_changeForm_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = E.formOrd η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  intro X _ _ p _ n hn Δ D η η' x m mD l gG fD g a F A δ t hη' hηF hm hmD hg hD hA
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'

  set gG' : X.functionFieldˣ := gG * F ^ (-(m : ℤ)) with hgG'
  have hord (E : DivOver p) : (E.ord gG' : ℚ) = E.ord gG - m * E.ord F := by
    rw [hgG', E.ord_mul, divOver_ord_zpow]
    push_cast
    ring
  have h1 : IsLogEqn p Δ η' x m gG' := by
    intro z hz E hE
    have e := hg z hz E hE
    rw [hηF, E.formOrd_smul hn hη' F] at e
    rw [hord, ← e]
    push_cast
    ring
  have hd1 (E : DivOver p) : discrep E η' m gG' = E.formOrd η' + E.ord F - E.ord gG / m := by
    rw [discrep, hord]
    field_simp
    ring

  obtain ⟨m₁, g₁, hm₁, h2, hd2⟩ := isLogEqn_add_smul X p n Δ D η' x m mD gG' fD (1 - δ) hm hmD h1 hD

  have hB : (CartierDiv.principal g + l • A).IsEqn x (g * a ^ l) :=
    (CartierDiv.isEqn_principal g x).add (hA.nsmul l)
  obtain ⟨V, hxV, hV⟩ := hB.exists_nhds
  have hD' : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal g + l • A) 1 z = (E.ord (g * a ^ l) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    rw [qWeil, (hV z (hz.mem_open V.isOpen hxV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, h3, hd3⟩ := isLogEqn_add_smul X p n (Δ + (1 - δ) • D)
    (qWeil (CartierDiv.principal g + l • A) 1) η' x m₁ 1 g₁ (g * a ^ l) t hm₁ Nat.one_pos h2 hD'
  refine ⟨m₂, g₂, hm₂, h3, fun E => ?_⟩
  rw [hd3, hd2, hd1]
  push_cast
  ring

end GlobalTheory.PairStep
