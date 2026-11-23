import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

def KroneckerLimit : Prop :=
  ∀ τ : ℂ, 0 < τ.im → ∃ C ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 1 < s → s < 1 + ε →
    |(∑' p : ℤ × ℤ, if p = 0 then (0 : ℝ) else τ.im ^ s / ‖(p.1 : ℂ) * τ + (p.2 : ℂ)‖ ^ (2 * s))
        - Real.pi / (s - 1)
        - 2 * Real.pi * (Real.eulerMascheroniConstant - Real.log 2
            - Real.log (Real.sqrt τ.im * ‖ModularForm.eta τ‖ ^ 2))| ≤ C * (s - 1)

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤

def Uniformization : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 →
    (∃ Λ : AddSubgroup ℂ, IsLat Λ ∧ g2 Λ = a ∧ g3 Λ = b) ∧
    ∀ Λ Λ' : AddSubgroup ℂ, IsLat Λ → IsLat Λ' → g2 Λ = a → g3 Λ = b → g2 Λ' = a → g3 Λ' = b →
      Λ = Λ'

def jL (Λ : AddSubgroup ℂ) : ℂ := 1728 * g2 Λ ^ 3 / discr Λ

def CMTransitive (D : D7) : Prop :=
  (∀ σ : ℂ ≃+* ℂ, ∀ 𝔞 : Ideal (𝓞 D.host.K), 𝔞 ≠ ⊥ →
    ∃ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ ∧ σ (jL (lamOf D 𝔞 1)) = jL (lamOf D 𝔟 1)) ∧
  ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.K), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ →
    ∃ σ : ℂ ≃+* ℂ, (∀ x : D.host.K, σ (D.host.φ₀ (x : D.host.E)) = D.host.φ₀ (x : D.host.E)) ∧
      σ (jL (lamOf D 𝔞 1)) = jL (lamOf D 𝔟 1)

def CMConjEmb (D : D7) : Prop :=
  ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (𝔞 : Ideal (𝓞 D.host.K)), 𝔞 ≠ ⊥ →
    ∀ h : jL (lamOf D 𝔞 1) ∈ M,
      ∃ 𝔟 : Ideal (𝓞 D.host.K), 𝔟 ≠ ⊥ ∧ ρ ⟨jL (lamOf D 𝔞 1), h⟩ = jL (lamOf D 𝔟 1)

def DedekindFactor (D : D7) : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta D.host.K s =
      riemannZeta s * (haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
        DirichletCharacter.LFunction (chK D) s)

def ThetaNormIndependent (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')

def th22U (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L')

def LinkPer : Prop :=
  ∀ D : D7, KroneckerLimit → Uniformization → CMTransitive D → DedekindFactor D →
    ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      per22 D (tor0 D cc δ)

def LinkChi : Prop :=
  ∀ D : D7, AdmittedStatements D → ∃ χ, IsChi D χ

def LinkThU : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ N N' L L', admitted D N N' L L' → ∀ G ∈ Th D (tor0 D cc δ) L L', ∀ x : VC D N N',
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (U D (tor0 D cc δ) x G) =
        normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') G

def LinkThUFam : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ e : FamE D, vec22 D (tor0 D cc δ) e → th22U D (tor0 D cc δ) e

def LinkThIndep : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ → vec22 D (tor0 D cc δ) e →
      eq22 D (tor0 D cc δ) χ e → ThetaNormIndependent D (tor0 D cc δ) e

theorem theta_norm_independent_of_bounds (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) (h : th22 D T C e) :
    ThetaNormIndependent D T e := h.1

theorem theta_norm_unitary_invariant_of_bounds (D : D7) (T : Tor D) (C : ℝ) (e : FamE D) (h : th22 D T C e) :
    th22U D T e := h.2.2.2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
