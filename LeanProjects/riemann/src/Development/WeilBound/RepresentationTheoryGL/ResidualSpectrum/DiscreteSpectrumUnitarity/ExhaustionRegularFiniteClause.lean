import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.CuspDiscrete
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.BaseChangeSpehOfDiscreteSeries

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs

def ExhaustionRegularFiniteClause : Prop :=
  ExhReg ∧ ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → PositivityTheory.RSHS.Clause3 E N

def UsedReg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a : ℕ) (π : CuspSub E a), a = N → IsNormalised π →
      ∃ V : Submodule ℂ (Sm E N), IsDiscrete V ∧ IsSpehOf V π 1) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → HasSpehComp V π d

namespace Re

open GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (E) in

def DiscreteSpectrumReg (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ τ, RegInt V τ →
    ∃ (a d : ℕ) (h : ∑ _ : Fin d, a = N) (P : CuspSub E a), (IsCsdGL V → P.IsCsd) ∧
      (∀ w σ', IsLocCompGL V w σ' → GlobalTheory.SmGL.IsUnitarisable σ'.ρ ∧
        ∃ σ, P.IsLocComp w σ ∧ GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ IsSpehQuot h σ σ') ∧
      ∀ τ m', HasInfCharGL V τ m' → ∃ m, P.HasInfChar τ m ∧ m' = spehInf d m

theorem regInt_of_le {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} {V : Submodule ℂ (Sm E N)}
    {τ : E →+* ℂ} {m M : Multiset ℂ} (hV : HasInfCharGL V τ m) (hle : m ≤ M) (hM : M.Nodup)
    (hint : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, x - y = n) : RegInt V τ :=
  ⟨m, hV, Multiset.nodup_of_le hle hM, fun x hx y hy => hint x (Multiset.mem_of_le hle hx) y (Multiset.mem_of_le hle hy)⟩

theorem infOfWeight_int {n : ℕ} (lam : Formalism.BasicNotions.DomWeight n) :
    ∀ x ∈ infOfWeight lam, ∀ y ∈ infOfWeight lam, ∃ k : ℤ, x - y = k := by
  have key : ∀ z ∈ infOfWeight lam, ∃ k : ℤ, z = ((n : ℂ) - 1) / 2 + k := fun z hz => by
    obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨lam.w k - (k : ℕ), by push_cast; ring⟩
  intro x hx y hy
  obtain ⟨k, rfl⟩ := key x hx
  obtain ⟨l, rfl⟩ := key y hy
  exact ⟨k - l, by push_cast; ring⟩

end Re

end PositivityTheory.Rg.Rs

end
