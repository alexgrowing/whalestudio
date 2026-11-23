import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def OneAt (D : D7) (p : ℕ) (𝔞 : IdE D) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (∀ x ∈ 𝔞, (s : D.host.E) * x ∈ (1 : IdE D)) ∧ (s : D.host.E) ∈ 𝔞

def LemmaU (D : D7) : Prop :=
  ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (𝔞 : IdE D),
    N1 D 𝔞 → OneAt D p 𝔞 → χ 𝔞 ∈ Qbar ∧ ‖lamC lam (χ 𝔞)‖ = 1

def DetOneAt (D : D7) : Prop :=
  ∀ (p N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L → OneAt D p (detId D (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L)

def ChiFacUnit (D : D7) : Prop :=
  ∀ χ : IdE D → ℂ, IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L' →
      Base.chiFac χ N N' L L' ∈ Qbar ∧ ‖lamC lam (Base.chiFac χ N N' L L')‖ = 1

def IntAway (D : D7) (T : Tor D) (e : FamE D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        Orthonormal D b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)) ∧
      JetsInt D lam (YYl D L L') F ∧
      ((p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) →
        ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
        IntegralMv (atLog D lam T.abelian₂ C wq b F))

def IntAtD (D : D7) (T : Tor D) (e : FamE D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop :=
  ∃ S : ℂ_[p], ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) ∧
    ∃ u : D.what₂.Tau → ℂ_[p], (∀ τ, ‖u τ‖ = 1) ∧ (∀ τ, u (tauSg D τ) = u τ) ∧
      ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
        (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
      (∀ τ, LocBasisW D (tauEmb D lam τ) L (P τ)) → (∀ τ, LocBasisW D (tauEmb D lam τ) L' (P' τ)) →
      DualB D P → DualB D P' →
      ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
      ∃ F₀, F = expMv (-(algebraMap ℂ_[p] _ S) * QdB D lam u P P') * F₀ ∧
        JetsInt D lam (YYl D L L') F₀

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
