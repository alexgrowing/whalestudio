import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace Formalism.L2.Ker.I3.JetMomA

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def SplitK (D : D7) (q : ℕ) : Prop := q = 2 ∨ jacobiSym (-(D.host.d : ℤ)) q = 1

def vecZ (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (q n : ℕ) [Fact q.Prime]
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[q]) : VC D N N' :=
  δ • embV D T (∑ i, (((PadicInt.toZModPow n (a i)).val : ℕ) : D.host.E) • b i)

abbrev Meas (q r : ℕ) [Fact q.Prime] : Type := C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]

section Stmts

variable (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ) (q : ℕ) [Fact q.Prime]
  (lam : Qbar →+* ℂ_[q])

def IntSplit : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[q], IsComb D B.tor (B.eNat χ) lam L L' F →
      (∀ (C : WeierstrassCurve.VariableChange ℂ_[q]) (wq : PowerSeries ℂ_[q]) (r : ℕ)
          (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        IsModel lam B.tor.abelian₂ C → IsWq (C • wModel lam B.tor.abelian₂) wq → LocBasis D q (YYl D L L') b →
        IntegralMv (atLog D lam B.tor.abelian₂ C wq b F)) ∧
      JetsInt D lam (YYl D L L') F

variable {D cc δ q} (Ω : ℂ_[q]) {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
  (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (μ : Meas q r)

def MomE : Prop :=
  ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
    (∀ a, g a = ∏ j, pairN D lam Ω b (y j) a) →
    jet D lam y (pSer D lam (B.eNat χ N N' L L')) = μ g

def TranslateJetMomentLaw : Prop :=
  ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε → ∀ yt : Fin r → Fin (q ^ n),
    ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (kap D B.tor (vecZ D B.tor δ q n b a) (liftY D B.tor δ q n ε b yt)) *
        ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (Wop D B.tor q (liftY D B.tor δ q n ε b yt) (B.eNat χ N N' L L'))) = μ g

def LocallyConstantJetMomentLaw : Prop :=
  ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε →
    ∀ Φ : LocallyConstant (Fin r → ℤ_[q]) ℂ, (∀ a, Φ a ∈ Qbar) → FactorsMod n Φ →
    ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[q], ℂ_[q])),
      (∀ a, g a = lamC lam (Φ a) * ∏ j, pairN D lam Ω b (y j) a) →
      jet D lam y (pSer D lam (XiF D B.tor δ q n ε b Φ (B.eNat χ N N' L L'))) = μ g

open Classical in

def MomentLawUnderBasisChange : Prop :=
  ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (r : ℕ) (b b₁ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Fin r → Fin r → D.host.K),
    admitted D N N' L L' → admitted D N N' L₁ L₂ → EqAway D q L L₁ → EqAway D q L' L₂ →
    NNBasis D B.tor δ q L L' b → NNBasis D B.tor δ q L₁ L₂ b₁ →
    (∀ j, b j = ∑ i, ((c i j : D.host.K) : D.host.E) • b₁ i) →
    (∀ i j, IsIntP (lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E))))) →
    ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[q]) ℂ), IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ →
      (∀ a, Φ a = if ∃ x : Fin r → ℤ_[q], ∀ i, zc (a i) =
          ∑ j, lamC lam (D.host.φ₀ (D.host.conj ((c i j : D.host.K) : D.host.E))) * zc (x j) then 1 else 0) →
      ∃ κ : ℂ, κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 ∧
        XiF D B.tor δ q n ε b₁ Φ (B.eNat χ N N' L₁ L₂) = fun z => κ * B.eNat χ N N' L L' z

variable (D cc δ q)

def MomSplit : Prop :=
  ∃ Ω : ℂ_[q], IsOmP lam B.tor.abelian₂ Ω ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D B.tor δ q L L' b →
      ∃ μ : Meas q r, ‖μ‖ ≤ 1 ∧ MomE B χ lam Ω L L' b μ ∧ TranslateJetMomentLaw B χ lam Ω L L' b μ ∧ LocallyConstantJetMomentLaw B χ lam Ω L L' b μ

end Stmts

def JetMomT : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (q : ℕ) [Fact q.Prime], SplitK D q → Nat.Coprime (Ideal.absNorm cc) q →
    ∀ lam : Qbar →+* ℂ_[q],
      IntSplit D cc δ B χ q lam ∧ MomSplit D cc δ B χ q lam ∧ MomentLawUnderBasisChange B χ lam

end Formalism.L2.Ker.I3.JetMomA
