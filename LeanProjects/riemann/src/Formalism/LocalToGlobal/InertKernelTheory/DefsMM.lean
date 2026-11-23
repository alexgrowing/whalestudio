import Formalism.LocalToGlobal.InertKernelTheory.DefsInt

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def atLogV (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (v : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p])) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  let W := C • wModel lam Λ
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
      PowerSeries.subst (MvPowerSeries.X i) (flog W wq)) F

def IntLocV (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (v : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p])) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq →
    IntegralMv (atLogV D lam T.abelian₂ C wq v F * ePh lam T.abelian₂ C wq r)

def IsConjP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : ℂ_[p] →+* ℂ_[p]) : Prop :=
  (∀ x : D.host.K, σ (lamC lam (D.host.φ₀ (x : D.host.E))) = lamC lam (D.host.φ₀ (D.host.conj (x : D.host.E)))) ∧
  ∀ y : ℂ_[p], ‖σ y‖ = ‖y‖

def IsLocONB (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (σ : ℂ_[p] →+* ℂ_[p]) {r : ℕ}
    (v : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p])) : Prop :=
  ∃ (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (A : Matrix (Fin r) (Fin r) ℂ_[p]),
    LocBasis D p Y b ∧
    (∀ i j, IsIntP (A i j) ∧
      A i j ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E)))) ∧
    ‖A.det‖ = 1 ∧
    (∀ i j, ∑ m, ∑ n, A i m * lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E)) * σ (A j n) =
      if i = j then 1 else 0) ∧
    ∀ i k, v i k = ∑ m, A i m * lamC lam (embT D k.1 (b m k.2.1 k.2.2))

def OneCopyLoc : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∃ (σ : ℂ_[p] →+* ℂ_[p]) (r : ℕ) (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p])),
      IsConjP D lam σ ∧ IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v ∧
      ∀ s : VC D 1 1, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) s →
        IntLocV D B.tor p lam v (pSer D lam (U D B.tor s (B.thZero 1 1)))

def LocInv : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (σ : ℂ_[p] →+* ℂ_[p]), IsConjP D lam σ →
    ∀ (N N' : ℕ) (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (r r' : ℕ)
      (v : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p])) (v' : Fin r' → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
      (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      IsLocONB D p lam Y σ v → IsLocONB D p lam Y σ v' →
      IntLocV D (tor0 D cc δ) p lam v F → IntLocV D (tor0 D cc δ) p lam v' F

def FourProd : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (σ : ℂ_[p] →+* ℂ_[p]) (r : ℕ) (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p])),
      IsConjP D lam σ → IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v →
      (∀ s : VC D 1 1, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) s →
        AlgEnt D (U D B.tor s (B.thZero 1 1)) ∧ IntLocV D B.tor p lam v (pSer D lam (U D B.tor s (B.thZero 1 1)))) →
      ∃ (r₄ : ℕ) (v₄ : Fin r₄ → (D.what₂.Tau × Fin 2 × Fin 2 → ℂ_[p])),
        IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) σ v₄ ∧
        ∀ s : VC D 2 2, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) s →
          IntLocV D B.tor p lam v₄ (pSer D lam (U D B.tor s (B.thZero 2 2)))

def GlobONB : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∃ (r : ℕ) (b : Fin r → Matrix (Fin 2) (Fin 2) D.host.E),
      LocBasis D p (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) b ∧ Orthonormal D b ∧
      ∀ σ : ℂ_[p] →+* ℂ_[p], IsConjP D lam σ →
        IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) σ
          (fun i k => lamC lam (embT D k.1 (b i k.2.1 k.2.2)))

def AlgZero : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ (N N' : ℕ) (s : VC D N N'),
      TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
      AlgEnt D (U D B.tor s (B.thZero N N'))

end Formalism.L2.KerInert
