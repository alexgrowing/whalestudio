import Formalism.LocalToGlobal.InertKernelTheory.StatementInt

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def IntS (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq → LocBasis D p (YYl D L L') b →
      Orthonormal D b →
      IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def IntSome (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b ∧ Orthonormal D b ∧
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq →
      IntegralMv (atLog D lam T.abelian₂ C wq b F * ePh lam T.abelian₂ C wq r)

def AlgEnt (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : Prop :=
  AnalyticOnNhd ℂ G Set.univ ∧ ∀ α : Mono D N N', taylor D G α ∈ Qbar

def tPull (D : D7) (T : Tor D) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') : VC D N N' :=
  fun τ => (Matrix.conjTranspose (γ'.map (T.emb τ)) * (Matrix.of (z τ)) * γ.map (T.emb τ) : Matrix _ _ ℂ)

def CombFact : Prop :=
  ∀ (D : D7) (T : Tor D) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (m : ℕ) (r : Fin m → ℂ_[p]) (F : Fin m → MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
    (∀ k, IsIntP (r k)) → (∀ k, IntS D T p lam L L' (F k)) →
    IntS D T p lam L L' (∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (r k) * F k)

def PairFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (N N' : ℕ)
    (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    EqAt D p L L₁ → EqAt D p L' L₁' →
      (∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
        LocBasis D p (YYl D L L') b → LocBasis D p (YYl D L₁ L₁') b) ∧
      (∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t → TorsPrime D p (La D (tor0 D cc δ) L₁ L₁') t)

def WeakApprox : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' →
    letI := D.host.cmStar
    ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' M M' ∧ EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M ∧ EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M' ∧
      L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧
      L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'

def PullTors : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (N N' : ℕ),
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (t : VC D N N'),
      TorsPrime D p (La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')) t →
      TorsPrime D p (La D (tor0 D cc δ) M M')
        (tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t)

def PullFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ),
    letI := D.host.cmStar
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (t : VC D N N') (G : VC D N N' → ℂ),
      AlgEnt D (U D (tor0 D cc δ) (tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) t) G) →
      IntS D (tor0 D cc δ) p lam M M' (pSer D lam (U D (tor0 D cc δ) (tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) G)) →
      IntS D (tor0 D cc δ) p lam (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
        (pSer D lam (U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) G)))

def AlgFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ N N' : ℕ,
      (∀ (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
        admitted D N N' M M' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M' →
        ∀ t : VC D N N', TorsPrime D p (La D B.tor M M') t → AlgEnt D (U D B.tor t (B.eNat χ N N' M M'))) ∧
      (∀ s : VC D N N', TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
        AlgEnt D (U D B.tor s (B.thZero N N')))

def PSerLin : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' m : ℕ) (c : Fin m → ℂ) (G : Fin m → VC D N N' → ℂ),
    (∀ k, c k ∈ Qbar) → (∀ k, AlgEnt D (G k)) →
    pSer D lam (fun z => ∑ k, c k * G k z) =
      ∑ k, algebraMap ℂ_[p] (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (lamC lam (c k)) * pSer D lam (G k)

def StdStep : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ χ : IdE D → ℂ, IsChi D χ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' M M' → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N) M → EqAt D p (Formalism.MainNotions.StandardLatticesGL3.stdL D N') M' →
      ∀ t : VC D N N', TorsPrime D p (La D B.tor M M') t →
      ∃ (m : ℕ) (c : Fin m → ℂ) (s : Fin m → VC D N N'),
        (∀ k, c k ∈ Qbar ∧ IsIntP (lamC lam (c k))) ∧
        (∀ k, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (s k)) ∧
        U D B.tor t (B.eNat χ N N' M M') = fun z => ∑ k, c k * U D B.tor (s k) (B.thZero N N') z

def BasisInv : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 →
    ∀ (lam : Qbar →+* ℂ_[p]) (N N' : ℕ)
      (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      IntSome D (tor0 D cc δ) p lam L L' F → IntS D (tor0 D cc δ) p lam L L' F

def TensFact : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    (∀ s : VC D 2 2, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) s →
      AlgEnt D (U D B.tor s (B.thZero 2 2)) ∧
      IntSome D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (pSer D lam (U D B.tor s (B.thZero 2 2))) ∧
      IntS D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (pSer D lam (U D B.tor s (B.thZero 2 2)))) →
    ∀ (N N' : ℕ), Even N → Even N' →
    ∀ s : VC D N N', TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) s →
      IntSome D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') (pSer D lam (U D B.tor s (B.thZero N N')))

def ThFourInt : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → ∀ lam : Qbar →+* ℂ_[p],
    ∀ s : VC D 2 2, TorsPrime D p (La D B.tor (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) s →
      IntSome D B.tor p lam (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (pSer D lam (U D B.tor s (B.thZero 2 2)))

end Formalism.L2.KerInert
