import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.FormalGroupJets
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.GlobalSchurBounds.StatementFamilyConstant

noncomputable section

namespace Formalism.MainNotions.GL3r7

section A

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def thTwo (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (ω₁ τ : ℂ), 0 < τ.im → lamOf D cc δ = AddSubgroup.closure {ω₁, ω₁ * τ} →
    ∀ a b : ℕ, a ≤ 1 → b ≤ 1 → IsTwoTorsionPointUnkilled D (lamOf D cc δ) (ω₁ * ((1 - (a : ℂ)) * τ + (1 - (b : ℂ))) / 2) →
    ∀ G, IsTheta0 D.host.d (lamOf D cc δ) G →
      (normSq1 (lamOf D cc δ) G)⁻¹ = Real.sqrt (2 * τ.im) *
        (Real.exp (-Real.pi * (a : ℝ) ^ 2 * τ.im / 4) * ‖jacobiTheta₂ (((a : ℂ) * τ + (b : ℂ)) / 2) τ‖) ^ 2

def thMean (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M →
    ∀ G : (M →ₐ[ℚ] ℂ) → ℂ → ℂ, (∀ ρ, IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (G ρ)) →
      (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (normSq1 (lamConj M ρ (lamOf D cc δ)) (G ρ))) / (Module.finrank ℚ M : ℝ) ≤
        (1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

def thSize (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ Lsc : ℝ, Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * Lsc →
    ∀ N N' L L', admitted D N N' L L' →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], DataIn D T M → CoefIn D (e N N' L L') M →
        meanLogNormSq D T L L' M (e N N' L L') ≤ (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc

def PhV {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι σ : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (w : ι → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) w)

def PhGram (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j, InOKp D g.lam (A j)) →
      Simeq (g.PhOn A)
        (∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * g.phAt (Xv j) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), g.be (g.mulBy (hP (A j) (A j')).1 (Xv j)) (Xv j'))

def sdL {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  g.PhOn (Sum.elim a a') - PhV g a (fun e => Xv (Sum.inl e)) - PhV g a' (fun e => Xv (Sum.inr e))

def sdR {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', g.be (g.mulBy (hP (a f) (a' f')).1 (Xv (Sum.inl f))) (Xv (Sum.inr f'))

def sdR' {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', g.be (Xv (Sum.inl f)) (g.mulBy (hP (a f) (a' f')).2 (Xv (Sum.inr f')))

def SDiff (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e, InOKp D g.lam (a e)) → (∀ e, InOKp D g.lam (a' e)) →
      Simeq (sdL g a a') (sdR g a a') ∧ Simeq (sdL g a a') (sdR' g a a')

def SDiffW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e, InOKp D g.lam (a e)) → (∀ e, InOKp D g.lam (a' e)) →
      CoefWf (sdL g a a') ∧ SimeqW (sdL g a a') (sdR g a a') ∧ SimeqW (sdL g a a') (sdR' g a a')

def FirstKernelRemainder (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (b b' : ι → κ → ℂ_[p] × ℂ_[p]) (b'' : ι' → κ → ℂ_[p] × ℂ_[p]),
      (∀ e, InOKp D g.lam (b e)) → (∀ e, InOKp D g.lam (b' e)) → (∀ e, InOKp D g.lam (b'' e)) → DualIso b b' →
      (∀ e f, hP (b e) (b'' f) = 0) → (∀ e f, hP (b' e) (b'' f) = 0) →
      CoefWf (g.PhOn (Sum.elim (Sum.elim b b') b'')) ∧
      SimeqW (g.PhOn (Sum.elim (Sum.elim b b') b''))
        (∑ e : ι, g.be (Xv (Sum.inl (Sum.inl e))) (Xv (Sum.inl (Sum.inr e))) + PhV g b'' (fun f => Xv (Sum.inr f)))

def coordO {p : ℕ} [Fact p.Prime] {μ κ ι : Type*} [Fintype μ] (o : κ → μ → ℂ_[p] × ℂ_[p]) (bs : ι → μ → ℂ_[p] × ℂ_[p]) :
    ι → κ → ℂ_[p] × ℂ_[p] := fun e k => hP (bs e) (o k)

def FirstKernelOrthogonal (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g → 5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : MvPowerSeries (Idx D N N') ℂ_[p]),
      admitted D N N' L L' → IsComb D (tor0 D cc δ) e g.lam L L' F →
      ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (o : κ → Idx D N N' → ℂ_[p] × ℂ_[p])
        (b b' : ι → Idx D N N' → ℂ_[p] × ℂ_[p]) (b'' : ι' → Idx D N N' → ℂ_[p] × ℂ_[p]),
        BasisP D g.lam (YYp D g.lam L L') o → (∀ i j, hP (o i) (o j) = if i = j then 1 else 0) →
        BasisP D g.lam (YYp D g.lam L L') (Sum.elim (Sum.elim b b') b'') → DualIso b b' →
        (∀ e f, hP (b e) (b'' f) = 0) → (∀ e f, hP (b' e) (b'' f) = 0) →
        IntegralMv (g.atLogP (Sum.elim (Sum.elim b b') b'') F * expMv (g.PhOn (coordO o (Sum.elim (Sum.elim b b') b'')))) ∧
        CoefWf (g.PhOn (coordO o (Sum.elim (Sum.elim b b') b''))) ∧
        SimeqW (g.PhOn (coordO o (Sum.elim (Sum.elim b b') b'')))
          (∑ e : ι, g.be (Xv (Sum.inl (Sum.inl e))) (Xv (Sum.inl (Sum.inr e))) +
            PhV g (coordO o b'') (fun f => Xv (Sum.inr f)))

def pairK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] × ℂ_[p] :=
  (tauK D lam a, tauKc D lam a)

def IntAtP (D : D7) (p : ℕ) (x : D.host.K) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : D.host.K) * x)

def IsGa4 (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' r : ℕ}
    (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (y : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K) : Prop :=
  LocBasis D p Y y ∧ (∀ i k, IntAtP D p (c i k)) ∧
  (∃ c' : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K, (∀ i k, IntAtP D p (c' i k)) ∧ c * c' = 1) ∧
  ∀ i j, hP (fun k => pairK D lam (c i k)) (fun k => pairK D lam (c j k)) =
    if i.1 = j.1 then pairK D lam (hYY D (y i.2) (y j.2)) else 0

def ePh4 (D : D7) {p : ℕ} [Fact p.Prime] (g : G1 p) {r : ℕ} (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  if p = 2 then 1 else expMv (g.PhOn (fun (i : Fin r) k => pairK D g.lam (c (0, i) k)))

def ser4 (D : D7) {p : ℕ} [Fact p.Prime] (g : G1 p) {N N' r : ℕ} (y : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K) (F : MvPowerSeries (Idx D N N') ℂ_[p]) : MvPowerSeries (Fin r) ℂ_[p] :=
  g.atLogP (fun i => embP D g.lam (y i)) F * ePh4 D g c

def GaussLe {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (B : ℝ) : Prop :=
  ∀ n, ‖MvPowerSeries.coeff n F‖ ≤ B

def Gauss1 {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  IntegralMv F ∧ ¬ ∃ ρ : ℝ, ρ < 1 ∧ GaussLe F ρ

def SelfDualPair (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) : Prop := StandardLatticesGL3.SD D L ∧ StandardLatticesGL3.SD D L'

def a2Ph (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      SelfDualPair D L L' → IsGa4 D g.lam (YYl D L L') y c → Orthonormal D y →
      Simeq (g.PhOn (fun (i : Fin r) k => pairK D g.lam (c (0, i) k))) (∑ i, g.phAt (Xv i))

def PhaseAwayFromTwo (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      SelfDualPair D L L' → IsGa4 D g.lam (YYl D L L') y c →
      ∀ (κ : Type) [Fintype κ] (o : κ → Idx D N N' → ℂ_[p] × ℂ_[p]), BasisP D g.lam (YYp D g.lam L L') o →
        (∀ i j, hP (o i) (o j) = if i = j then 1 else 0) →
        Simeq (g.PhOn (fun (i : Fin r) k => pairK D g.lam (c (0, i) k))) (g.PhOn (coordO o (fun i => embP D g.lam (y i))))

def ga4Ex (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SelfDualPair D L L' →
    ∃ (r : ℕ) (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      IsGa4 D lam (YYl D L L') y c

def IsSecP (D : D7) (T : Tor D) (p : ℕ) {N N' : ℕ} (La₀ : AddSubgroup (VC D N N')) (G : VC D N N' → ℂ) : Prop :=
  (∃ (La'' : AddSubgroup (VC D N N')) (n : ℕ), 0 < n ∧ Nat.Coprime n p ∧ La'' ≤ La₀ ∧ (∀ x ∈ La₀, n • x ∈ La'') ∧
    G ∈ ThSp D T La'') ∧ CoefIn D G Qbar

def NormA2Invariant (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      SelfDualPair D L L' → IsGa4 D g.lam (YYl D L L') y c →
      ∀ G, IsSecP D (tor0 D cc δ) p (La D (tor0 D cc δ) L L') G → G ≠ 0 →
        (∃ κ : ℂ, κ ∈ Qbar ∧ κ ≠ 0 ∧ Gauss1 (ser4 D g y c (pSer D g.lam (fun z => κ * G z)))) ∧
        ∀ (g' : G1 p) (y' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c' : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
          At D cc δ g' → g'.lam = g.lam → IsGa4 D g'.lam (YYl D L L') y' c' →
          ∀ B : ℝ, GaussLe (ser4 D g y c (pSer D g.lam G)) B ↔ GaussLe (ser4 D g' y' c' (pSer D g'.lam G)) B

def pdNorm (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      SelfDualPair D L L' → IsGa4 D g.lam (YYl D L L') y c →
      (∀ G, IsSecP D (tor0 D cc δ) p (La D (tor0 D cc δ) L L') G →
        ∀ t, TorsPrime D p (La D (tor0 D cc δ) L L') t → ∀ B : ℝ,
          GaussLe (ser4 D g y c (pSer D g.lam (U D (tor0 D cc δ) t G))) B ↔ GaussLe (ser4 D g y c (pSer D g.lam G)) B) ∧
      ∀ L₁ L₁', SelfDualPair D L₁ L₁' → EqAt D p L L₁ → EqAt D p L' L₁' →
        ∀ G ∈ Th D (tor0 D cc δ) L L', CoefIn D G Qbar → ∀ B : ℝ,
          GaussLe (ser4 D g y c (pSer D g.lam
            (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') G))) B ↔
          GaussLe (ser4 D g y c (pSer D g.lam G)) B

def enPrim (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K) (t : VC D N N'),
      admitted D N N' L L' → IsGa4 D g.lam (YYl D L L') y c → TorsPrime D p (La D (tor0 D cc δ) L L') t →
      Gauss1 (ser4 D g y c (pSer D g.lam (U D (tor0 D cc δ) t (e N N' L L'))))

def enMove (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → admitted D N N' L₁ L₁' → EqAt D p L L₁ → EqAt D p L' L₁' →
      ∃ u : ℂ, u ∈ Qbar ∧ ‖lamC lam u‖ = 1 ∧
        e N N' L₁ L₁' = fun z => u * Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (e N N' L L') z

def Le1 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (G : VC D N N' → ℂ) : Prop :=
  ∃ (g : G1 p) (r : ℕ) (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
    At D cc δ g ∧ g.lam = lam ∧ IsGa4 D g.lam (YYl D L L') y c ∧ IntegralMv (ser4 D g y c (pSer D g.lam G))

def CCterms (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) {m : ℕ}
    (t : Fin m → VC D N N') (G : Fin m → VC D N N' → ℂ) : Prop :=
  ∀ k, TorsPrime D p (La D (tor0 D cc δ) L L') (t k) ∧
    ∃ L₁ L₁', SelfDualPair D L₁ L₁' ∧ EqAt D p L L₁ ∧ EqAt D p L' L₁' ∧ G k ∈ Th D (tor0 D cc δ) L₁ L₁' ∧ CoefIn D (G k) Qbar ∧
      Le1 D cc δ lam L₁ L₁' (G k)

def CCp (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (F : MvPowerSeries (Idx D N N') ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (r : Fin m → ℂ_[p]) (t : Fin m → VC D N N') (G : Fin m → VC D N N' → ℂ),
    (∀ k, IsIntP (r k)) ∧ CCterms D cc δ lam L L' t G ∧
    F = ∑ k, algebraMap ℂ_[p] (MvPowerSeries (Idx D N N') ℂ_[p]) (r k) * pSer D lam (U D (tor0 D cc δ) (t k) (G k))

def genA (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (y : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      SelfDualPair D L L' → IsGa4 D g.lam (YYl D L L') y c →
      ∀ F, CCp D cc δ g.lam L L' F → IntegralMv (ser4 D g y c F)

def genInt (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      SelfDualPair D L L' → StandardLatticesGL3.IntAt D (tor0 D cc δ) lam L L' (CCp D cc δ lam L L')

def genMom (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), SelfDualPair D L L' →
      ∀ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → VC D N N') (G : Fin m → VC D N N' → ℂ),
        (∀ k, r k ∈ Qbar ∧ ‖lamC lam (r k)‖ ≤ 1) → CCterms D cc δ lam L L' t G →
        ∃ s : ℕ, 0 < s ∧ Nat.Coprime s p ∧
          ∀ (k : ℕ) (b : Fin k → Matrix (Fin N') (Fin N) D.host.E), NNBasis D (tor0 D cc δ) δ p L L' b →
            (∀ i, ∃ x ∈ La D (tor0 D cc δ) L L', δ • embV D (tor0 D cc δ) (b i) = s • x) →
            StandardLatticesGL3.MomAt D cc δ lam Ω b (fun z => ∑ i, r i * U D (tor0 D cc δ) (t i) (G i) z)

def genNat (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), Nat.Coprime (Ideal.absNorm cc) p →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L L' → ∀ F, IsComb D (tor0 D cc δ) e lam L L' F → CCp D cc δ lam L L' F

def genOdd (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : StandardLatticesGL3.WeilO D cc δ N N' e0) (S : Finset ℕ), (∀ q ∈ S, q.Prime ∧ AllSplit D q) →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → Nat.Coprime (Ideal.absNorm cc) p →
      ∀ F, StandardLatticesGL3.IsCombO D cc δ W S lam F → CCp D cc δ lam (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') F

def oddPrim (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : StandardLatticesGL3.WeilO D cc δ N N' e0) (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g →
    ∀ (a : StandardLatticesGL3.GA D N) (a' : StandardLatticesGL3.GA D N') (r : ℕ) (y : Fin r → Matrix (Fin N') (Fin N) D.host.E)
      (c : Matrix (Fin 4 × Fin r) (Fin 4 × Fin r) D.host.K),
      StandardLatticesGL3.TrivAt D p (a : GL (Fin N) (StandardLatticesGL3.AE D)) → StandardLatticesGL3.TrivAt D p (a' : GL (Fin N') (StandardLatticesGL3.AE D)) →
      IsGa4 D g.lam (YYl D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) y c →
      Gauss1 (ser4 D g y c (pSer D g.lam (W.Om a a' e0)))

def StrAt (D : D7) (T : Tor D) (e : FamE D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (ep c : ℂ_[p]) : Prop :=
  ∀ (d : ℕ) [NeZero d] (Po : Pos D p d) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E) (ϖ : ℂ_[p]),
    admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
    (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) →
    ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) →
    ∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], IsComb D T e lam L L' F →
    ∀ h' : {v // v ∈ Po.V} → MvPowerSeries (TVar D Po N N') ℂ_[p],
      (∀ v, ∃ G : MvPowerSeries (TVar D Po N N') ℂ_[p], IntegralMv G ∧ MvPowerSeries.constantCoeff G = 0 ∧
        h' v = hh D Po v (fun _ => c) + algebraMap ℂ_[p] _ (p : ℂ_[p]) * G) →
      InProd D Po h' (atLin (fun k j => ep * chg D lam Po P P' k j * ϖ)
        (fun j => MvPowerSeries.X j) F)

def strC (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → AllSplit D p →
    ∃ ep : ℂ_[p], InW ep ∧ ‖ep‖ = 1 ∧ ∃ c : ℂ_[p], InW c ∧ (c, -c) ∈ OKp D lam ∧ StrAt D T e lam ep c

def strTied (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g → 5 ≤ p → InertK D p → AllSplit D p →
    ModelOverW g.lam g.abelian₂ g.C →
    ∀ ep : ℂ_[p], ep ∈ Wp p → ‖ep‖ = 1 → IntegralW (g.thF ep () : MvPowerSeries Unit ℂ_[p]) →
    ∀ c : ℂ_[p], (c, -c) ∈ OKp D g.lam →
      SimeqW (g.be (g.thF ep 0) (g.thF ep 1) : MvPowerSeries (Fin 2) ℂ_[p]) (MvPowerSeries.C c * (serA p + serB p)) →
      StrAt D (tor0 D cc δ) e g.lam ep c

def sOne {σ : Type*} (p : ℕ) [Fact p.Prime] (j : σ) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ l ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if α = Finsupp.single j ((p ^ 2) ^ l) then (-1 : ℂ_[p]) ^ l else 0

def InProdG {σ V : Type*} [Fintype V] {p : ℕ} [Fact p.Prime] (h : V → MvPowerSeries σ ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∃ g : (V → ℕ) → MvPowerSeries σ ℂ_[p], (∀ i, IntegralMv (g i)) ∧
    ∀ α, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : V => Finset.range ((α.sum fun _ k => k) + 1)),
        MvPowerSeries.coeff α
          (algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (∏ v, ((p : ℂ_[p]) ^ i v)⁻¹) * (∏ v, h v ^ i v) * g i)

def hhB {V ι : Type*} [Fintype ι] (p : ℕ) [Fact p.Prime] (c : ℂ_[p]) (v : V) : MvPowerSeries ((V × ι) ⊕ (V × ι)) ℂ_[p] :=
  MvPowerSeries.C c * ∑ e : ι, (sOne p (Sum.inl (v, e)) * sOne p (Sum.inr (v, e)) ^ p +
    sOne p (Sum.inl (v, e)) ^ p * sOne p (Sum.inr (v, e)))

def strB (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
    5 ≤ p → jacobiSym (-(D.host.d : ℤ)) p = -1 → IsFrobC D p →
    ∃ ep : ℂ_[p], InW ep ∧ ‖ep‖ = 1 ∧ ∃ c : ℂ_[p], InW c ∧ (c, -c) ∈ OKp D lam ∧
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
      (ι : Type) [Fintype ι] (b b' : D.what₂.Tau × ι → Idx D N N' → ℂ_[p] × ℂ_[p]) (ϖ : ℂ_[p]),
      admitted D N N' L L' → BasisP D lam (YYp D lam L L') (Sum.elim b b') → DualIso b b' →
      (∀ j k, k.1 ≠ j.1 → b j k = 0 ∧ b' j k = 0) → ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) →
      ∀ F : MvPowerSeries (Idx D N N') ℂ_[p], IsComb D T e lam L L' F →
      ∀ h' : D.what₂.Tau → MvPowerSeries ((D.what₂.Tau × ι) ⊕ (D.what₂.Tau × ι)) ℂ_[p],
        (∀ v, ∃ G : MvPowerSeries ((D.what₂.Tau × ι) ⊕ (D.what₂.Tau × ι)) ℂ_[p], IntegralMv G ∧
          MvPowerSeries.constantCoeff G = 0 ∧ h' v = hhB p c v + algebraMap ℂ_[p] _ (p : ℂ_[p]) * G) →
        InProdG h' (atLin (fun k j => ep * (Sum.elim b b' j k).1 * ϖ) (fun j => MvPowerSeries.X j) F)

def items7 (D : D7) : Prop :=
  thTwo D ∧ thMean D ∧ PhGram D ∧ SDiff D ∧ SDiffW D ∧ FirstKernelRemainder D ∧ a2Ph D ∧ PhaseAwayFromTwo D ∧ ga4Ex D ∧ NormA2Invariant D ∧ pdNorm D ∧ genA D ∧ genInt D ∧ genMom D

def famItems7 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  FirstKernelOrthogonal D cc δ e ∧ enPrim D cc δ e ∧ enMove D cc δ e ∧ genNat D cc δ e ∧
    strC D (tor0 D cc δ) e ∧ strTied D cc δ e ∧ strB D (tor0 D cc δ) e

def StatementSymmetricDifference (D : D7) : Prop := PhGram D → beConj D → SDiff D
def StatementSymmetricDifferenceWitt (D : D7) : Prop := phW D → readW → addInt D → endIntW D → SDiff D → SDiffW D
def StatementFirstKernelRemainder (D : D7) : Prop := phW D → addInt D → endIntW D → SDiffW D → PhDualW D → FirstKernelRemainder D
def StatementPhaseA2 (D : D7) : Prop := PhGram D → a2Ph D ∧ PhaseAwayFromTwo D
def StatementGaussSumFourExists (D : D7) : Prop := InducedCMType D → HostFieldConditions D → ga4Ex D
def StatementGeneratorA (D : D7) : Prop := NormA2Invariant D → pdNorm D → genA D
def StatementFirstKernel (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  intOrtho D cc δ e → endInt D → addInt D → FirstKernelRemainder D → FirstKernelOrthogonal D cc δ e

end A

section C

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.FormalGroupJets Formalism.MainNotions.StandardLatticesGL3 Classical

def b0A (D : D7) {l d : ℕ} [Fact l.Prime] [NeZero d] (lam : Qbar →+* ℂ_[l]) (ep : ℂ_[l]) (Po : Pos D l d)
    (be : {v // v ∈ Po.V} → MvPowerSeries (ZMod d) ℂ_[l]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Cmb : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l] → Prop) : Prop :=
  ∀ (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
    (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l]),
    (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
    (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) → Cmb F →
    (∃ U : MvPowerSeries (TVar D Po N N') ℂ_[l], IntegralMv U ∧
      atLin (fun k j => ep * chg D lam Po P P' k j) (fun j => jetLogG l d j) F =
        U * expMv (algebraMap ℂ_[l] _ (-1 : ℂ_[l]) * ∑ v, beAt N N' (fun ab => (v, ab)) (be v))) ∧
    ∀ v, ∃ U : MvPowerSeries (ZMod d × Fin N × Fin N') ℂ_[l], IntegralMv U ∧
      atLin (fun k (j : ZMod d × Fin N × Fin N') => ep * chg D lam Po P P' k (j.1, (v, j.2)))
          (fun j => jetLogG l d j) F =
        U * expMv (algebraMap ℂ_[l] _ (-1 : ℂ_[l]) * beAt N N' id (be v))

def b0B (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (ep : ℂ_[l])
    (be : MvPowerSeries (ZMod 2) ℂ_[l]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Cmb : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l] → Prop) : Prop :=
  ∀ (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
    (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l]),
    (∀ τ, OrthoBasisW D (tauEmb D lam τ) L (P τ)) →
    (∀ τ, OrthoBasisW D (tauEmb D lam τ) L' (P' τ)) → Cmb F →
    (∃ U : MvPowerSeries (TVarB D N N') ℂ_[l], IntegralMv U ∧
      atLin (fun k j => ep * chgB D lam P P' k j) (fun j => jetLogG l 1 j) F =
        U * expMv (algebraMap ℂ_[l] _ ((-1 : ℂ_[l]) / 2) * ∑ τ, beAt1 N N' (fun ab => (τ, ab)) 1 be)) ∧
    ∀ τ, ∃ U : MvPowerSeries (ZMod 1 × Fin N × Fin N') ℂ_[l], IntegralMv U ∧
      atLin (fun k (j : ZMod 1 × Fin N × Fin N') => ep * chgB D lam P P' k (j.1, (τ, j.2)))
          (fun j => jetLogG l 1 j) F =
        U * expMv (algebraMap ℂ_[l] _ ((-1 : ℂ_[l]) / 2) * beAt1 N N' id 1 be)

def TheoremBEvenRanks (D : D7) (T : Tor D) (e : FamE D) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
    (ep : ℂ_[l]) : Prop :=
  IsFrobC D l → ExistsIntegralAdditionSeries l 1 ∧ B1c1 D T lam ep ∧
    ∃ (be : MvPowerSeries (ZMod 2) ℂ_[l]), FormalSeriesJetConditions be ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
        TaylorLogMetric.admitted D N N' L L' → b0B D lam ep be L L' (IsComb D T e lam L L')

theorem TheoremBEvenRanks.toB {D : D7} {T : Tor D} {e : FamE D} {l : ℕ} [Fact l.Prime] {lam : Qbar →+* ℂ_[l]}
    {ep : ℂ_[l]} (h : TheoremBEvenRanks D T e lam ep) : caseB D T e lam ep := by
  intro hf
  obtain ⟨h1, h2, be, hb, h3⟩ := h hf
  exact ⟨h1, h2, be, 1, -1, norm_one, Or.inr rfl, hb,
    fun N N' L L' P P' F hA hP hP' hF => h3 N N' L L' hA P P' F hP hP' hF⟩

def forOdd (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
    (X : ∀ N N' : ℕ, (MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l] → Prop) → Prop) : Prop :=
  ∀ N N' : ℕ, Even (N * N') → ∀ (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (S : Finset ℕ),
    (∀ q ∈ S, q.Prime ∧ AllSplit D q) → l ∉ S → Nat.Coprime (Ideal.absNorm cc) l →
    IntAt D (tor0 D cc δ) lam (stdL D N) (stdL D N') (IsCombO D cc δ W S lam) →
    X N N' (IsCombO D cc δ W S lam)

def caseAO (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {l : ℕ} [Fact l.Prime]
    (lam : Qbar →+* ℂ_[l]) (ep : ℂ_[l]) : Prop :=
  ∀ (d : ℕ) [NeZero d] (Po : Pos D l d), ExistsIntegralAdditionSeries l d ∧ B1c D (tor0 D cc δ) lam Po ep ∧
    ∃ (be : {v // v ∈ Po.V} → MvPowerSeries (ZMod d) ℂ_[l]), (∀ v, FormalSeriesJetConditions (be v)) ∧
      (∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
        TaylorLogMetric.admitted D N N' L L' → b0A D lam ep Po be L L' (IsComb D (tor0 D cc δ) e lam L L')) ∧
      forOdd D cc δ lam fun N N' Cmb => b0A D lam ep Po be (stdL D N) (stdL D N') Cmb

def caseBO (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {l : ℕ} [Fact l.Prime]
    (lam : Qbar →+* ℂ_[l]) (ep : ℂ_[l]) : Prop :=
  IsFrobC D l → ExistsIntegralAdditionSeries l 1 ∧ B1c1 D (tor0 D cc δ) lam ep ∧
    ∃ (be : MvPowerSeries (ZMod 2) ℂ_[l]), FormalSeriesJetConditions be ∧
      (∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
        TaylorLogMetric.admitted D N N' L L' → b0B D lam ep be L L' (IsComb D (tor0 D cc δ) e lam L L')) ∧
      forOdd D cc δ lam fun N N' Cmb => b0B D lam ep be (stdL D N) (stdL D N') Cmb

theorem caseAO.toA {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {l : ℕ} [Fact l.Prime]
    {lam : Qbar →+* ℂ_[l]} {ep : ℂ_[l]} (h : caseAO D cc δ e lam ep) :
    caseA D (tor0 D cc δ) e lam ep := by
  intro d _ Po
  obtain ⟨h1, h2, be, hb, h3, -⟩ := h d Po
  exact ⟨h1, h2, be, -1, Or.inr rfl, hb,
    fun N N' L L' P P' F hA hP hP' hF => h3 N N' L L' hA P P' F hP hP' hF⟩

theorem caseBO.case_B_of_case_B_pair {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {l : ℕ} [Fact l.Prime]
    {lam : Qbar →+* ℂ_[l]} {ep : ℂ_[l]} (h : caseBO D cc δ e lam ep) :
    TheoremBEvenRanks D (tor0 D cc δ) e lam ep := by
  intro hf
  obtain ⟨h1, h2, be, hb, h3, -⟩ := h hf
  exact ⟨h1, h2, be, hb, h3⟩

def ThetaTheoremsAB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), 5 ≤ l →
    (D.host.cls l = .signal ∨ D.host.cls l = .inertClass) →
    ∃ ep : ℂ_[l], InW ep ∧ ‖ep‖ = 1 ∧ caseAO D cc δ e lam ep ∧ caseBO D cc δ e lam ep

theorem ThetaTheoremsAB.toE {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} (h : ThetaTheoremsAB D cc δ e) :
    ConclusionE₂ D (tor0 D cc δ) e := by
  intro l _ lam h5 hc
  obtain ⟨ep, h1, h2, hA, hB⟩ := h l lam h5 hc
  exact ⟨ep, h1, h2, hA.toA, hB.case_B_of_case_B_pair.toB⟩

def StatementThetaAB (D : D7) : Prop :=
  FormalGroupJets.adm1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : IdE D → ℂ) (e : FamE D),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → LargePrimeLengthVanishing D (tor0 D cc δ) χ e → ThetaTheoremsAB D cc δ e

theorem StatementThetaAB.to {D : D7} (h : StatementThetaAB D) : FormalGroupJets.Stmt D :=
  fun ha cc δ χ e hc hd he => (h ha cc δ χ e hc hd he).toE

def transInv7 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (x ω : ℂ) (m : ℕ), 0 < m → (m : ℂ) * x ∈ lamOf D cc δ → ω ∈ lamOf D cc δ →
      U1 (lamOf D cc δ) (x + 2 * (m : ℂ) * ω) (sgStar (lamOf D cc δ)) =
        U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))

theorem mem_of_half {A : AddSubgroup ℂ} {m : ℕ} {x : ℂ} (hx : (m : ℂ) * (x / 2) ∈ A) : (m : ℂ) * x ∈ A := by
  have : (m : ℂ) * x = (m : ℂ) * (x / 2) + (m : ℂ) * (x / 2) := by ring
  rw [this]
  exact A.add_mem hx hx

theorem transInv7.to {D : D7} (h : transInv7 D) : transInv D :=
  fun cc δ hc x ω m hm hx hω => h cc δ hc x ω m hm (mem_of_half hx) hω

def gal1v7 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ →
      g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M →
      ∀ (x x' : ℂ) (m : ℕ), 0 < m → (m : ℂ) * x ∈ lamOf D cc δ →
        Adp1 M ρ (lamOf D cc δ) (2 * m) x x' →
        (∀ n, coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n ∈ M) →
        ∀ n, cj M ρ (coef1 (U1 (lamOf D cc δ) x (sgStar (lamOf D cc δ))) n) =
          coef1 (U1 (lamConj M ρ (lamOf D cc δ)) x' (sgStar (lamConj M ρ (lamOf D cc δ)))) n

theorem gal1v7.to {D : D7} (h : gal1v7 D) : gal1 D :=
  fun cc δ hc M ρ hK h2 h3 x x' m hm hx => h cc δ hc M ρ hK h2 h3 x x' m hm (mem_of_half hx)

def StatementTranslationInvariantSeventh (D : D7) : Prop := transInv7 D
def StatementGaloisFirstSeventh (D : D7) : Prop := galStar D → galSg D → transInv7 D → gal1v7 D

def odd4v7 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even (N * N') →
    ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ (W : WeilO D cc δ N N' e0)
      (g : GA D N) (g' : GA D N') L₁ L₁' (c : ℂ),
      Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' →
      (W.Om g g' e0 = fun z => c *
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) →
      (∀ z z' x x' : (AE D)ˣ,
        SplitComp D (Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))) z →
        SplitComp D (Matrix.GeneralLinearGroup.det (g' : GL (Fin N') (AE D))) z' →
        x = z * sgU D x → x' = z' * sgU D x' →
          c ^ 2 = (((W.chV.f x' ^ 2) ^ W.ep * (W.chV'.f x ^ 2) ^ W.ep' : ℂˣ) : ℂ)) ∧
      ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]),
        TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p (g' : GL (Fin N') (AE D)) →
        Mod1All c ∧ ‖lamC lam c‖ = 1

theorem odd4v7.to {D : D7} (h : odd4v7 D) : odd4 D := by
  intro cc δ hc N N' hN e0 he hne W g g' L₁ L₁' c hm hm' hO
  obtain ⟨h1, h2⟩ := h cc δ hc N N' hN e0 he hne W g g' L₁ L₁' c hm hm' hO
  refine ⟨fun z z' x x' a b c' d => ⟨1, Or.inl rfl, by rw [one_mul]; exact h1 z z' x x' a b c' d⟩, ?_⟩
  intro p _ lam a b
  exact ⟨(h2 p lam a b).1.1, (h2 p lam a b).2⟩

def StatementOddFourthSeventh (D : D7) : Prop := admG1 D → IntertwinerUnitary D → odd3 D → odd4v7 D

def oddMomC (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ) : Prop :=
  ∀ (W : WeilO D cc δ N N' e0) (S : Finset ℕ), (∀ q ∈ S, q.Prime ∧ AllSplit D q) →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S →
    (p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1) → Nat.Coprime (Ideal.absNorm cc) p →
    ∃ Ω : ℂ_[p], IsOmP lam (tor0 D cc δ).abelian₂ Ω ∧
      ∀ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → VC D N N') (g : Fin m → GA D N) (g' : Fin m → GA D N')
        (Φ : Fin m → VC D N N' → ℂ),
        (∀ i, r i ∈ Qbar ∧ ‖lamC lam (r i)‖ ≤ 1) →
        (∀ i, TorsPrime D p (La0 D (tor0 D cc δ) N N') (t i)) →
        (∀ i, TrivAt D p (g i : GL (Fin N) (AE D)) ∧ TrivAt D p (g' i : GL (Fin N') (AE D))) →
        (∀ i, DatS D cc δ e0 S lam (Φ i)) →
        ∃ s : ℕ, 0 < s ∧ Nat.Coprime s p ∧
          ∀ (k : ℕ) (b : Fin k → Matrix (Fin N') (Fin N) D.host.E),
            NNBasis D (tor0 D cc δ) δ p (stdL D N) (stdL D N') b →
            (∀ j, ∃ x ∈ La0 D (tor0 D cc δ) N N', δ • embV D (tor0 D cc δ) (b j) = s • x) →
            MomAt D cc δ lam Ω b
              (fun z => ∑ i, r i * U D (tor0 D cc δ) (t i) (W.Om (g i) (g' i) (Φ i)) z)

def odd7 (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
    ∀ N N' : ℕ, Even (N * N') → ∃ e0 : VC D N N' → ℂ,
      oddE0 D cc δ t0 N N' e0 ∧ oddKer D cc δ t0 N N' e0 ∧ oddInt D cc δ N N' e0 ∧ oddMom D cc δ N N' e0 ∧
        oddEq D cc δ N N' e0 ∧ oddMomC D cc δ N N' e0 ∧ genOdd D cc δ N N' e0 ∧ oddPrim D cc δ N N' e0

theorem odd7.to {D : D7} (h : odd7 D) : odd D := by
  intro cc δ hc t0 ht N N' hN
  obtain ⟨e0, h1, h2, h3, h4, h5, -⟩ := h cc δ hc t0 ht N N' hN
  exact ⟨e0, h1, h2, h3, h4, h5⟩

def OddThetaSeventhForm (D : D7) : Prop := transInv7 D ∧ gal1v7 D ∧ odd4v7 D ∧ odd7 D

theorem OddThetaSeventhForm.to {D : D7} (h : OddThetaSeventhForm D) : transInv D ∧ gal1 D ∧ odd4 D ∧ odd D :=
  ⟨h.1.to, h.2.1.to, h.2.2.1.to, h.2.2.2.to⟩

def OddThetaSeventhFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam OddThetaSeventhForm Fm

def StatementThetaABFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), StatementThetaAB (Fm.D x i)

theorem StatementThetaABFamily.to {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} (h : StatementThetaABFamily Fm) : FormalGroupJets.KudlaFamilyStatement Fm :=
  fun x i => (h x i).to

end C

section Z

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

def TwistedThetaSeventhForm (D : D7) : Prop :=
  GL3Theta.TwistedThetaTheorem D (1 / 2) fun cc δ e => StandardLatticesGL3.natTie D cc δ e ∧ famItems7 D cc δ e ∧ ThetaTheoremsAB D cc δ e

theorem TwistedThetaSeventhForm.toEd {D : D7} (h : TwistedThetaSeventhForm D) : TwistedThetaFamilies.TwistedThetaFamily D (1 / 2) :=
  GL3Theta.TwistedThetaTheorem.mono (fun _ _ _ hx => hx.1) h

theorem IntAt.mono {D : D7} {T : Tor D} {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {Cmb Cmb' : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] → Prop} (h : ∀ F, Cmb' F → Cmb F)
    (H : StandardLatticesGL3.IntAt D T lam L L' Cmb) : StandardLatticesGL3.IntAt D T lam L L' Cmb' := by
  refine ⟨fun hp F hF => H.1 hp F (h F hF), fun hp => ?_⟩
  obtain ⟨S, hS, u, hu, hu', H2⟩ := H.2 hp
  exact ⟨S, hS, u, hu, hu', fun P P' a b c d F hF => H2 P P' a b c d F (h F hF)⟩

def division_rows_rational_lattice (D : D7) : Prop :=
  items7 D ∧ transInv7 D ∧ gal1v7 D ∧ odd4v7 D ∧ odd7 D ∧ TwistedThetaSeventhForm D

theorem division_rows_rational_lattice.where₂ {D : D7} (h : division_rows_rational_lattice D) :
    StandardLatticesGL3.transInv D ∧ StandardLatticesGL3.gal1 D ∧ StandardLatticesGL3.odd4 D ∧ StandardLatticesGL3.odd D ∧ TwistedThetaFamilies.TwistedThetaFamily D (1 / 2) :=
  ⟨h.2.1.to, h.2.2.1.to, h.2.2.2.1.to, h.2.2.2.2.1.to, h.2.2.2.2.2.toEd⟩

def GL3ThetaAndRationalLattice (D : D7) : Prop := GL3Theta.Adm3s D → StandardLatticesGL3.AdmDext D → GL3Theta.aux₃ D ∧ division_rows_rational_lattice D

def DivisionRowsRationalLatticeOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := GL3Theta.Fam division_rows_rational_lattice Fm
def StatementSeventhFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := TwistedThetaFamilies.AdmF Fm → GL3Theta.ConclusionOnFamily Fm ∧ DivisionRowsRationalLatticeOnFamily Fm

theorem DivisionRowsRationalLatticeOnFamily.toEd {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} (h : DivisionRowsRationalLatticeOnFamily Fm) : TwistedThetaFamilies.TwistedThetaOnFamily Fm (1 / 2) :=
  fun x i => (h x i).2.2.2.2.2.toEd

end Z

end Formalism.MainNotions.GL3r7
