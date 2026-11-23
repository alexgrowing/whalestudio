import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

noncomputable section

namespace Formalism.MainNotions.FormalGroupJets

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

def zL (l d : ℕ) [Fact l.Prime] (s : ZMod d) : MvPowerSeries (ZMod d × Unit) ℂ_[l] :=
  jetLogG l d (s, ())

def zC (l d : ℕ) [Fact l.Prime] (c : Fin 3) (s : ZMod d) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l] :=
  MvPowerSeries.subst (fun k : ZMod d × Unit => (MvPowerSeries.X (c, k.1) : MvPowerSeries (Fin 3 × ZMod d) ℂ_[l]))
    (zL l d s)

def ExistsIntegralAdditionSeries (l d : ℕ) [Fact l.Prime] : Prop :=
  ∃ Fg : ZMod d → MvPowerSeries (Fin 3 × ZMod d) ℂ_[l],
    (∀ s n, InW (MvPowerSeries.coeff n (Fg s))) ∧
    ∀ s, MvPowerSeries.subst (fun k : ZMod d × Unit => Fg k.1) (zL l d s) = zC l d 0 s + zC l d 1 s

def B1 {l d : ℕ} [Fact l.Prime] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ n, NonzeroIndexPlace (MvPowerSeries.coeff n be)

def IsEv {d : ℕ} (s : ZMod d) : Prop := Even s.val

def B2 {l d : ℕ} [Fact l.Prime] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ d - 1) = 1 →
    MvPowerSeries.subst (fun s : ZMod d => algebraMap ℂ_[l] (MvPowerSeries (ZMod d) ℂ_[l])
        (if IsEv s then u ^ (l ^ s.val) else (u⁻¹) ^ (l ^ s.val)) * MvPowerSeries.X s) be = be

def degEv {d : ℕ} (α : ZMod d →₀ ℕ) : ℕ := ∑ s ∈ α.support.filter (fun s => IsEv s), α s
def degOd {d : ℕ} (α : ZMod d →₀ ℕ) : ℕ := ∑ s ∈ α.support.filter (fun s => ¬ IsEv s), α s

def B3 {l d : ℕ} [Fact l.Prime] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  ∀ α, MvPowerSeries.coeff α be ≠ 0 → 1 ≤ degEv α ∧ 1 ≤ degOd α ∧ ¬ (degEv α = 1 ∧ degOd α = 1)

def ExpW {σ : Type*} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  MvPowerSeries.constantCoeff F = 0 ∧ ∀ n, InW (MvPowerSeries.coeff n (expMv F))

def B4 {l d : ℕ} [Fact l.Prime] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  let ev (w : ZMod d → MvPowerSeries (Fin 3 × ZMod d) ℂ_[l]) := MvPowerSeries.subst w be
  ExpW (ev (fun s => if IsEv s then zC l d 0 s + zC l d 1 s else zC l d 2 s) -
      ev (fun s => if IsEv s then zC l d 0 s else zC l d 2 s) -
      ev (fun s => if IsEv s then zC l d 1 s else zC l d 2 s)) ∧
  ExpW (ev (fun s => if IsEv s then zC l d 0 s else zC l d 1 s + zC l d 2 s) -
      ev (fun s => if IsEv s then zC l d 0 s else zC l d 1 s) -
      ev (fun s => if IsEv s then zC l d 0 s else zC l d 2 s))

def FormalSeriesJetConditions {l d : ℕ} [Fact l.Prime] (be : MvPowerSeries (ZMod d) ℂ_[l]) : Prop :=
  B1 be ∧ B2 be ∧ B3 be ∧ B4 be

def ModelW {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[l]) : Prop :=
  InW ((C.u : ℂ_[l]ˣ) : ℂ_[l]) ∧ InW (C • wModel lam Λ).a₁ ∧ InW (C • wModel lam Λ).a₂ ∧
    InW (C • wModel lam Λ).a₃ ∧ InW (C • wModel lam Λ).a₄ ∧ InW (C • wModel lam Λ).a₆

def cmpM (D : D7) {l d : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (Po : Pos D l d)
    (v : {v // v ∈ Po.V}) (ω : ZMod d → D.host.E) : Matrix (ZMod d) (ZMod d) ℂ_[l] :=
  Matrix.of fun s k =>
    if IsEv s ∧ IsEv k then posEmb D lam Po.φ v.1 s (ω k)
    else if ¬ IsEv s ∧ ¬ IsEv k then posEmb D lam Po.φ v.1 s (D.host.conj (ω k))
    else 0

def B1c (D : D7) (T : Tor D) {l d : ℕ} [Fact l.Prime] [NeZero d] (lam : Qbar →+* ℂ_[l]) (Po : Pos D l d)
    (ep : ℂ_[l]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[l]) (wq : PowerSeries ℂ_[l]),
    IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq →
    ∀ (v : {v // v ∈ Po.V}) (ω : ZMod d → D.host.E),
      (∀ s k, ‖cmpM D lam Po v ω s k‖ ≤ 1) → ‖(cmpM D lam Po v ω).det‖ = 1 →
      ∃ Tt : ZMod d → MvPowerSeries (ZMod d) ℂ_[l],
        (∀ s, IntegralMv (Tt s) ∧ MvPowerSeries.constantCoeff (Tt s) = 0) ∧
        (ModelW lam T.abelian₂ C → ∀ s n, InW (MvPowerSeries.coeff n (Tt s))) ∧
        ‖(Matrix.of fun s k : ZMod d => MvPowerSeries.coeff (Finsupp.single k 1) (Tt s)).det‖ = 1 ∧
        ∀ s, MvPowerSeries.subst (fun k : ZMod d × Unit => Tt k.1) (zL l d s) =
          algebraMap ℂ_[l] (MvPowerSeries (ZMod d) ℂ_[l]) (ep⁻¹ * ((C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l])) *
            ∑ k, algebraMap ℂ_[l] (MvPowerSeries (ZMod d) ℂ_[l]) (cmpM D lam Po v ω s k) *
              PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (ZMod d) ℂ_[l])
                (flog (C • wModel lam T.abelian₂) wq)

def B1c1 (D : D7) (T : Tor D) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (ep : ℂ_[l]) : Prop :=
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[l]) (wq : PowerSeries ℂ_[l]),
    IsModel lam T.abelian₂ C → IsWq (C • wModel lam T.abelian₂) wq →
    ∃ Tt : PowerSeries ℂ_[l], (∀ n, IsIntP (PowerSeries.coeff n Tt)) ∧ PowerSeries.coeff 0 Tt = 0 ∧
      ‖PowerSeries.coeff 1 Tt‖ = 1 ∧ (ModelW lam T.abelian₂ C → ∀ n, InW (PowerSeries.coeff n Tt)) ∧
      MvPowerSeries.subst (fun _ : ZMod 1 × Unit => (Tt : MvPowerSeries Unit ℂ_[l])) (zL l 1 0) =
        algebraMap ℂ_[l] (PowerSeries ℂ_[l]) (ep⁻¹ * ((C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l])) *
          flog (C • wModel lam T.abelian₂) wq

def beAt {l d : ℕ} [Fact l.Prime] {β : Type*} (N N' : ℕ) (inj : Fin N × Fin N' → β)
    (be : MvPowerSeries (ZMod d) ℂ_[l]) : MvPowerSeries (ZMod d × β) ℂ_[l] :=
  ∑ a : Fin N, ∑ b : Fin N', MvPowerSeries.subst (fun s : ZMod d => jetLogG l d (s, inj (a, b))) be

def caseA (D : D7) (T : Tor D) (e : FamE D) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
    (ep : ℂ_[l]) : Prop :=
  ∀ (d : ℕ) [NeZero d] (Po : Pos D l d), ExistsIntegralAdditionSeries l d ∧ B1c D T lam Po ep ∧
    ∃ (be : {v // v ∈ Po.V} → MvPowerSeries (ZMod d) ℂ_[l]) (sg : ℂ_[l]), (sg = 1 ∨ sg = -1) ∧
      (∀ v, FormalSeriesJetConditions (be v)) ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : {v // v ∈ Po.V} → Matrix (Fin N) (Fin N) D.host.E)
        (P' : {v // v ∈ Po.V} → Matrix (Fin N') (Fin N') D.host.E)
        (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l]),
        TaylorLogMetric.admitted D N N' L L' → (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L (P v)) →
        (∀ v, LocBasisW D (posEmb D lam Po.φ v.1 (0 : ZMod d)) L' (P' v)) → IsComb D T e lam L L' F →
        (∃ U : MvPowerSeries (TVar D Po N N') ℂ_[l], IntegralMv U ∧
          atLin (fun k j => ep * chg D lam Po P P' k j) (fun j => jetLogG l d j) F =
            U * expMv (algebraMap ℂ_[l] _ sg * ∑ v, beAt N N' (fun ab => (v, ab)) (be v))) ∧
        ∀ v, ∃ U : MvPowerSeries (ZMod d × Fin N × Fin N') ℂ_[l], IntegralMv U ∧
          atLin (fun k (j : ZMod d × Fin N × Fin N') => ep * chg D lam Po P P' k (j.1, (v, j.2)))
              (fun j => jetLogG l d j) F =
            U * expMv (algebraMap ℂ_[l] _ sg * beAt N N' id (be v))

def beAt1 {l : ℕ} [Fact l.Prime] {β : Type*} (N N' : ℕ) (inj : Fin N × Fin N' → β) (ep' : ℂ_[l])
    (be : MvPowerSeries (ZMod 2) ℂ_[l]) : MvPowerSeries (ZMod 1 × β) ℂ_[l] :=
  ∑ a : Fin N, ∑ b : Fin N', MvPowerSeries.subst (fun s : ZMod 2 =>
    if s = 0 then jetLogG l 1 (0, inj (a, b))
    else algebraMap ℂ_[l] (MvPowerSeries (ZMod 1 × β) ℂ_[l]) ep' * jetLogG l 1 (0, inj (a, b))) be

def caseB (D : D7) (T : Tor D) (e : FamE D) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
    (ep : ℂ_[l]) : Prop :=
  IsFrobC D l → ExistsIntegralAdditionSeries l 1 ∧ B1c1 D T lam ep ∧
    ∃ (be : MvPowerSeries (ZMod 2) ℂ_[l]) (ep' sg : ℂ_[l]), ‖ep'‖ = 1 ∧ (sg = 1 ∨ sg = -1) ∧ FormalSeriesJetConditions be ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
        (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
        (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
        (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[l]),
        TaylorLogMetric.admitted D N N' L L' → (∀ τ, OrthoBasisW D (tauEmb D lam τ) L (P τ)) →
        (∀ τ, OrthoBasisW D (tauEmb D lam τ) L' (P' τ)) → IsComb D T e lam L L' F →
        (∃ U : MvPowerSeries (TVarB D N N') ℂ_[l], IntegralMv U ∧
          atLin (fun k j => ep * chgB D lam P P' k j) (fun j => jetLogG l 1 j) F =
            U * expMv (algebraMap ℂ_[l] _ (sg / 2) * ∑ τ, beAt1 N N' (fun ab => (τ, ab)) ep' be)) ∧
        ∀ τ, ∃ U : MvPowerSeries (ZMod 1 × Fin N × Fin N') ℂ_[l], IntegralMv U ∧
          atLin (fun k (j : ZMod 1 × Fin N × Fin N') => ep * chgB D lam P P' k (j.1, (τ, j.2)))
              (fun j => jetLogG l 1 j) F =
            U * expMv (algebraMap ℂ_[l] _ (sg / 2) * beAt1 N N' id ep' be)

def ConclusionE₂ (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), 5 ≤ l →
    (D.host.cls l = .signal ∨ D.host.cls l = .inertClass) → ∃ ep : ℂ_[l], InW ep ∧ ‖ep‖ = 1 ∧ caseA D T e lam ep ∧ caseB D T e lam ep

def adm1 (D : D7) : Prop := Formalism.MainNotions.TaylorLogMetric.adm1 D

def LargePrimeLengthVanishing (D : D7) (T : Tor D) (χ : IdE D → ℂ) (e : FamE D) : Prop :=
  IsChi D χ ∧ vec22 D T e ∧ eq22 D T χ e ∧ int22 D T e

def Stmt (D : D7) : Prop :=
  adm1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : IdE D → ℂ) (e : FamE D),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → LargePrimeLengthVanishing D (tor0 D cc δ) χ e → ConclusionE₂ D (tor0 D cc δ) e

def thAt (J : JetLoc) (ep : ℂ_[J.l]) : MvPowerSeries (ZMod J.d × Fin J.N0 × Fin J.N1) ℂ_[J.l] :=
  MvPowerSeries.subst (fun k : ZMod J.d × Fin J.N0 × Fin J.N1 =>
    algebraMap ℂ_[J.l] (MvPowerSeries (ZMod J.d × Fin J.N0 × Fin J.N1) ℂ_[J.l]) ep * jetLogG J.l J.d k) J.Th

def thAt1 (J : JetLoc1) (ep : ℂ_[J.l]) : MvPowerSeries (ZMod 1 × Fin J.N0 × Fin J.N1) ℂ_[J.l] :=
  MvPowerSeries.subst (fun k : ZMod 1 × Fin J.N0 × Fin J.N1 =>
    algebraMap ℂ_[J.l] (MvPowerSeries (ZMod 1 × Fin J.N0 × Fin J.N1) ℂ_[J.l]) ep * jetLogG J.l 1 k) J.Th

def JetSeriesConditions (D : D7) : Prop :=
  (∀ i : D.jet.Sit, ∃ ep : ℂ_[(D.jet.loc i).l], ‖ep‖ = 1 ∧
    ∃ (be : MvPowerSeries (ZMod (D.jet.loc i).d) ℂ_[(D.jet.loc i).l]) (sg : ℂ_[(D.jet.loc i).l])
      (U : MvPowerSeries (ZMod (D.jet.loc i).d × Fin (D.jet.loc i).N0 × Fin (D.jet.loc i).N1)
        ℂ_[(D.jet.loc i).l]),
      (sg = 1 ∨ sg = -1) ∧ FormalSeriesJetConditions be ∧ IntegralMv U ∧
      thAt (D.jet.loc i) ep = U * expMv (algebraMap _ _ sg * beAt _ _ id be)) ∧
  (∀ i : D.jet.Sit1, ∃ ep : ℂ_[(D.jet.loc1 i).l], ‖ep‖ = 1 ∧
    ∃ (be : MvPowerSeries (ZMod 2) ℂ_[(D.jet.loc1 i).l]) (ep' sg : ℂ_[(D.jet.loc1 i).l])
      (U : MvPowerSeries (ZMod 1 × Fin (D.jet.loc1 i).N0 × Fin (D.jet.loc1 i).N1) ℂ_[(D.jet.loc1 i).l]),
      ‖ep'‖ = 1 ∧ (sg = 1 ∨ sg = -1) ∧ FormalSeriesJetConditions be ∧ IntegralMv U ∧
      thAt1 (D.jet.loc1 i) ep = U * expMv (algebraMap _ _ (sg / 2) * beAt1 _ _ id ep' be))

def JetJoint (D : D7) : Prop :=
  ∀ (T : Tor D) (e : FamE D), ConclusionE₂ D T e → JetTorsionCompatibility D T e → JetSeriesConditions D

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), Stmt (Fm.D x i)

end Formalism.MainNotions.FormalGroupJets
