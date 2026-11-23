import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.CurveAt

open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (phFF thetaS NormRel PV)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open Formalism.L2.Th1.Top (IsHypPair inHyp IsLTNorm IsLatH IsFrameH thetaH)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.L2.Th1.GD (LocNorm thetaLin frameM InMul IsPairFrame)

def PlaceSeriesJetsCyclicOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l])
    (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β → IsSysW l Q S β

def IntegralSeriesCyclicOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l])
    (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ Θ : MvPowerSeries n ℂ_[l], HostInt l g2 g3 s2 ε Θ →
    ∃ U : MvPowerSeries S.ι ℂ_[l], Integral U ∧
      MvPowerSeries.subst x (serAlong e (inHyp l f f' Θ)) = MvPowerSeries.subst S.g U * S.E

def HostEntryA : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l])
    (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ Θ : MvPowerSeries n ℂ_[l], HostInt l g2 g3 s2 ε Θ →
    IsEntryAll l Q β (MvPolynomial.coeff 0 (jetPairPoly S.P (MvPowerSeries.subst x (serAlong e (inHyp l f f' Θ)))))

def PlaceSeriesJetsOneLetterOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (P : Type) (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostB l σ (cob F (phFF l g2 g3 s2 ε)) (phFF l g2 g3 s2 ε) N0 N1 P S x Ψ β → IsSysW l Q S β

def IntegralSeriesOneLetterOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (P : Type) [Fintype P] (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l])
    (β : ℝ), IsHostB l σ (cob F (phFF l g2 g3 s2 ε)) (phFF l g2 g3 s2 ε) N0 N1 P S x Ψ β →
  ∀ Θ : MvPowerSeries P ℂ_[l], HostInt l g2 g3 s2 ε Θ →
    ∃ U : MvPowerSeries S.ι ℂ_[l], Integral U ∧ MvPowerSeries.subst x Θ = MvPowerSeries.subst S.g U * S.E

def HostEntryB : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (P : Type) [Fintype P] (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l])
    (β : ℝ), IsHostB l σ (cob F (phFF l g2 g3 s2 ε)) (phFF l g2 g3 s2 ε) N0 N1 P S x Ψ β →
  ∀ Θ : MvPowerSeries P ℂ_[l], HostInt l g2 g3 s2 ε Θ →
    IsEntryAll l Q β (MvPolynomial.coeff 0 (jetPairPoly S.P (MvPowerSeries.subst x Θ)))

def HostIntFree : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  (∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F →
    CurveAt l g2 g3 s2 ε σ F) ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
    ∃ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix (n) (n) ℂ_[l]), IsFrameH σ ι g₁ γ B') ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → (∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F) →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
    HostInt l g2 g3 s2 ε (thetaH l ι B' h t θ)

def HostIntComb : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (n : Type) [Fintype n] (κx : Type) [Fintype κx] (r : κx → ℂ_[l])
    (Θ : κx → MvPowerSeries n ℂ_[l]), (∀ k, ‖r k‖ ≤ 1) → (∀ k, HostInt l g2 g3 s2 ε (Θ k)) →
    HostInt l g2 g3 s2 ε (∑ k, MvPowerSeries.C (r k) * Θ k)

def LatAt (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) {n : Type} [Fintype n]
    [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  CmOK a₀ b₀ c₀ dK ∧ IsSelfDual (matH h) Λ ∧ (∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ dK • x ∈ Λ) ∧
    θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ ∧ LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι

def HostJetsOdd : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι → p ≠ 2 → ¬ p ∣ dK →
    IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) →
  ∀ (Q : OrbSys ℂ_[p] → ℝ → Prop) (R : MvPolynomial ν ℂ_[p]), (∀ k, ‖MvPolynomial.coeff k R‖ ≤ 1) →
    IsEntryAll p Q 0 (jetPair R (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)))

def HostJetsTwo : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (ι : ℂ ≃+* ℂ_[2]), LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ 2 ι →
  ∀ W : WeierstrassCurve ℂ_[2], Unif 2 (cmL a₀ b₀ dK ha hdK lam hlam) ι W → IntCurve W → ‖W.a₁‖ = 1 →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[2]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 2 ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[2]), (∀ j x, ‖A j x‖ ≤ 1) →
  ∀ (Q : OrbSys ℂ_[2] → ℝ → Prop) (R : MvPolynomial ν ℂ_[2]), (∀ k, ‖MvPolynomial.coeff k R‖ ≤ 1) →
    IsEntryAll 2 Q 0 (jetPair R (thetaLin (ι : ℂ →+* ℂ_[2]) h θ r t (frameM (ι : ℂ →+* ℂ_[2]) v A)))

def ThetaZJetsThree : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → d % 3 = 2 → Formalism.L2.Th1.CM.HasCMBy d L →
  ∀ (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]), Unif 3 L ι W → IntCurve W →
  ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    (starRingEnd ℂ) (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
  ∀ (n : Type) [Fintype n] (κ : Type) [Fintype κ] (r : κ → ℂ_[3]) (s : κ → n → ℂ) (N : ℕ),
    (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 3 ∣ N → (∀ k i, (N : ℂ) * s k i ∈ L.lattice) →
    JetsIntegral (Formalism.L2.Th1.Top.thetaZ 3 L ι ω₀ r s)

def HostJetsThree : Prop :=
  ThetaZJetsThree →
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (ι : ℂ ≃+* ℂ_[3]), LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ 3 ι → dK % 3 = 2 →
  ∀ W : WeierstrassCurve ℂ_[3], Unif 3 (cmL a₀ b₀ dK ha hdK lam hlam) ι W → IntCurve W →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[3]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ 3 ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ dK ha hdK lam hlam) Λ (v j)) →
  ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[3]), (∀ j x, ‖A j x‖ ≤ 1) →
  ∀ (Q : OrbSys ℂ_[3] → ℝ → Prop) (R : MvPolynomial ν ℂ_[3]), (∀ k, ‖MvPolynomial.coeff k R‖ ≤ 1) →
    IsEntryAll 3 Q 0 (jetPair R (thetaLin (ι : ℂ →+* ℂ_[3]) h θ r t (frameM (ι : ℂ →+* ℂ_[3]) v A)))

def HostShapeD : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), LatAt a₀ b₀ c₀ dK ha hdK lam hlam h Λ θ p ι → p ∣ dK →
    IntCurve (curveL p (cmL a₀ b₀ dK ha hdK lam hlam) ι) →
  ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (N : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < N → ¬ p ∣ N →
    (∀ k, (N : ℂ) • t k ∈ Λ) →
  ∀ (J : Type) [Fintype J] (v : J → n → ℂ) (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
    (A : J → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
    (q : ((Bool × H) × Fin N0 × Fin N1) → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]),
    ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) → IsPairFrame (ι : ℂ →+* ℂ_[p]) (cmL a₀ b₀ dK ha hdK lam hlam) h Λ v A u th q →
    (∀ s, ‖u s‖ ≤ 1) →
  ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
    (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
  ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
    (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) → (∀ τ, size τ = ∑ c, ht τ c) →
  ∀ (Q : OrbSys ℂ_[p] → ℝ → Prop) (δ : MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p] →ₗ[ℂ_[p]] ℂ_[p]), MonInt δ →
    IsEntryAll p Q (expD TT nu1 nu2 size)
      (δ (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A))))

end Formalism.L2.DIV.C
