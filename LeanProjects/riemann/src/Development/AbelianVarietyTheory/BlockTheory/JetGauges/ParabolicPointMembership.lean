import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical
open Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

section Curve

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def atP (c : D.host.K) : ℂ_[p] := lamC lam (D.host.φ₀ (c : D.host.E))

def atPbar (c : D.host.K) : ℂ_[p] := lamC lam (D.host.φ₀ (D.host.conj (c : D.host.E)))

def InLocAway (p : ℕ) (cc : Ideal (𝓞 D.host.K)) (c : D.host.K) : Prop :=
  ∃ (k : ℕ) (z : 𝓞 D.host.K), z ∈ cc ∧ (p : D.host.K) ^ k * c = (z : D.host.K)

def parPt (Lp : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ_[p]) (z : ℂ) : ℂ_[p] :=
  if z ∈ Lp.lattice then 0 else
    let x₀ : ℂ_[p] := lamC lam (Lp.weierstrassP z)
    let y₀ : ℂ_[p] := lamC lam (Lp.derivWeierstrassP z / 2)
    let x : ℂ_[p] := (x₀ - C.r) / (C.u : ℂ_[p]) ^ 2
    let y : ℂ_[p] := (y₀ - C.s * (x₀ - C.r) - C.t) / (C.u : ℂ_[p]) ^ 3
    (-x) / y

def kap1 (Λ : AddSubgroup ℂ) (w z : ℂ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((((w * conj z) / (area Λ : ℂ)).im : ℝ) : ℂ))

variable {D}

def IsPeriod {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (Ω : ℂ_[p]) : Prop :=
  IsOmP lam (lamOf D cc δ) Ω ∧
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
    ∀ s ∈ cc, ∀ c : D.host.K, InLocAway D p cc c → ‖atPbar D lam c‖ ≤ 1 →
      HasSum (fun n : ℕ => PowerSeries.coeff n (expPS (algebraMap ℂ_[p] (PowerSeries ℂ_[p])
          (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * atPbar D lam (s : D.host.K) / Ω) * flog (C • wModel lam (lamOf D cc δ)) wq)) *
          parPt lam B.L C (δ * D.host.φ₀ (c : D.host.E)) ^ n)
        (lamC lam (kap1 (lamOf D cc δ) (δ * D.host.φ₀ ((s : D.host.K) : D.host.E)) (δ * D.host.φ₀ (c : D.host.E))))

end Curve

section Meas

variable {p : ℕ} [Fact p.Prime]

abbrev Meas (p r : ℕ) [Fact p.Prime] : Type := C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]

def IsRMeas {r : ℕ} (μ : Meas p r) : Prop := ‖μ‖ ≤ 1

def wt {r : ℕ} (f : C(Fin r → ℤ_[p], ℂ_[p])) (μ : Meas p r) : Meas p r :=
  μ.comp (ContinuousLinearMap.mul ℂ_[p] C(Fin r → ℤ_[p], ℂ_[p]) f)

theorem wt_apply {r : ℕ} (f g : C(Fin r → ℤ_[p], ℂ_[p])) (μ : Meas p r) : wt f μ g = μ (f * g) := rfl

theorem continuous_zc : Continuous (zc : ℤ_[p] → ℂ_[p]) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

variable (D : D7) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def pairC (y : Matrix (Fin N') (Fin N) D.host.E) : C(Fin r → ℤ_[p], ℂ_[p]) where
  toFun := pairN D lam Ω b y
  continuous_toFun := by
    unfold pairN
    exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (continuous_zc.comp (continuous_apply i)).mul continuous_const)

def IsTransform (μ : Meas p r) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), jet D lam y F = μ (∏ i, pairC D lam Ω b (y i))

def polyJet {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (P : MvPolynomial (Fin n) ℂ_[p])
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : ℂ_[p] :=
  ∑ α ∈ P.support, P.coeff α *
    MvPowerSeries.constantCoeff ((List.finRange n).foldr (fun i G => (der D lam (y i))^[α i] G) F)

def polyC {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (P : MvPolynomial (Fin n) ℂ_[p]) :
    C(Fin r → ℤ_[p], ℂ_[p]) :=
  MvPolynomial.aeval (fun i => pairC D lam Ω b (y i)) P

def XiMoments (μ : Meas p r) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ_[p])
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) : Prop :=
  IsTransform D lam Ω b (wt Φ.toContinuousMap μ) F ∧
  ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (P : MvPolynomial (Fin n) ℂ_[p]),
    polyJet D lam y P F = μ (polyC D lam Ω b y P * Φ.toContinuousMap) ∧
    ((∀ a, IsIntP (Φ a)) → (∀ a, Φ a ≠ 0 → IsIntP (polyC D lam Ω b y P a)) → IsIntP (polyJet D lam y P F))

end Meas

section Lifts

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ}

def AlgEntire (G : VC D N N' → ℂ) : Prop := Differentiable ℂ G ∧ CoefIn D G Qbar

def MemAtP (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∃ s : 𝓞 D.host.K, ‖atP D lam (s : D.host.K)‖ = 1 ∧ ((s : D.host.K) : D.host.E) • A ∈ Y

def MemAtPbar (Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∃ s : 𝓞 D.host.K, ‖atPbar D lam (s : D.host.K)‖ = 1 ∧ ((s : D.host.K) : D.host.E) • A ∈ Y

def vecOf (A : Matrix (Fin N') (Fin N) D.host.E) : VC D N N' := δ • embV D (tor0 D cc δ) A

def AdmLift (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  (∃ k : ℕ, p ^ k • vecOf D cc δ A ∈ La D (tor0 D cc δ) L L') ∧
  MemAtP D lam (YYl D L L') (((p : D.host.E) ^ n) • A) ∧
  MemAtPbar D lam (YYl D L L') (((p : D.host.E) ^ n)⁻¹ • A)

def IsCoords (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (A : Matrix (Fin N') (Fin N) D.host.E)
    (c' : Fin r → D.host.K) : Prop :=
  ∃ c : Fin r → D.host.K, A = ∑ i, (c i : D.host.E) • b i ∧
    ∀ i, InLocAway D p cc (c' i) ∧ ‖atP D lam (c' i - c i)‖ ≤ 1 ∧ ‖atPbar D lam (c' i - c i)‖ ≤ 1

def IsTranslate (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p])
    (v : Fin r → ℂ_[p]) (H : MvPowerSeries (Fin r) ℂ_[p]) : Prop :=
  (∀ i, ‖v i‖ < 1) ∧ ∀ α : Fin r →₀ ℕ,
    HasSum (fun β : Fin r →₀ ℕ =>
        MvPowerSeries.coeff (α.mapDomain (Fin.castAdd r) + β.mapDomain (Fin.natAdd r))
          (atLog D lam (lamOf D cc δ) C wq (Fin.append b b) F) * ∏ i, v i ^ β i)
      (MvPowerSeries.coeff α H)

def FactorsModP (n : ℕ) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ_[p]) : Prop :=
  ∀ a a' : Fin r → ℤ_[p], (∀ i, ‖a i - a' i‖ ≤ (p : ℝ) ^ (-(n : ℤ))) → Φ a = Φ a'

def XiP (n : ℕ) (ε : 𝓞 D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ_[p]) (G : VC D N N' → ℂ) :
    MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] :=
  ∑ y : Fin r → Fin (p ^ n),
    (((p : ℂ_[p]) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), Φ (fun i => ((a i : ℕ) : ℤ_[p])) *
      (lamC lam (kap D (tor0 D cc δ) (vecN D (tor0 D cc δ) δ p n b a) (liftY D (tor0 D cc δ) δ p n ε b y)))⁻¹) •
    pSer D lam (Wop D (tor0 D cc δ) p (liftY D (tor0 D cc δ) δ p n ε b y) G)

end Lifts

section Clauses

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)
  {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def HidaSetting : Prop :=
  g2 (lamOf D cc δ) ∈ Qbar ∧ g3 (lamOf D cc δ) ∈ Qbar ∧
  (∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsModel lam (lamOf D cc δ) C ∧ IsWq (C • wModel lam (lamOf D cc δ)) wq) ∧
  (∀ c : D.host.K, InLocAway D p cc c → ‖atPbar D lam c‖ ≤ 1 →
    (δ * D.host.φ₀ (c : D.host.E) ∉ B.L.lattice →
      B.L.weierstrassP (δ * D.host.φ₀ (c : D.host.E)) ∈ Qbar ∧
      B.L.derivWeierstrassP (δ * D.host.φ₀ (c : D.host.E)) ∈ Qbar) ∧
    ∀ C, IsModel lam (lamOf D cc δ) C → ‖parPt lam B.L C (δ * D.host.φ₀ (c : D.host.E))‖ < 1) ∧
  (∀ N N' L L', admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
    NNBasis D B.tor δ p L L' b) ∧
  ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε

def eMinusPhi (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  if p = 2 then
    PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * flog (C • wModel lam (lamOf D cc δ)) wq)
      (PowerSeries.mk fun n => lamC lam (iteratedDeriv n B.th0 0 / (n.factorial : ℂ)))
  else ePhi1 lam (lamOf D cc δ) C wq

def PhTrivial : Prop :=
  (∀ n : ℕ, iteratedDeriv n (if p = 2 then B.th0 else sgStar (lamOf D cc δ)) 0 ∈ Qbar) ∧
  ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq → ∀ r : ℕ,
      let eP : MvPowerSeries (Fin r) ℂ_[p] := ∏ i : Fin r,
        PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (eMinusPhi B lam C wq)
      MvPowerSeries.constantCoeff eP = 1 ∧ IntegralMv eP

def IntAlg : Prop :=
  ∀ N N' L L', admitted D N N' L L' → ∀ L₁ L₁', admitted D N N' L₁ L₁' → EqAt D p L L₁ → EqAt D p L' L₁' →
    ∀ t, TorsPrime D p (La D B.tor L L') t → AlgEntire D (U D B.tor t (B.eNat χ N N' L₁ L₁'))

def IntSplit : Prop :=
  ∀ N N' L L', admitted D N N' L L' → ∀ F, IsComb D B.tor (B.eNat χ) lam L L' F →
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
      ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b →
        IntegralMv (atLog D lam (lamOf D cc δ) C wq b F)

def IntJets : Prop :=
  ∀ N N' L L', admitted D N N' L L' → ∀ F, IsComb D B.tor (B.eNat χ) lam L L' F →
    ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ i, y i ∈ YYl D L L') →
      ∀ P : MvPolynomial (Fin n) ℂ_[p], (∀ α, IsIntP (P.coeff α)) → IsIntP (polyJet D lam y P F)

variable {N N' r : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
  (Ω : ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def IsMeasE (μ : Meas p r) : Prop :=
  IsRMeas μ ∧ IsTransform D lam Ω b μ (pSer D lam (B.eNat χ N N' L L')) ∧
  ∀ μ' : Meas p r, IsTransform D lam Ω b μ' (pSer D lam (B.eNat χ N N' L L')) → μ' = μ

def MomTranslate : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), AdmLift D lam cc δ L L' n A →
    AlgEntire D (Wop D B.tor p (vecOf D cc δ A) (B.eNat χ N N' L L')) ∧
    ∀ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      IsModel lam (lamOf D cc δ) C → IsWq (C • wModel lam (lamOf D cc δ)) wq →
      ∀ (r' : ℕ) (b' : Fin r' → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b' →
        ∃ c' : Fin r' → D.host.K, IsCoords D lam cc b' A c' ∧
          IsTranslate D lam cc δ C wq b' (pSer D lam (B.eNat χ N N' L L'))
            (fun i => parPt lam B.L C (δ * D.host.φ₀ (c' i : D.host.E)))
            (atLog D lam (lamOf D cc δ) C wq b'
              (pSer D lam (Wop D B.tor p (vecOf D cc δ A) (B.eNat χ N N' L L'))))

def MomChar (μ : Meas p r) : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), AdmLift D lam cc δ L L' n A →
    ∃ ψ : C(Fin r → ℤ_[p], ℂ_[p]),
      (∀ a : Fin r → ℤ, ψ (fun i => (a i : ℤ_[p])) =
        lamC lam (kap D B.tor (vecOf D cc δ (∑ i, (a i : D.host.E) • b i)) (vecOf D cc δ A))) ∧
      IsTransform D lam Ω b (wt ψ μ) (pSer D lam (Wop D B.tor p (vecOf D cc δ A) (B.eNat χ N N' L L')))

def MomXiAlg (μ : Meas p r) : Prop :=
  ∀ Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ, (∀ a, Φ a ∈ Qbar) → ∀ n : ℕ, FactorsMod n Φ →
    ∀ ε : 𝓞 D.host.K, IsIdem D lam (2 * n) ε →
      AlgEntire D (XiF D B.tor δ p n ε b Φ (B.eNat χ N N' L L')) ∧
      XiMoments D lam Ω b μ (Φ.map (lamC lam)) (pSer D lam (XiF D B.tor δ p n ε b Φ (B.eNat χ N N' L L')))

def MomXiPadic (μ : Meas p r) : Prop :=
  ∀ Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ_[p], ∀ n : ℕ, FactorsModP n Φ →
    ∀ ε : 𝓞 D.host.K, IsIdem D lam (2 * n) ε →
      XiMoments D lam Ω b μ Φ (XiP D lam cc δ n ε b Φ (B.eNat χ N N' L L'))

def MomIndicator : Prop :=
  ∀ (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L₁ L₂ →
    (∃ k : ℕ, (∀ A ∈ homL D L L', ((p : D.host.E) ^ k) • A ∈ homL D L₁ L₂) ∧
      ∀ A ∈ homL D L₁ L₂, ((p : D.host.E) ^ k) • A ∈ homL D L L') →
    (∀ A ∈ homL D L L', MemAtPbar D lam (homL D L₁ L₂) A) →
    ∀ (r' : ℕ) (b' : Fin r' → Matrix (Fin N') (Fin N) D.host.E), NNBasis D B.tor δ p L₁ L₂ b' →
      ∃ (Φ : LocallyConstant (Fin r' → ℤ_[p]) ℂ) (u : ℂ),
        (∀ a : Fin r' → ℤ, Φ (fun i => (a i : ℤ_[p])) =
          if MemAtPbar D lam (YYl D L L') (∑ i, (a i : D.host.E) • b' i) then 1 else 0) ∧
        u ∈ Qbar ∧ ‖lamC lam u‖ = 1 ∧
        ∀ n : ℕ, FactorsMod n Φ → ∀ ε : 𝓞 D.host.K, IsIdem D lam (2 * n) ε →
          XiF D B.tor δ p n ε b' Φ (B.eNat χ N N' L₁ L₂) = fun z => u * B.eNat χ N N' L L' z

end Clauses

def IntAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)
    {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Prop :=
  PhTrivial B lam ∧ IntAlg B χ (p := p) ∧ IntSplit B χ lam ∧ IntJets B χ lam

def MomAt {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : IdE D → ℂ)
    {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∃ Ω : ℂ_[p], IsPeriod lam B Ω ∧
    ∀ N N' L L', admitted D N N' L L' →
      MomTranslate B χ lam L L' ∧ MomIndicator B χ lam L L' ∧
      ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D B.tor δ p L L' b →
        ∃ μ : Meas p r, IsMeasE B χ lam L L' Ω b μ ∧ MomChar B χ lam L L' Ω b μ ∧
          MomXiAlg B χ lam L L' Ω b μ ∧ MomXiPadic B χ lam L L' Ω b μ

def IntMomSplit : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (B : Base D cc δ) (χ : IdE D → ℂ), IsChi D χ →
      ∀ (p : ℕ) [Fact p.Prime], SplitK D p → Nat.Coprime (Ideal.absNorm cc) p →
        ∀ lam : Qbar →+* ℂ_[p], HidaSetting B lam ∧ IntAt B χ lam ∧ MomAt B χ lam

example {p r : ℕ} [Fact p.Prime] (μ : Meas p r) : wt 1 μ = μ := by
  ext f; simp [wt_apply]

example {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Lp : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ_[p]) :
    parPt lam Lp C 0 = 0 := by simp [parPt]

end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership
