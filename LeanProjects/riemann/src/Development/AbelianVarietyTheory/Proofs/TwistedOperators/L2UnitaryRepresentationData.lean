import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ArchRec

abbrev Mn (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

section Cover

variable {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s}

def IsGK {W : Type} [AddCommGroup W] [Module ℂ W] (a : Mat p q →ₗ[ℂ] Module.End ℂ W) : Prop :=
  IsLieAct a ∧ (∀ v, ∃ F : Submodule ℂ W, FiniteDimensional ℂ F ∧ v ∈ F ∧ KStable a F) ∧
    ∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub a μ

structure IsUAct {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (b : Mat p q → Module.End ℂ U) : Prop where
  add : ∀ X ∈ upq p q, ∀ Y ∈ upq p q, b (X + Y) = b X + b Y
  smul : ∀ (c : ℝ), ∀ X ∈ upq p q, b (c • X) = (c : ℂ) • b X
  lie : ∀ X ∈ upq p q, ∀ Y ∈ upq p q, b (X * Y - Y * X) = b X * b Y - b Y * b X
  skew : ∀ X ∈ upq p q, ∀ x y, ⟪b X x, y⟫_ℂ = -⟪x, b X y⟫_ℂ

def ctr (R : DSRep T₁) (U : Type) [AddCommGroup U] [Module ℂ U] (v : R.HK.V) : R.HK.V ⊗[ℂ] U →ₗ[ℂ] U :=
  TensorProduct.lift (LinearMap.lsmul ℂ U ∘ₗ (innerₛₗ ℂ (R.ι v) ∘ₗ R.ι))

theorem ctr_tmul (R : DSRep T₁) (U : Type) [AddCommGroup U] [Module ℂ U] (v x : R.HK.V) (y : U) :
    ctr R U v (x ⊗ₜ y) = ⟪R.ι v, R.ι x⟫_ℂ • y := by
  simp [ctr]

def PInv {W U : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (a : Mat p q →ₗ[ℂ] Module.End ℂ W) (R : DSRep T₁) (b : W →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) : Prop :=
  ∀ Z ∈ upq p q, ∀ P v, b (a Z P) v + b P (R.HK.act Z v) = 0

def TIntw {W : Type} [AddCommGroup W] [Module ℂ W] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ W)
    (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ W) (M₁ : GKMod p q) (M₂ : GKMod r s) (f : W →ₗ[ℂ] M₁.V ⊗[ℂ] M₂.V) : Prop :=
  (∀ X, f ∘ₗ a₁ X = TensorProduct.map (M₁.act X) LinearMap.id ∘ₗ f) ∧
    ∀ Y, f ∘ₗ a₂ Y = TensorProduct.map LinearMap.id (M₂.act Y) ∘ₗ f

variable {σ : Type} (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
  (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))

def CJoint (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ) (Φ : MvPolynomial σ ℂ) : Prop :=
  (∃ d, Φ.IsHomogeneous d ∧ (∀ Z ∈ pR p q, (a₁ Z Φ).IsHomogeneous (d + 2)) ∧
    ∀ Z ∈ pR r s, (a₂ Z Φ).IsHomogeneous (d + 2)) ∧ IsHW a₁ Λ₁ Φ ∧ IsHW a₂ Λ₂ Φ

variable (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ)

structure TensLaw : Prop where
  ex : ∃ Φ, CJoint a₁ a₂ Λ₁ Λ₂ Φ
  uniq : ∀ Φ Φ', CJoint a₁ a₂ Λ₁ Λ₂ Φ → CJoint a₁ a₂ Λ₁ Λ₂ Φ' → ∃ c : ℂ, Φ' = c • Φ
  unit : ∀ (MM : UGKMod r s) (f : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] MM.M.V), TIntw a₁ a₂ R₁.HK MM.M f → f ≠ 0 →
    (∃ N : Submodule ℂ MM.M.V, ∃ e : R₂.HK.V ≃ₗ[ℂ] N,
      (∀ Z x, ((e (R₂.HK.act Z x) : N) : MM.M.V) = MM.M.act Z (e x)) ∧
      LinearMap.range f = LinearMap.range (TensorProduct.map LinearMap.id N.subtype)) ∧
    ∀ Φ, CJoint a₁ a₂ Λ₁ Λ₂ Φ → f Φ ≠ 0 ∧ ∀ f', TIntw a₁ a₂ R₁.HK MM.M f' → f' Φ = f Φ → f' = f
  line : ∃ f₀ : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] R₂.HK.V, TIntw a₁ a₂ R₁.HK R₂.HK f₀ ∧ f₀ ≠ 0 ∧
    ∀ f, TIntw a₁ a₂ R₁.HK R₂.HK f → ∃ c : ℂ, f = c • f₀

def PLift {U : Type} [AddCommGroup U] [Module ℂ U] (b : Mat r s → Module.End ℂ U)
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U) : Prop :=
  PInv a₁ R₁ B ∧ ∀ Z ∈ upq r s, ∀ P v, B (a₂ Z P) v = b Z (B P v)

structure PairLaw : Prop where
  ex : ∃ Φ, CJoint a₁ a₂ Λ₁ Λ₂ Φ
  uniq : ∀ Φ Φ', CJoint a₁ a₂ Λ₁ Λ₂ Φ → CJoint a₁ a₂ Λ₁ Λ₂ Φ' → ∃ c : ℂ, Φ' = c • Φ
  unit : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (b : Mat r s → Module.End ℂ U), IsUAct b →
    ∀ B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U, PLift a₁ a₂ R₁ b B → B ≠ 0 →
      (∃ e : R₂.HK.V →ₗ[ℂ] U, Function.Injective e ∧ (∀ Z ∈ upq r s, ∀ x, e (R₂.HK.act Z x) = b Z (e x)) ∧
        LinearMap.range e = Submodule.span ℂ {y | ∃ P v, y = B P v}) ∧
      ∀ Φ, CJoint a₁ a₂ Λ₁ Λ₂ Φ → (∀ v, UnitHW R₁ Λ₁ v → B Φ v ≠ 0) ∧
        ∀ B', PLift a₁ a₂ R₁ b B' → B' Φ = B Φ → B' = B
  line : ∃ B₀ : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] R₂.HK.V, B₀ ≠ 0 ∧
    PLift a₁ a₂ R₁ (fun Z => R₂.HK.act Z) B₀ ∧ ∀ B, PLift a₁ a₂ R₁ (fun Z => R₂.HK.act Z) B → ∃ c : ℂ, B = c • B₀

def TensNo : Prop :=
  ∀ (MM : GKMod r s) (f : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] MM.V), TIntw a₁ a₂ R₁.HK MM f → f = 0

def PairNo : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (B : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V →ₛₗ[starRingEnd ℂ] U),
    PInv a₁ R₁ B → B = 0

end Cover

def phi {p q n : ℕ} (br : Bool) (e : Ix p q ≃ Fin n) (Z : Mat p q) : Mn n := if br then barMat e Z else plainMat e Z

def phiFr {p q n : ℕ} (fr : Mn n) (br : Bool) (e : Ix p q ≃ Fin n) (Z : Mat p q) : Mn n := fr⁻¹ * phi br e Z * fr

def sg (br cj : Bool) : ℝ := if br = cj then 1 else -1

def parOf (br cj : Bool) (l₁ l₂ : List ℚ) (c : ℚ) : SPar := if br = cj then signed l₁ l₂ c else dualPar (signed l₁ l₂ c)

def cjc (cj : Bool) (z : ℂ) : ℂ := if cj then conj z else z

section Comparison₂

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {p q : ℕ} {T : GrpData p q}

def IsOrd {n : ℕ} (ε : Fin n → Bool) (lamM : Fin n → ℝ) (lam : Ix p q → ℚ) (c : ℚ) (sgn : ℝ) (e : Ix p q ≃ Fin n) : Prop :=
  SignCompat ε e ∧ (∀ a, lamM (e a) = sgn * ((lam a + c : ℚ) : ℝ)) ∧
    ∀ a, Formalism.QuantumDeterminants.lowK ε lamM (e a) = sgn * ((blattner lam a + c : ℚ) : ℝ)

structure Comparison₂ (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ)
    (U : M.H τ → R.U.H) : Prop where
  add : ∀ x y, U (x + y) = U x + U y
  smul : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x
  bij : Function.Bijective U
  norm : ∀ x, ‖U x‖ = ‖x‖
  grp : ∀ (g : T.G) (x : M.H τ), R.U.π g (U x) =
    ((T.sq g : ℂˣ) : ℂ) ^ (-m) • U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x)
  kfin : ∀ x : M.H τ, IsKFin (M.ε τ) (M.σ τ) x ↔ U x ∈ Set.range R.ι

structure KTie (R : DSRep T) (M : DSModel V S) (τ : D.what₂.Tau) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool)
    (e : Ix p q ≃ Fin V.rank) (u : kfin M τ → R.HK.V) : Prop where
  par : IsParam lam
  ord : IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e
  add : ∀ x y, u (x + y) = u x + u y
  smul : ∀ (z : ℂ) x, u (z • x) = cjc cj z • u x
  bij : Function.Bijective u
  lie : phiFr (M.fr τ) br e '' upq p q = lieAt V τ
  der : ∀ Z ∈ upq p q, ∀ v v', VecDer M τ (phiFr (M.fr τ) br e Z) v v' ↔
    u v' = R.HK.act Z (u v) + ((c : ℂ) * Z.trace) • u v
  hi : ∀ v, UnitHighest M τ v ↔ UnitHW R (blattner lam) (u v)
  coef : ∀ m : ℤ, (m : ℚ) = 2 * c → ∀ (g : T.G) (v w : kfin M τ),
    cjc cj ⟪(w : M.H τ), M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) v⟫_ℂ =
      ((T.sq g : ℂˣ) : ℂ) ^ m * ⟪R.ι (u w), R.U.π g (R.ι (u v))⟫_ℂ

end Comparison₂

def DirectBridge (D : D7) : Prop :=
  ∀ (X : ProvA) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ),
    1 ≤ p + q → l₁.length = p → l₂.length = q → IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) →
    HasParam (X.ds p q (ofBlocks l₁ l₂)) (ofBlocks l₁ l₂) → S τ = signed l₁ l₂ c →
    ∃ m : ℤ, (m : ℚ) = 2 * c ∧ ∀ e : Ix p q ≃ Fin V.rank, SignCompat (M.ε τ) e → ∀ b : Bool,
      ∃ U, Comparison₂ (X.ds p q (ofBlocks l₁ l₂)) M τ b b e m U

section Side

variable {ι σ Z : Type} {n p q : ℕ}

structure Side (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ))
    (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (φ : Mat p q → Mn n) (c : ℚ)
    (a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) : Prop where
  der : ∀ Y ∈ upq p q, ∀ P P', PolDer A pt (φ Y) P P' ↔ κ P' = a Y (κ P) + ((c : ℂ) * Y.trace) • κ P
  wt : ∀ (μ : Ix p q → ℚ) P, κ P ∈ wtSub a μ ↔ ∀ x : Ix p q → ℝ,
    A (φ (Matrix.diagonal fun j => Complex.exp ((x j : ℂ) * Complex.I))) (pt P) =
      Complex.exp (((∑ j, ((μ j + c : ℚ) : ℝ) * x j : ℝ) : ℂ) * Complex.I) • pt P

def Graded (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∀ d P, (κ P).IsHomogeneous d ↔ P.IsHomogeneous d

def Fischer (pt : MvPolynomial ι ℂ → (Z → ℂ)) (ip : (Z → ℂ) → (Z → ℂ) → ℂ)
    (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (N : ℝ) : Prop :=
  0 < N ∧ ∀ P Q, ip (pt P) (pt Q) = (N : ℂ) * fockIp (κ P) (κ Q)

structure L2UnitaryRepresentationData (G : Mn n) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ))
    (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (Θ : Submodule ℂ (Z → ℂ)) : Prop where
  mem : ∀ P, pt P ∈ Θ
  pt_lin : ∀ (z : ℂ) P Q, pt (z • P + Q) = z • pt P + pt Q
  ip_lin : ∀ (z : ℂ), ∀ F ∈ Θ, ∀ F' ∈ Θ, ∀ E ∈ Θ, ip (z • F + F') E = z * ip F E + ip F' E
  ip_symm : ∀ F ∈ Θ, ∀ E ∈ Θ, ip E F = conj (ip F E)
  ip_pos : ∀ F ∈ Θ, F ≠ 0 → 0 < (ip F F).re
  stable : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ F ∈ Θ, A g F ∈ Θ
  lin : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ (z : ℂ), ∀ F ∈ Θ, ∀ F' ∈ Θ, A g (z • F + F') = z • A g F + A g F'
  one : ∀ F ∈ Θ, A 1 F = F
  mul : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, ∀ F ∈ Θ, A (g * g') F = A g (A g' F)
  unit : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ F ∈ Θ, ∀ E ∈ Θ, ip (A g F) (A g E) = ip F E
  cont : ∀ F ∈ Θ, ∀ E ∈ Θ, ContinuousOn (fun g => ip (A g F) E) (Formalism.QuantumDeterminants.UH G)
  der : ∀ X : Mn n, Xᴴ * G + G * X = 0 → ∀ P P', PolDer A pt X P P' → ∀ E ∈ Θ,
    HasDerivAt (fun t : ℝ => ip (A (NormedSpace.exp (t • X)) (pt P)) E) (ip (pt P') E) 0

def Coef {r s : ℕ} {T₀ : GrpData (p * r + q * s) (p * s + q * r)} {T₁ : GrpData p q} {T₂ : GrpData r s}
    (F : FockData T₀ T₁ T₂) (A : Mn n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ))
    (ip : (Z → ℂ) → (Z → ℂ) → ℂ) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] Pol p q r s) (φ : Mat p q → Mn n) (m : ℤ) (N : ℝ) : Prop :=
  0 < N ∧ (∀ P Q, ip (pt P) (pt Q) = (N : ℂ) * ⟪F.ι (κ Q), F.ι (κ P)⟫_ℂ) ∧
    ∀ (g : T₁.G) P Q, ip (A (φ ((T₁.cov g : GL (Ix p q) ℂ) : Mat p q)) (pt P)) (pt Q) =
      (N : ℂ) * ((T₁.sq g : ℂˣ) : ℂ) ^ m * ⟪F.ι (κ Q), F.π (g, 1) (F.ι (κ P))⟫_ℂ

end Side

def IsFrameOf {n : ℕ} (G s : Mn n) (ε : Fin n → Bool) (fr : Mn n) : Prop :=
  IsUnit fr ∧ frᴴ * Formalism.REAL.Jm ε * fr = G ∧ s = fr⁻¹ * Formalism.REAL.Jm ε * fr

theorem isFrameOf_model {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    IsFrameOf (gramAt D V τ) (cart M τ) (M.ε τ) (M.fr τ) := ⟨M.fr_unit τ, M.fr_gram τ, rfl⟩

section Theta

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}

def DerAll (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (γ : ℝ → GA D S × GA D T) (F F' : WO S T → ℂ) : Prop :=
  (∀ g z, HasDerivAt (fun t : ℝ => ω (g * γ t) F z) (ω g F' z) 0) ∧
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ E, IsThetaFunO ψ S T E → HasDerivAt (fun t : ℝ => ipTh μ 𝓕 (ω (γ t) F) E) (ipTh μ 𝓕 F' E) 0

def QuadGen (θ : InfFam D) (τ : D.what₂.Tau) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (γ : ℝ → GA D S × GA D T) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℂ) (z z' : Fin k → Matrix (Fin T.rank) (Fin S.rank) ℂ) (lam : ℂ),
    ∀ F, IsThetaFunO ψ S T F → DerAll ψ ω γ F
      ((∑ i, c i • dRho (heisO ψ S T) θ τ (z i) (dRho (heisO ψ S T) θ τ (z' i) F)) + lam • F)

def LieAt (θ : InfFam D) (τ : D.what₂.Tau) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (εS : Fin S.rank → Bool) (frS : Mn S.rank) (εT : Fin T.rank → Bool) (frT : Mn T.rank) (aS aT : ℚ)
    (pt : LPol T.rank S.rank → (WO S T → ℂ)) : Prop :=
  (∀ X ∈ lieAt S τ, ∀ P, DerAll ψ ω (fun t => (oneP θ S τ X t, 1)) (pt P)
    (pt (locS εS εT ((frS * X * frS⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P))) ∧
  ∀ Y ∈ lieAt T τ, ∀ P, DerAll ψ ω (fun t => (1, oneP θ T τ Y t)) (pt P)
    (pt (locT εS εT (frT * Y * frT⁻¹) P + ((aS : ℂ) * Y.trace) • P))

end Theta

def Centred (D : D7) (al be ga de : List ℚ) : Prop :=
  HypA D.R.t al be ga de ∧ (∀ x ∈ al ++ be ++ ga ++ de, ((D.R.t : ℚ) + 3) / 2 ≤ |x|) ∧
    (NodeGap D → HypG D.R.t al be ga de)

def ForPair (D : D7)
    (C : ∀ (i : Fin D.R.m) (M' : DSModel (Wc D i) (parHol D i)) (θ : InfFam D) (_ : CoefA (Vc D i))
      (_ : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
      (_ : PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ)), Prop) : Prop :=
  ∀ (i : Fin D.R.m) (M : DSModel (Vc D i) (parDef D i)) (M' : DSModel (Wc D i) (parHol D i))
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)),
    IsInfFam θ → IsWeilDatumO ψ (Vc D i) (Wc D i) χS χT ω →
    (∀ τ, HasInfExp D χS τ (-(D.hc τ).e i) ∧ HasInfExp D χT τ (-(D.hc τ).e i - 1 / 2)) →
    ∀ (c : CoefA (Vc D i)), c.Is → (∃ pr, IsDualPair θ M c pr) →
    ∀ (BV : D.what₂.Tau → Mn (Vc D i).rank) f,
      (∀ τ, IsFockAt ψ θ (Vc D i) (Wc D i) τ 1 (cart M' τ) (BV τ) (onb M' τ) f) →
      C i M' θ c ω (pureTensorO ψ θ (Vc D i) (Wc D i) (fun _ => 1) (cart M') BV (onb M') f)

def IoEx (D : D7) : Prop := ForPair D fun i M' θ c ω pt => ∃ io, IsIoW θ M' c ω pt (RealDat.Delta i) io

def IoUniq (D : D7) : Prop :=
  ForPair D fun i M' θ c ω pt => ∀ io io', IsIoW θ M' c ω pt (RealDat.Delta i) io →
    IsIoW θ M' c ω pt (RealDat.Delta i) io' → ∃ a : ℂ, ‖a‖ = 1 ∧ io' = a • io

def IoHarm (D : D7) : Prop :=
  ForPair D fun i M' θ c ω pt => ∀ io, IsIoW θ M' c ω pt (RealDat.Delta i) io →
    ∃ d, ∀ x w τ, IsHarm M' τ (actTgt θ ω τ) pt d (io x w)

end GlobalTheory.ArchRec

end
