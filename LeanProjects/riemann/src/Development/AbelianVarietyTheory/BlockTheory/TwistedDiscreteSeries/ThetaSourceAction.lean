import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Mat (n : ℕ) : Type := Matrix (Fin n) (Fin n) ℂ

structure IsUnitLieAct {n : ℕ} (L : Set (Mat n)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a : Mat n → Module.End ℂ H) : Prop where
  add : ∀ X ∈ L, ∀ Y ∈ L, a (X + Y) = a X + a Y
  smul : ∀ (c : ℝ), ∀ X ∈ L, a (c • X) = (c : ℂ) • a X
  lie : ∀ X ∈ L, ∀ Y ∈ L, a (X * Y - Y * X) = a X * a Y - a Y * a X
  skew : ∀ X ∈ L, ∀ x y, ⟪a X x, y⟫_ℂ = -⟪x, a X y⟫_ℂ

variable {D : D7}

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)

def kfin : Submodule ℂ (M.H τ) := Submodule.span ℂ {v | IsKFin (M.ε τ) (M.σ τ) v}

def VecDer (X : Mat V.rank) (v v' : kfin M τ) : Prop :=
  HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (v' : M.H τ) 0

def UnitHighest (v : kfin M τ) : Prop := IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) (v : M.H τ)

def ofFr (X : Mat V.rank) : Mat V.rank := (M.fr τ)⁻¹ * X * M.fr τ

end Model

section Pol

variable {ι Z : Type}

def PolDer {n : ℕ} (A : Mat n → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (X : Mat n)
    (P P' : MvPolynomial ι ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => A (NormedSpace.exp (t • X)) (pt P) z) (pt P' z) 0

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
  (A : Mat V.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ))

def IsHarm (d : ℕ) (P : MvPolynomial ι ℂ) : Prop :=
  P.IsHomogeneous d ∧ ∀ X ∈ lieAt V τ, cart M τ * X = -(X * cart M τ) →
    ∃ P', PolDer A pt X P P' ∧ P'.IsHomogeneous (d + 2)

def KilledBy (a b : Fin V.rank) (P : MvPolynomial ι ℂ) : Prop :=
  ∃ PX PY, PolDer A pt (ofFr M τ (Matrix.single a b 1 - Matrix.single b a 1)) P PX ∧
    PolDer A pt (ofFr M τ (Complex.I • (Matrix.single a b 1 + Matrix.single b a 1))) P PY ∧ PX = Complex.I • PY

def HasWt (μ : Fin V.rank → ℝ) (P : MvPolynomial ι ℂ) : Prop :=
  ∀ x : Fin V.rank → ℝ, A (ofFr M τ (Matrix.diagonal fun a => Complex.exp ((x a : ℂ) * Complex.I))) (pt P) =
    Complex.exp (((∑ a, μ a * x a : ℝ) : ℂ) * Complex.I) • pt P

def IsHi (P : MvPolynomial ι ℂ) : Prop :=
  HasWt M τ A pt (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) P ∧
    ∀ a b, a < b → M.ε τ a = M.ε τ b → KilledBy M τ A pt a b P

def IsLo (P : MvPolynomial ι ℂ) : Prop :=
  HasWt M τ A pt (-Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) P ∧
    ∀ a b, a < b → M.ε τ a = M.ε τ b → KilledBy M τ A pt b a P

def IsInv {U : Type} [AddCommGroup U] [Module ℂ U] (q : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U) : Prop :=
  ∀ X ∈ lieAt V τ, ∀ P P' v v', PolDer A pt X P P' → VecDer M τ X v v' → q P' v + q P v' = 0

variable {W : HSp D} {S' : D.what₂.Tau → SPar} (N : DSModel W S') (B : Mat W.rank → (Z → ℂ) → (Z → ℂ))

def IsLiftMap {U : Type} [AddCommGroup U] [Module ℂ U] (R : Mat W.rank → U → U → Prop)
    (q : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U) : Prop :=
  IsInv M τ A pt q ∧ ∀ Y ∈ lieAt W τ, ∀ P P', PolDer B pt Y P P' → ∀ v, R Y (q P v) (q P' v)

def IsJoint (Φ : MvPolynomial ι ℂ) : Prop :=
  Φ ≠ 0 ∧ (∃ d, IsHarm M τ A pt d Φ ∧ IsHarm N τ B pt d Φ) ∧ IsLo M τ A pt Φ ∧ IsHi N τ B pt Φ

structure LiftLaw : Prop where
  joint_ex : ∃ Φ, IsJoint M τ A pt N B Φ
  joint_uniq : ∀ Φ Φ', IsJoint M τ A pt N B Φ → IsJoint M τ A pt N B Φ' → ∃ c : ℂ, Φ' = c • Φ
  unitary : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (a : Mat W.rank → Module.End ℂ U),
    IsUnitLieAct (lieAt W τ) a → ∀ q : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U,
    IsLiftMap M τ A pt B (fun Y x y => y = a Y x) q → q ≠ 0 →
      (∃ e : kfin N τ →ₗ[ℂ] U, Function.Injective e ∧
        (∀ Y ∈ lieAt W τ, ∀ x x', VecDer N τ Y x x' → e x' = a Y (e x)) ∧
        LinearMap.range e = Submodule.span ℂ {y | ∃ P v, y = q P v}) ∧
      ∀ Φ, IsJoint M τ A pt N B Φ → (∀ v, UnitHighest M τ v → q Φ v ≠ 0) ∧
        ∀ q', IsLiftMap M τ A pt B (fun Y x y => y = a Y x) q' → q' Φ = q Φ → q' = q
  line : ∃ q₀ : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] kfin N τ, q₀ ≠ 0 ∧ IsLiftMap M τ A pt B (VecDer N τ) q₀ ∧
    ∀ q, IsLiftMap M τ A pt B (VecDer N τ) q → ∃ c : ℂ, q = c • q₀

def ZetaLaw (ip : (Z → ℂ) → (Z → ℂ) → ℂ) : Prop :=
  ∀ Φ, IsJoint M τ A pt N B Φ → ∀ v, UnitHighest N τ v →
    ∀ μ : Measure (Formalism.REAL.UJ (N.ε τ)), μ.IsHaarMeasure →
      Integrable (coefOn (ε := N.ε τ) (N.σ τ) (v : N.H τ) v) μ ∧
      Integrable (fun g => ip (B (ofFr N τ (umat g)) (pt Φ)) (pt Φ) * star (coefOn (N.σ τ) (v : N.H τ) v g)) μ ∧
      (∃ z : ℝ, 0 < z ∧
        ∫ g, ip (B (ofFr N τ (umat g)) (pt Φ)) (pt Φ) * star (coefOn (N.σ τ) (v : N.H τ) v g) ∂μ = (z : ℂ)) ∧
      ((∀ a, M.ε τ a = true) → ∀ d : ℝ, IsFdeg μ (N.σ τ) d →
        ∫ g, ip (B (ofFr N τ (umat g)) (pt Φ)) (pt Φ) * star (coefOn (N.σ τ) (v : N.H τ) v g) ∂μ =
          ip (pt Φ) (pt Φ) / (d : ℂ))

def NoLift : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (q : MvPolynomial ι ℂ →ₗ[ℂ] kfin M τ →ₗ[ℂ] U), IsInv M τ A pt q → q = 0

end Pol

section Weil

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)

def IsAdapted {n : ℕ} (G s B : Mat n) : Prop :=
  ∃ ε : Fin n → Bool, Bᴴ * G * B = Formalism.REAL.Jm ε ∧ s * B = B * Formalism.REAL.Jm ε

example (n : ℕ) : IsAdapted (1 : Mat n) 1 1 := ⟨fun _ => true, by simp [Formalism.REAL.Jm], by simp [Formalism.REAL.Jm]⟩

def ptAt (τ : D.what₂.Tau) (sS : Mat S.rank) (sT : Mat T.rank) (BS : Mat S.rank) (BT : Mat T.rank) (f : WO S T → ℂ) :
    MvPolynomial (Fin T.rank × Fin S.rank) ℂ → (WO S T → ℂ) :=
  pureTensorL (fun k : Fin T.rank × Fin S.rank => aPlus (heisO ψ S T) θ τ (cplxO sS sT) (unitMap BS BT k.1 k.2)) f

def actSrc {S T : HSp D} (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau) (g : Mat S.rank)
    (F : WO S T → ℂ) : WO S T → ℂ := ω (atTau θ S τ g, 1) F

def actTgt {S T : HSp D} (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau) (h : Mat T.rank)
    (F : WO S T → ℂ) : WO S T → ℂ := ω (1, atTau θ T τ h) F

def ipTh {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (F F' : WO S T → ℂ) : ℂ :=
  ∫ w in 𝓕, F w * star (F' w) ∂μ

structure IsFockAt (τ : D.what₂.Tau) (sS : Mat S.rank) (sT : Mat T.rank) (BS : Mat S.rank) (BT : Mat T.rank)
    (f : WO S T → ℂ) : Prop where
  inf : IsInfFam θ
  onS : IsAdapted (gramAt D S τ) sS BS
  onT : IsAdapted (gramAt D T τ) sT BT
  theta : IsThetaFunO ψ S T f
  ne : f ≠ 0
  vac : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f

theorem isAdapted_model {V : HSp D} {P : D.what₂.Tau → SPar} (M : DSModel V P) (τ : D.what₂.Tau) :
    IsAdapted (gramAt D V τ) (cart M τ) (onb M τ) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  refine ⟨M.ε τ, ?_, ?_⟩
  · rw [← M.fr_gram τ, onb]
    calc (M.fr τ)⁻¹ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹
        = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  · rw [cart, onb, Matrix.mul_assoc, h1, Matrix.mul_one]

end Weil

section Pair

variable (τ : D.what₂.Tau) (S T : HSp D) (aS aT : ℚ)

def ForAllAt (pS pT : SPar)
    (C : ∀ {PS PT : D.what₂.Tau → SPar}, DSModel S PS → DSModel T PT → (Mat S.rank → (WO S T → ℂ) → (WO S T → ℂ)) →
      (Mat T.rank → (WO S T → ℂ) → (WO S T → ℂ)) → (MvPolynomial (Fin T.rank × Fin S.rank) ℂ → (WO S T → ℂ)) → Prop) :
    Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω →
    HasInfExp D χS τ aS → HasInfExp D χT τ aT →
    ∀ (PS PT : D.what₂.Tau → SPar) (MS : DSModel S PS) (MT : DSModel T PT), PS τ = pS → PT τ = pT →
    ∀ BS BT f, IsFockAt ψ θ S T τ (cart MS τ) (cart MT τ) BS BT f →
      C MS MT (actSrc θ ω τ) (actTgt θ ω τ) (ptAt ψ θ S T τ (cart MS τ) (cart MT τ) BS BT f)

def ToTarget (pS pT : SPar) : Prop :=
  ForAllAt τ S T aS aT pS pT fun MS MT A B pt => LiftLaw MS τ A pt MT B

def ToSource (pS pT : SPar) : Prop :=
  ForAllAt τ S T aS aT pS pT fun MS MT A B pt => LiftLaw MT τ B pt MS A

def ZetaSource (pS pT : SPar) : Prop :=
  ForAllAt τ S T aS aT pS pT fun MS MT A B pt =>
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ZetaLaw MT τ B pt MS A (ipTh μ 𝓕)

def ZetaTarget (pS pT : SPar) : Prop :=
  ForAllAt τ S T aS aT pS pT fun MS MT A B pt =>
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ZetaLaw MS τ A pt MT B (ipTh μ 𝓕)

def NoLowerTarget (pS pT : SPar) : Prop :=
  ∀ (PS PT : D.what₂.Tau → SPar) (MS : DSModel S PS) (_ : DSModel T PT), PS τ = pS → PT τ = pT →
    ∀ (T' : HSp D) (i : ℕ), 1 ≤ i → IsWittLower T T' i →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)), IsWeilDatumO ψ S T' χS χT ω → HasInfExp D χT τ aT →
      ∀ sT BS BT f, IsFockAt ψ θ S T' τ (cart MS τ) sT BS BT f →
        NoLift MS τ (actSrc θ ω τ) (ptAt ψ θ S T' τ (cart MS τ) sT BS BT f)

def NoLowerSource (pS pT : SPar) : Prop :=
  ∀ (PS PT : D.what₂.Tau → SPar) (_ : DSModel S PS) (MT : DSModel T PT), PS τ = pS → PT τ = pT →
    ∀ (S' : HSp D) (i : ℕ), 1 ≤ i → IsWittLower S S' i →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S' × GA D T →* Module.End ℂ (WO S' T → ℂ)), IsWeilDatumO ψ S' T χS χT ω → HasInfExp D χS τ aS →
      ∀ sS BS BT f, IsFockAt ψ θ S' T τ sS (cart MT τ) BS BT f →
        NoLift MT τ (actTgt θ ω τ) (ptAt ψ θ S' T τ sS (cart MT τ) BS BT f)

end Pair

variable (D)

def NodeGap : Prop :=
  ∃ N : ℕ, D.R.rankX' + 1 ≤ N ∧ ∀ τ (i : Fin D.R.m) (h : i.1 + 1 < D.R.m),
    (D.R.t : ℚ) + 2 * (N : ℚ) ^ 3 + 1 ≤ (D.hc τ).b ⟨i.1 + 1, h⟩ - (D.hc τ).b i

def alS (k : Fin D.R.m) (τ : D.what₂.Tau) : ℚ := if Odd ((k : ℕ) + 1) then -(D.hc τ).e k - 1 / 2 else -(D.hc τ).e k

def alT (k : Fin D.R.m) (τ : D.what₂.Tau) : ℚ := if Odd ((k : ℕ) + 1) then -(D.hc τ).e k else -(D.hc τ).e k - 1 / 2

def parHol (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar := parW (Wc D i) (Formalism.L2.NTheta.wtOf D (Wc D i)) τ

def parDef (i : Fin D.R.m) (τ : D.what₂.Tau) : SPar :=
  ((Finset.univ.image (D.hc τ).v) ∪ (Finset.univ.image fun l => -(D.hc τ).b l) ∪
    TPar.block (-(D.hc τ).e i) D.R.t).image fun x => (x - 1 / 2, true)

def ChainTop : Prop :=
  ∀ (k : Fin D.R.m) (τ : D.what₂.Tau) (V W : HSp D),
    ToTarget τ V W (alS D k τ) (alT D k τ) (parA (Ptw D) k τ) (parA (Ptw D) (k + 1) τ) ∧
    ToSource τ V W (alS D k τ) (alT D k τ) (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) ∧
    ZetaSource τ V W (alS D k τ) (alT D k τ) (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ)

def ChainLower : Prop :=
  ∀ (k : Fin D.R.m) (τ : D.what₂.Tau) (V W : HSp D),
    NoLowerTarget τ V W (alT D k τ) (parA (Ptw D) k τ) (parA (Ptw D) (k + 1) τ) ∧
    NoLowerSource τ V W (alS D k τ) (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ)

def PairTop : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    ToTarget τ (Vc D i) (Wc D i) (-(D.hc τ).e i) (-(D.hc τ).e i - 1 / 2) (parDef D i τ) (parHol D i τ) ∧
    ToSource τ (Vc D i) (Wc D i) (-(D.hc τ).e i) (-(D.hc τ).e i - 1 / 2) (dualPar (parDef D i τ))
      (dualPar (parHol D i τ)) ∧
    ZetaTarget τ (Vc D i) (Wc D i) (-(D.hc τ).e i) (-(D.hc τ).e i - 1 / 2) (parDef D i τ) (parHol D i τ)

def PairLower : Prop :=
  ∀ (i : Fin D.R.m) (τ : D.what₂.Tau),
    NoLowerTarget τ (Vc D i) (Wc D i) (-(D.hc τ).e i - 1 / 2) (parDef D i τ) (parHol D i τ)

def ItLaw : Prop :=
  ∀ (k : Fin D.R.m) (V W : HSp D) (P P' : D.what₂.Tau → SPar) (M : DSModel V P) (M' : DSModel W P'),
    P = parB (Ptw D) k → P' = parB (Ptw D) (k + 1) →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω →
      (∀ τ, HasInfExp D χS τ (alS D k τ) ∧ HasInfExp D χT τ (alT D k τ)) →
      ∀ f, (∀ τ, IsFockAt ψ θ V W τ (cart M τ) (cart M' τ) (onb M τ) (onb M' τ) f) →
        ∃ It, IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) It ∧
          ∀ It', IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) It' → ∃ c : ℂ, It' = c • It

def IoLaw : Prop :=
  ∀ (i : Fin D.R.m) (P P' : D.what₂.Tau → SPar) (M : DSModel (Vc D i) P) (M' : DSModel (Wc D i) P'),
    P = parDef D i → P' = parHol D i →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)),
      IsWeilDatumO ψ (Vc D i) (Wc D i) χS χT ω →
      (∀ τ, HasInfExp D χS τ (-(D.hc τ).e i) ∧ HasInfExp D χT τ (-(D.hc τ).e i - 1 / 2)) →
      ∀ (c : CoefA (Vc D i)), c.Is → (∃ pr, IsDualPair θ M c pr) →
      ∀ (BV : D.what₂.Tau → Mat (Vc D i).rank) f,
        (∀ τ, IsFockAt ψ θ (Vc D i) (Wc D i) τ 1 (cart M' τ) (BV τ) (onb M' τ) f) →
        ∃ io, IsIoW θ M' c ω (pureTensorO ψ θ (Vc D i) (Wc D i) (fun _ => 1) (cart M') BV (onb M') f)
            (RealDat.Delta i) io ∧
          (∀ io', IsIoW θ M' c ω (pureTensorO ψ θ (Vc D i) (Wc D i) (fun _ => 1) (cart M') BV (onb M') f)
            (RealDat.Delta i) io' → ∃ a : ℂ, ‖a‖ = 1 ∧ io' = a • io) ∧
          ∃ d, ∀ x w τ, IsHarm M' τ (actTgt θ ω τ)
            (pureTensorO ψ θ (Vc D i) (Wc D i) (fun _ => 1) (cart M') BV (onb M') f) d (io x w)

def ArchOnRecord : Prop :=
  (ChainLower D ∧ PairLower D) ∧ (NodeGap D → ChainTop D ∧ PairTop D ∧ ItLaw D ∧ IoLaw D)

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction

end
