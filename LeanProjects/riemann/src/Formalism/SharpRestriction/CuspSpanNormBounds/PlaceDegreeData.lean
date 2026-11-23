import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementMass
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.SharpRestriction.CuspSpanNormBounds.DstarEq
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.PlaceDegreeData

open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S

def qOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = false).card

def pOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = true).card

def decBound {n : ℕ} (q : ℕ) (h : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.exp (-(h / 8) * min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * (q : ℝ))))

def wtF {n : ℕ} (lam : Fin n → ℝ) (X km : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∏ i : Fin (n - 1),
    (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^
      (-(lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1))

def rank1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : H →L[ℂ] H :=
  (innerSL ℂ x).smulRight x

def phLoc {n : ℕ} (ε : Fin n → Bool) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Formalism.REAL.UJ ε → ℂ :=
  fun g => ((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star (coefOn σ w w g)

def IsOpInt {n : ℕ} (ε : Fin n → Bool) {Hp : Type*} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp]
    (π : Matrix (Fin n) (Fin n) ℂ → (Hp →L[ℂ] Hp)) (φ : Formalism.REAL.UJ ε → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ (Formalism.REAL.muG ε) ∧
    ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π (umat g) y⟫_ℂ ∂(Formalism.REAL.muG ε)

def phe (I : AutInst) (ph : I.Ginf → ℂ) (e : I.Gf → ℂ) : I.GA → ℂ := fun x => ph x.1 * e x.2

def fdegAll (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def phOf (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : I.Ginf → ℂ :=
  fun g => ((fdegAll I σ w : ℝ) : ℂ) * star (∏ v, coefOn (σ v) (w v) (w v) (g v))

def HidaSetting (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (μf : Measure I.Gf) (g g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  n₀ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧
    Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧
    I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀

def q0At (I : AutInst) (v : InfinitePlace I.F) : ℕ := min (I.pAt v) (I.qAt v)

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) (lowKSub ε lam σ) ∧
        ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → μ ≠ Formalism.QuantumDeterminants.lowK ε lam →
          vNormSq ε (Formalism.QuantumDeterminants.lowK ε lam) < vNormSq ε μ

section HC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def thetaJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)

def reJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X + thetaJ ε X)

def imJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (X - thetaJ ε X)

def rdC {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => rdM (reJ ε X) f g + Complex.I * rdM (imJ ε X) f g

def rdCWord {n : ℕ} (ε : Fin n → Bool) :
    List (Matrix (Fin n) (Fin n) ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | [], f => f
  | X :: w, f => rdC ε X (rdCWord ε w f)

def gelfandOp {n : ℕ} (ε : Fin n → Bool) (k : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (k + 1) → Fin n,
    rdCWord ε (List.ofFn fun i : Fin (k + 1) => Matrix.single (a i) (a (finRotate (k + 1) i)) (1 : ℂ)) f g

def IsZFinOn {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ (N : ℕ) (F : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F i)) ∧
    (∃ c : Fin N → ℂ, ∀ g ∈ UJset ε, f g = ∑ i, c i * F i g) ∧
    ∀ (k : ℕ) (i : Fin N), ∃ c : Fin N → ℂ, ∀ g ∈ UJset ε, gelfandOp ε k (F i) g = ∑ j, c j * F j g

def IsKFinFunOn {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ (N : ℕ) (F : Fin N → Matrix (Fin n) (Fin n) ℂ → ℂ), ∀ k₁ ∈ Formalism.REAL.Kset ε, ∀ k₂ ∈ Formalism.REAL.Kset ε,
    ∃ c : Fin N → ℂ, ∀ g ∈ UJset ε, f (k₁ * g * k₂) = ∑ i, c i * F i g

def IsDSCoef {n : ℕ} (ε : Fin n → Bool) (φ : Formalism.REAL.UJ ε → ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H),
    Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ ∧ φ = coefOn σ v w

def adm3 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsKFinFunOn ε f → IsZFinOn ε f → MemLp (fun g : Formalism.REAL.UJ ε => f (umat g)) 2 (Formalism.REAL.muG ε) →
    ∃ (N : ℕ) (φ : Fin N → Formalism.REAL.UJ ε → ℂ), (∀ i, IsDSCoef ε (φ i)) ∧ ∀ g, f (umat g) = ∑ i, φ i g

end HC

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def covRad {N : ℕ} (L : Set (EuclideanSpace ℝ (Fin N))) : ℝ := ⨆ x, Metric.infDist x L

def dualLat {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ x ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}

def firstMin {N : ℕ} (S : Set (EuclideanSpace ℝ (Fin N))) : ℝ :=
  sInf {r | ∃ y ∈ S, y ≠ 0 ∧ r = ‖y‖}

def adm5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (N : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) [DiscreteTopology L], IsZLattice ℝ L →
    covRad (L : Set (EuclideanSpace ℝ (Fin N))) * firstMin (dualLat L) ≤ (N : ℝ) / 2

def metIp {E : Type} [Field E] [NumberField E] {j : ℕ} (Hm : (E →+* ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (x y : Fin j → E) : ℝ :=
  ∑ τ : E →+* ℂ, (∑ a, ∑ b, star (τ (x a)) * Hm τ a b * τ (y b)).re

def htZ {E : Type} [Field E] [NumberField E] {j : ℕ} (Hm : (E →+* ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (R : Submodule (𝓞 E) (Fin j → E)) : ℝ := by
  classical
  exact if h : ∃ N : ℕ, Nonempty (Module.Basis (Fin N) ℤ R) then
    (Matrix.of fun a b : Fin h.choose =>
      metIp Hm ((h.choose_spec.some a : R) : Fin j → E) ((h.choose_spec.some b : R) : Fin j → E)).det
  else 0

def degW {E : Type} [Field E] [NumberField E] {j : ℕ} (Hm : (E →+* ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (W : Submodule E (Fin j → E)) : ℝ :=
  -(1 / 2) * Real.log (htZ Hm (Λ ⊓ W.restrictScalars (𝓞 E)))

def slopeW {E : Type} [Field E] [NumberField E] {j : ℕ} (Hm : (E →+* ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (A B : Submodule E (Fin j → E)) : ℝ :=
  (degW Hm Λ B - degW Hm Λ A) / ((Module.finrank E B : ℝ) - (Module.finrank E A : ℝ))

def IsHNChain {E : Type} [Field E] [NumberField E] {j : ℕ} (Hm : (E →+* ℂ) → Matrix (Fin j) (Fin j) ℂ)
    (Λ : Submodule (𝓞 E) (Fin j → E)) (s : ℕ) (W : ℕ → Submodule E (Fin j → E)) : Prop :=
  W 0 = ⊥ ∧ W s = ⊤ ∧ (∀ i < s, W i < W (i + 1)) ∧
    (∀ i, i + 2 ≤ s → slopeW Hm Λ (W (i + 1)) (W (i + 2)) < slopeW Hm Λ (W i) (W (i + 1))) ∧
    ∀ i < s, ∀ U : Submodule E (Fin j → E), W i < U → U ≤ W (i + 1) →
      slopeW Hm Λ (W i) U ≤ slopeW Hm Λ (W i) (W (i + 1))

def adm6 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Λ.FG →
      Submodule.span E (Λ : Set (Fin j → E)) = ⊤ →
    ∀ Hm : (E →+* ℂ) → Matrix (Fin j) (Fin j) ℂ, (∀ τ, (Hm τ).PosDef) →
      (∀ τ : E →+* ℂ, Hm ((starRingEnd ℂ).comp τ) = (Hm τ).map (starRingEnd ℂ)) →
      (∃ (s : ℕ) (W : ℕ → Submodule E (Fin j → E)), IsHNChain Hm Λ s W) ∧
      ∀ (s s' : ℕ) (W W' : ℕ → Submodule E (Fin j → E)), IsHNChain Hm Λ s W → IsHNChain Hm Λ s' W' →
        s = s' ∧ ∀ i ≤ s, W i = W' i

def adm7 (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∃ r : ℝ, Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * dedekindZeta E (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds (r : ℂ)) ∧
      |r| ≤ (C * Real.log (|(discr E : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HermitianLatticesTheory.fDeg E : ℝ))))) ^
        (2 * Formalism.HermitianLatticesTheory.fDeg E)

def CountData (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  (∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧
    I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧
    I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re

def adm8 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
      FiniteDimensional ℂ (I.eHom σs μf fund R Re)

def admitted (D : Formalism.BasicNotions.D7) (Cres : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D

def Conclusion1 (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), n₀ ≤ n → qOf ε ^ 2 ≤ n → Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      ∀ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → Formalism.REAL.inP ε X →
        ‖E.comp ((σ (k * NormedSpace.exp X)).comp E)‖ ≤ decBound (qOf ε) h X

def DiscreteSeriesLowestKTypeFormula (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ w : H, IsHighestUnit ε lam σ w →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inP ε X →
        (E ∘L σ (NormedSpace.exp X) ∘L E =
          ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℂ) •
            ∫ kk : Formalism.REAL.KG ε, ((wtF lam X (Formalism.REAL.toMK kk) : ℝ) : ℂ) • rank1 (σ (Formalism.REAL.toMK kk) w)
              ∂(Formalism.REAL.muK ε)) ∧
        (E ∘L σ (NormedSpace.exp X) ∘L E).IsPositive

def LowestKTypePositivity (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inP ε X → ∀ x ∈ lowKSub ε lam σ,
        (⟪x, σ (NormedSpace.exp X) x⟫_ℂ).im = 0 ∧ 0 ≤ (⟪x, σ (NormedSpace.exp X) x⟫_ℂ).re

def DiscreteSeriesDecayBound (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      ∀ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → Formalism.REAL.inP ε X →
        ‖E.comp ((σ (k * NormedSpace.exp X)).comp E)‖ ≤ decBound (min (pOf ε) (qOf ε)) h X

def DiscreteSeriesDecayMinusSigns (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      ∀ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → Formalism.REAL.inP ε X →
        ‖E.comp ((σ (k * NormedSpace.exp X)).comp E)‖ ≤ decBound (qOf ε) h X

def MatrixCoefficientIntegrable (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ w : H, IsLowUnit ε lam σ w →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      Integrable (phLoc ε σ w) (Formalism.REAL.muG ε)

def phA {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (d : ℝ)
    (σ : G →* (H →L[ℂ] H)) (w : H) : G → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsOpIntA {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {Hp : Type*} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (φ : G → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ μ ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def AbstractGroupProjectorExists (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ x, Continuous fun g => σ g x) →
    ∀ d : ℝ, 0 < d →
    (∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) →
    ∀ w : H, ‖w‖ = 1 → Integrable (fun g => ⟪w, σ g w⟫_ℂ) μ →
      (∀ g : G, star (phA d σ w g⁻¹) = phA d σ w g) ∧
      (∀ x y : G, ∫ g, phA d σ w g * phA d σ w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * phA d σ w y) ∧
      ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
        (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) →
        (∃ P : Hp →L[ℂ] Hp, IsOpIntA μ π (phA d σ w) P) ∧
        ∀ P : Hp →L[ℂ] Hp, IsOpIntA μ π (phA d σ w) P →
          IsStarProjection P ∧
          (∀ x : G, P ∘L π x ∘L P = ⟪w, σ x w⟫_ℂ • P) ∧
          (∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
            (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
            ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : G) (u : H), io (σ g u) = π g (io u)) ∧
          ((LinearMap.range (P : Hp →ₗ[ℂ] Hp) : Submodule ℂ Hp) : Set Hp) =
            {v | ∃ io : H →L[ℂ] Hp, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w}

def LocalProjectorRealPlace (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ w : H, IsLowUnit ε lam σ w →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      Integrable (phLoc ε σ w) (Formalism.REAL.muG ε) ∧
      (∀ g : Formalism.REAL.UJ ε, star (phLoc ε σ w g⁻¹) = phLoc ε σ w g) ∧
      (∀ x y : Formalism.REAL.UJ ε, ∫ g, phLoc ε σ w g * phLoc ε σ w (x⁻¹ * g⁻¹ * y) ∂(Formalism.REAL.muG ε) =
        coefOn σ w w x * phLoc ε σ w y) ∧
      ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
        (π : Matrix (Fin n) (Fin n) ℂ → (Hp →L[ℂ] Hp)), IsURepOn (UJset ε) π →
        (∃ P : Hp →L[ℂ] Hp, IsOpInt ε π (phLoc ε σ w) P) ∧
        ∀ P : Hp →L[ℂ] Hp, IsOpInt ε π (phLoc ε σ w) P →
          IsStarProjection P ∧
          (∀ x : Formalism.REAL.UJ ε, P ∘L π (umat x) ∘L P = coefOn σ w w x • P) ∧
          (∀ v ∈ LinearMap.range (P : Hp →ₗ[ℂ] Hp), ‖v‖ = 1 →
            (∀ g : Formalism.REAL.UJ ε, coefOn π v v g = coefOn σ w w g) ∧
            ∃ io : H →ₗᵢ[ℂ] Hp, io w = v ∧ ∀ (g : Formalism.REAL.UJ ε) (u : H), io (σ (umat g) u) = π (umat g) (io u)) ∧
          ((LinearMap.range (P : Hp →ₗ[ℂ] Hp) : Submodule ℂ Hp) : Set Hp) =
            {v | ∃ io : H →L[ℂ] Hp, (∀ g : Formalism.REAL.UJ ε, io ∘L σ (umat g) = π (umat g) ∘L io) ∧ v = io w}

def ConclB (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (hL1 hP : Prop) : Prop :=
  (hL1 → Integrable (phOf I σ w) (Measure.pi fun v => Formalism.REAL.muG (I.ε v))) ∧
    (hP → ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConv μf fund R (phe I (phOf I σ w) e) T →
      IsStarProjection T ∧
      FiniteDimensional ℂ (LinearMap.range (T : I.L2 μf fund →ₗ[ℂ] I.L2 μf fund)) ∧
      Module.finrank ℂ (LinearMap.range (T : I.L2 μf fund →ₗ[ℂ] I.L2 μf fund)) =
        I.Dcount σs μf fund R Re ∧
      ∀ Fv ∈ LinearMap.range (T : I.L2 μf fund →ₗ[ℂ] I.L2 μf fund), I.IsCuspFn (I.muA μf) (I.ext Fv))

def Conclusion2 (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    ConclB I σ w σs μf fund R e Re
      (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
      ((∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) ∧
        ∀ v, C * (I.n : ℝ) ^ 2 * Real.sqrt (q0At I v : ℝ) ≤ h)

def ProjectorBoundNoGapHypothesis (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    ConclB I σ w σs μf fund R e Re True True

def PointsLemma (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTie (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop :=
  (∃ pl : InfinitePlace X.I.F ≃ D.what₂.Tau, AutTie D X pl) ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (X.lam v)) ∧
    (SplitsCompl D.host.E (D.host.g 0) → SplitsCompl X.I.E X.g₀)

def WordCountBound (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (X : RowsAut) (b h : ℝ), RowsTie D X → HidaSetting X.I n₀ A b X.lam X.μf X.g X.g₀ X.e →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (X.I.ε v) (X.lam v) h) →
    C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (b * D.host.rdE) ≤ h →
    Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) →
    Real.log (Real.log b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) →
    |(D.what₂.Dall : ℝ) - D.what₂.Dstar| ≤
      Real.exp (-(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ))) * D.what₂.Dstar

def Stmt (D : Formalism.BasicNotions.D7) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) : Prop :=
  admitted D Cres → DiscreteSeriesLowestKTypeFormula D ∧ DiscreteSeriesDecayBound D ∧ MatrixCoefficientIntegrable D ∧ AbstractGroupProjectorExists D ∧ LocalProjectorRealPlace D ∧ Conclusion2 D n₀ A Cb ∧ PointsLemma D n₀ A C c cb

def HarishChandraFormulaStatement (D : Formalism.BasicNotions.D7) : Prop := adm2 D ∧ adm3 D → DiscreteSeriesLowestKTypeFormula D

def PositivityFromLowestKType (D : Formalism.BasicNotions.D7) : Prop := adm2 D → DiscreteSeriesLowestKTypeFormula D → LowestKTypePositivity D

def IntegralityFromMetric (D : Formalism.BasicNotions.D7) : Prop := DiscreteSeriesLowestKTypeFormula D → DiscreteSeriesDecayBound D

def IntegrabilityFromDecay (D : Formalism.BasicNotions.D7) : Prop := DiscreteSeriesDecayBound D → MatrixCoefficientIntegrable D

def AbstractGroupProjectorForDatum (D : Formalism.BasicNotions.D7) : Prop := AbstractGroupProjectorExists D

def LocalProjectorFromSchur (D : Formalism.BasicNotions.D7) : Prop := adm1 D → MatrixCoefficientIntegrable D → AbstractGroupProjectorExists D → LocalProjectorRealPlace D

def HodgeTateFromSandwich (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A Cb : ℝ) : Prop :=
  adm1 D ∧ adm6 D ∧ adm8 D → DiscreteSeriesDecayBound D → LocalProjectorRealPlace D → Conclusion2 D n₀ A Cb

def TowerRallisLemma (D : Formalism.BasicNotions.D7) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) : Prop :=
  ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Cres ∧ adm8 D → DiscreteSeriesDecayBound D → Conclusion2 D n₀ A Cb → PointsLemma D n₀ A C c cb

def UniformExportStatement : Prop :=
  ∃ c cb : ℝ, 0 < c ∧ 0 < cb ∧ ∀ Cres A : ℝ, 1 ≤ A → ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ Cb ≥ C₀, ∀ C ≥ C₀,
    ∀ D : Formalism.BasicNotions.D7, Stmt D Cres n₀ A Cb C c cb

def ClosedFormProjectorBound : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ Cb ≥ C₀, ∀ D : Formalism.BasicNotions.D7, HodgeTateFromSandwich D n₀ A Cb

def ClosedFormWordCount : Prop :=
  ∃ c cb : ℝ, 0 < c ∧ 0 < cb ∧ ∀ Cres A Cb : ℝ, 1 ≤ A → ∃ (n₀ : ℕ) (C₀ : ℝ), ∀ C ≥ C₀,
    ∀ D : Formalism.BasicNotions.D7, TowerRallisLemma D Cres n₀ A Cb C c cb

def admF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)
def admF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i)
def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)

def admF7 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i) Cres
def admF8 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) : Prop := ∀ x (i : Fm.Ix x), admitted (Fm.D x i) Cres

def FamilyLowestKTypeFormula {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), DiscreteSeriesLowestKTypeFormula (Fm.D x i)

def FamilyLowestKTypePositivity {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), LowestKTypePositivity (Fm.D x i)

def FamilyDiscreteSeriesDecay {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), DiscreteSeriesDecayBound (Fm.D x i)

def FamilyDecayMinusSigns {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), DiscreteSeriesDecayMinusSigns (Fm.D x i)

def ConclusionF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) n₀

def FamilyMatrixCoefficientL1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), MatrixCoefficientIntegrable (Fm.D x i)

def FamilyAbstractProjectorEveryMember {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), AbstractGroupProjectorExists (Fm.D x i)

def FamilyLocalProjectorEveryMember {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), LocalProjectorRealPlace (Fm.D x i)

def ConclusionF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i) n₀ A C

def ConclusionF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), PointsLemma (Fm.D x i) n₀ A C c cb

def FamilyWordCountBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  0 < c ∧ 0 < cb ∧ ∀ x (i : Fm.Ix x), WordCountBound (Fm.D x i) n₀ A C c cb

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) : Prop :=
  AdmF Fm Cres →
    FamilyLowestKTypeFormula Fm ∧ FamilyDiscreteSeriesDecay Fm ∧ FamilyMatrixCoefficientL1 Fm ∧ FamilyAbstractProjectorEveryMember Fm ∧ FamilyLocalProjectorEveryMember Fm ∧ ConclusionF2 Fm n₀ A Cb ∧ ConclusionF3 Fm n₀ A C c cb

def FamilyFormulaStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := admF2 Fm ∧ admF3 Fm → FamilyLowestKTypeFormula Fm

def FamilyPositivityOfLowestKTypeFormula {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := admF2 Fm → FamilyLowestKTypeFormula Fm → FamilyLowestKTypePositivity Fm

def PeriodFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := FamilyLowestKTypeFormula Fm → FamilyDiscreteSeriesDecay Fm

def FamilyIntegrabilityOfDecay {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := FamilyDiscreteSeriesDecay Fm → FamilyMatrixCoefficientL1 Fm

def FamilyAbstractProjector {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := FamilyAbstractProjectorEveryMember Fm

def FamilyLocalProjectorOfAbstractProjector {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := admF1 Fm → FamilyMatrixCoefficientL1 Fm → FamilyAbstractProjectorEveryMember Fm → FamilyLocalProjectorEveryMember Fm

def DeterminantValueFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (n₀ : ℕ) (A Cb : ℝ) : Prop :=
  admF1 Fm ∧ admF6 Fm ∧ admF8 Fm → FamilyDiscreteSeriesDecay Fm → FamilyLocalProjectorEveryMember Fm → ConclusionF2 Fm n₀ A Cb

def FlatLineDegreeFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cres : ℝ) (n₀ : ℕ) (A Cb C c cb : ℝ) : Prop :=
  admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm Cres ∧ admF8 Fm → FamilyDiscreteSeriesDecay Fm → ConclusionF2 Fm n₀ A Cb →
    ConclusionF3 Fm n₀ A C c cb

end Formalism.MainNotions.PlaceDegreeData
