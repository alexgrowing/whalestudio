import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

def NoLow (X : ProvA) (p q : ℕ) {r s : ℕ} (lam' : Ix r s → ℚ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ (MM : GKMod (p - i) (q - i))
    (f : Pol (p - i) (q - i) r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
    Formalism.BasicNotions.TH.IsIntw (X.fock (p - i) (q - i) r s) MM (X.ds r s lam').HK f → f = 0

structure Rule (X : ProvA) {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop where
  pos : 1 ≤ p + q
  pos' : 1 ≤ r + s
  par : IsParam lam
  par' : IsParam lam'
  down : Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam lam'
  line : Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam'
  low : NoLow X p q lam'

def RulePar (X : ProvA) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (p q r s : ℕ) (l₁ l₂ l₁' l₂' : List ℚ), l₁.length = p ∧ l₂.length = q ∧ l₁'.length = r ∧ l₂'.length = s ∧
    Rule X (ofBlocks l₁ l₂ : Ix p q → ℚ) (ofBlocks l₁' l₂' : Ix r s → ℚ) ∧
    S = dualPar (signed l₁ l₂ aT) ∧ S' = dualPar (signed l₁' l₂' aS)

def ThetaPar (t : ℕ) (P P' : SPar) (c c' : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, P = signed (al ++ be) (ga ++ de) c ∧
    ((Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ P' = signed (al ++ block t ++ de) (ga ++ be) c') ∨
      (Formalism.MainNotions.SchurIrreducible.DataARm t al be ga de ∧ P' = signed (al ++ de) (ga ++ block t ++ be) c'))

def PairPar (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (t : ℕ) (P P' : SPar), S = dualPar P ∧ S' = dualPar P' ∧
    ((ThetaPar t P P' aT aS ∧ GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) P) ∨ ThetaPar t P' P aS aT)

def partner (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) : SPar :=
  (P.image fun x => (x.1 - c + c', if x.1 < c then !x.2 else x.2)) ∪ (TPar.block c' t).image fun x => (x, b)

def GapOver (P : SPar) (h : ℚ) : Prop := ∀ x ∈ P, ∀ y ∈ P, x.2 ≠ y.2 → h < |x.1 - y.1|

def att (c : ℚ) (n : ℕ) : ℚ := if Odd n then c - 1 / 2 else c

variable {D : D7}

structure Inputs (D : D7) (X : ProvA) : Prop where
  chosen : GlobalTheory.Chain.RealIt.ChosenSeries X
  hc : GlobalTheory.Published.HarishChandraModules
  decay : GlobalTheory.Published.CuspRapidDecay
  bridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D
  vacChar : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D
  lie : LieFockAll D
  cpt : CompactFockAll D
  dense : FockDense D
  laws : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D
  const : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D
  ext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D

def IsWeilExp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (aS aT : D.what₂.Tau → ℚ) (ω : WRep V W) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χS χT ω ∧ ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)

def LowFock (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ), IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
      Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

def LowAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f' : WO V' W → ℂ), IsThetaFunO ψ V' W f' →
      Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

def CuspAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (_M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      IsCuspFun V (Lift.liftInt ν 𝓕 (thetaKO ω) f (F v))

def LiftsM (θ : InfFam D) {A B : HSp D} {SA SB : D.what₂.Tau → SPar} (MA : DSModel A SA) (MB : DSModel B SB) {P : Type}
    (ν : Measure (GA D A)) (𝓕 : Set (GA D A)) (K : P → GA D B → GA D A → ℂ) (It : P → SmT MA → SmT MB) : Prop :=
  ∀ F ∈ MultT θ MA ∅ 1, ∃ F' ∈ MultT θ MB ∅ 1, ∀ (p : P) (v : SmT MA) (h : GA D B),
    IntegrableOn (fun g => K p h g * F v g) 𝓕 ν ∧ ∫ g in 𝓕, K p h g * F v g ∂ν = F' (It p v) h

def PairLifts (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (f₀ : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsVacVec ψ θ M M' f₀ →
      IsItW θ M M' ω (ptOf ψ θ M M' f₀) It →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ f, IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f →
      LiftsM θ M' M ν 𝓕 (fun P g h => thetaKO ω g h (ptOf ψ θ M M' f P)) fun P v => It P v

structure IsIntwF {V W : HSp D} {S S' : D.what₂.Tau → SPar} {Z P : Type} (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (pt : P → (Z → ℂ))
    (It : P → SmT M' →ₗ[ℂ] SmT M) : Prop where
  ne : ∃ φ, It φ ≠ 0
  bdd : ∀ φ w, ∃ c : ℝ, ∀ v : M'.Vec,
    ‖ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖
  eqK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ φ', pt φ' = ω (atTau θ V τ g, 1) (pt φ) →
    ∀ v, inclT M (It φ' v) = actT M τ g (inclT M (It φ v))
  eqg : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ Y t, 1) (pt φ) z) (pt φ' z) 0) →
    ∀ v, DerT M τ Y (It φ v) (It φ' v)
  invK : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ φ' v v', pt φ' = ω (1, atTau θ W τ h) (pt φ) →
    inclT M' v' = actT M' τ h (inclT M' v) → It φ' v' = It φ v
  invg : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ φ' v v', (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (pt φ) z) (pt φ' z) 0) →
    DerT M' τ Y v v' → It φ' v + It φ v' = 0

structure ModelTr (σ : ℂ →+* ℂ) (ε : Bool) (θ : InfFam D) {V : HSp D} {S S₁ : D.what₂.Tau → SPar}
    (M₁ : DSModel (sgn ε V) S₁) (M : DSModel V S) (κ : SmT M₁ ≃+ SmT M) : Prop where
  smul : ∀ (c : ℂ) x, κ (c • x) = σ c • κ x
  cart : ∀ τ, cart M₁ τ = sgnM ε (cart M τ)
  act : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y,
    inclT M₁ y = actT M₁ τ g (inclT M₁ x) ↔ inclT M (κ y) = actT M τ g (inclT M (κ x))
  der : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ x y, DerT M₁ τ Y x y ↔ DerT M τ Y (κ x) (κ y)
  ell : ∀ w₁, ∃ w, ∀ x, ellT M₁ w₁ (inclT M₁ x) = σ (ellT M w (inclT M (κ x)))
  vec : ∀ v₁ : M₁.Vec, ∃ v : M.Vec, κ (PiTensorProduct.tprod ℂ v₁) = PiTensorProduct.tprod ℂ v ∧
    ∀ τ, ‖(v τ : M.H τ)‖ = ‖(v₁ τ : M₁.H τ)‖
  mult : ∀ F ∈ MultT θ M ∅ 1, ∃ F₁ ∈ MultT θ M₁ ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))
  mult' : ∀ F₁ ∈ MultT θ M₁ ∅ 1, ∃ F ∈ MultT θ M ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))

structure SgnLaw (θ : InfFam D) (ε : Bool) (V : HSp D) : Prop where
  rat : ∀ g, g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V
  fin : ∀ g, g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V
  inf : ∀ g, g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V
  grp : ∀ τ, Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ)
  lie : ∀ τ, lieAt (sgn ε V) τ = lieAt V τ
  atTau : ∀ τ g, ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g
  meas : ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν

def adjO (S T : HSp D) (y : WO T S) : WO S T :=
  HMul.hMul (HMul.hMul (T.gram⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose)
    (S.gram.map (incA D))

def dag (S T : HSp D) (f : WO S T → ℂ) : WO T S → ℂ := fun y => starRingEnd ℂ (f (adjO S T y))

structure AdjLaw (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where
  invol : ∀ x : WO S T, adjO S T (adjO T S x) = x
  add : ∀ y y' : WO T S, adjO S T (y + y') = adjO S T y + adjO S T y'
  cont : Continuous (adjO S T)
  sympl : ∀ y y' : WO T S, symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y'
  act : ∀ (g : GA D S) (h : GA D T) (y : WO T S), adjO S T (actO T S h g y) = actO S T g h (adjO S T y)
  rat : ∀ y : WO T S, adjO S T y ∈ ratL T S ↔ y ∈ ratL S T
  half : ∀ (e : AE D) (y : WO T S), IsHalf e y → IsHalf (cA D e) (adjO S T y)
  Heisenberg₂ : ∀ (y : WO T S) (f : WO S T → ℂ), heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f)
  theta : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f)

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]
      exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases hab : a = b
        · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
        · simp [Formalism.REAL.Jm, hab]
      show _ = gramAt D (neg V) τ
      rw [e, h, ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn ε A).cart τ = sgnM ε (A.cart τ) := by

  have hJ : Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) = sgnM ε (Formalism.REAL.Jm (A.ε τ)) := by
    cases ε
    · simp [sgnM]
    · simp only [sgnM, cond_true, Formalism.REAL.Jm, Bool.true_xor]
      rw [Matrix.diagonal_neg]
      congr 1
      funext a
      cases A.ε τ a <;> simp
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) * A.fr τ = sgnM ε ((A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
  rw [hJ]
  cases ε
  · rfl
  · simp only [sgnM, cond_true, Matrix.mul_neg, Matrix.neg_mul]

end GlobalTheory.PairLift

end
