import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section Beta

variable {l : ℕ} [Fact l.Prime]

def zOf (l : ℕ) [Fact l.Prime] {σ : Type} (k : σ) : MvPowerSeries σ ℂ_[l] :=
  PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries σ ℂ_[l]) (logF l)

def beAt {σ : Type} (be : MvPowerSeries (Fin 2) ℂ_[l]) (a b : MvPowerSeries σ ℂ_[l]) : MvPowerSeries σ ℂ_[l] :=
  MvPowerSeries.subst ![a, b] be

def BeCoef (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop := CoefWf be

def BeInv (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop :=
  ∀ u : ℂ_[l], u ^ (l ^ 2 - 1) = 1 → MvPowerSeries.rescale ![u, (u ^ l)⁻¹] be = be

def BeVan (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop :=
  ∀ n : Fin 2 →₀ ℕ, (n 0 = 0 ∨ n 1 = 0 ∨ (n 0 = 1 ∧ n 1 = 1)) → MvPowerSeries.coeff n be = 0

def BeBiadd (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop :=
  SimeqW (beAt be (zOf l 0 + zOf l 1) (zOf l 2) : MvPowerSeries (Fin 3) ℂ_[l])
      (beAt be (zOf l 0) (zOf l 2) + beAt be (zOf l 1) (zOf l 2)) ∧
    SimeqW (beAt be (zOf l 0) (zOf l 1 + zOf l 2) : MvPowerSeries (Fin 3) ℂ_[l])
      (beAt be (zOf l 0) (zOf l 1) + beAt be (zOf l 0) (zOf l 2))

def IsBe (be : MvPowerSeries (Fin 2) ℂ_[l]) : Prop := BeCoef be ∧ BeInv be ∧ BeVan be ∧ BeBiadd be

def expFactor (S : Type) [Fintype S] (N N' : ℕ) (be : MvPowerSeries (Fin 2) ℂ_[l]) (ep : ℂ_[l]) :
    MvPowerSeries (S × Fin N × Fin N') ℂ_[l] :=
  ∏ s : S, expMv (-(MvPowerSeries.C (2⁻¹ : ℂ_[l]) * ∑ a : Fin N, ∑ b : Fin N',
    beAt be (zOf l (s, a, b)) (MvPowerSeries.C ep * zOf l (s, a, b))))

def HasShape {S : Type} [Fintype S] {N N' : ℕ} (be : MvPowerSeries (Fin 2) ℂ_[l]) (ep : ℂ_[l])
    (Θ : MvPowerSeries (S × Fin N × Fin N') ℂ_[l]) : Prop :=
  ∃ κ : S → ℂ_[l], (∀ s, ‖κ s‖ = 1) ∧
    ∃ U : MvPowerSeries (S × Fin N × Fin N') ℂ_[l], IntegralMv U ∧
      MvPowerSeries.subst (fun x : S × Fin N × Fin N' => MvPowerSeries.C (κ x.1) * zOf l x) Θ =
        U * expFactor S N N' be ep

end Beta

def embAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (x : Fin N → D.host.E) : Fin N → ℂ_[l] × ℂ_[l] :=
  fun k => (lamC lam (embT D τ (x k)), lamC lam (embT D τ (D.host.conj (x k))))

def latAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Set (Fin N → ℂ_[l] × ℂ_[l]) :=
  closure (embAt D lam τ '' (L : Set (Fin N → D.host.E)))

def IsOrthoAt (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (b : Fin N → Fin N → ℂ_[l] × ℂ_[l]) : Prop :=
  BasisP D lam (latAt D lam τ L) b ∧ ∀ a a', hP (b a) (b a') = if a = a' then 1 else 0

def colMat {l : ℕ} [Fact l.Prime] {N : ℕ} (b : Fin N → Fin N → ℂ_[l] × ℂ_[l]) : Matrix (Fin N) (Fin N) ℂ_[l] :=
  Matrix.of fun k a => (b a k).1

open Classical in

def chgO (D : D7) {l : ℕ} [Fact l.Prime] {N N' : ℕ} (c0 : D.what₂.Tau → ℂ_[l])
    (b : D.what₂.Tau → Fin N → Fin N → ℂ_[l] × ℂ_[l]) (b' : D.what₂.Tau → Fin N' → Fin N' → ℂ_[l] × ℂ_[l])
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × Formalism.MainNotions.G.HH D) × Fin N × Fin N') : ℂ_[l] :=
  if tauPl D x.1 = k.1 then c0 k.1 * colMat (b' k.1) k.2.1 x.2.2 * (colMat (b k.1))⁻¹ x.2.1 k.2.2 else 0

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

def CurveTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : IdE D → ℂ) : Prop :=
  IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ IsChi D χ

def LevelTie (Dx : DivX D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) : Prop :=
  ∀ p ∈ O.S, p = (D.mem u).A.T ∨ p = D.host.g 0 ∨ p = D.host.g 1 ∨ p ∈ Dx.Qp μ

def KerTie {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (i : ℕ) : Prop :=
  liftTie D (tor0 D cc δ) (B.eNat χ) O i

def SeriesTie (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ))
    (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    ∃ (b : D.what₂.Tau → Fin (D.R.N i) → Fin (D.R.N i) →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (b' : D.what₂.Tau → Fin (D.R.N (i + 1)) → Fin (D.R.N (i + 1)) →
        ℂ_[D.what₂.places.resChar w] × ℂ_[D.what₂.places.resChar w])
      (c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w]),
      (∀ τ, IsOrthoAt D (E.lam w) τ (O.lat i c).1 (b τ)) ∧
      (∀ τ, IsOrthoAt D (E.lam w) τ (O.lat (i + 1) c').1 (b' τ)) ∧
      (∀ τ, ‖c0 τ‖ = 1) ∧
      E.Th u μ w i c c' = linAt (chgO D c0 b b') (pSer D (E.lam w) (O.Th i c c'))

def ConjPrime (D : D7) (cc : Ideal (𝓞 D.host.K)) (l : ℕ) : Prop :=
  5 ≤ l ∧ InertK D l ∧ IsFrobC D l ∧ Nat.Coprime (Ideal.absNorm cc) l

def ShapeAll (E : KerEnt D Dx Tw) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    (w : D.what₂.places.Pl) (be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w])
    (ep : ℂ_[D.what₂.places.resChar w]) : Prop :=
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup) (O : LiftObj D (D.chTw u μ)), LevelTie Dx O → LevFree Dx u μ w →
    ∀ i < D.R.m, KerTie B χ O i → SeriesTie E O w i →
      ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape be ep (E.Th u μ w i c c')

def ThetaConj_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) : Prop :=
  CurveTie D cc δ χ → ∀ w : D.what₂.places.Pl, ConjPrime D cc (D.what₂.places.resChar w) →
    ∃ (be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w]) (ep : ℂ_[D.what₂.places.resChar w]),
      IsBe be ∧ ep ∈ Wp (D.what₂.places.resChar w) ∧ ‖ep‖ = 1 ∧ ShapeAll E B χ w be ep

def ThetaConjOne_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) : Prop :=
  CurveTie D cc δ χ → ∀ w : D.what₂.places.Pl, ConjPrime D cc (D.what₂.places.resChar w) →
    ∃ be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w], IsBe be ∧ ShapeAll E B χ w be 1

def Tied (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  CurveTie D cc δ χ ∧ (∀ u μ, LevelTie Dx (O u μ)) ∧ (∀ u μ, ∀ i < D.R.m, KerTie B χ (O u μ) i) ∧
    ∀ u μ w, ConjPrime D cc (D.what₂.places.resChar w) → LevFree Dx u μ w → ∀ i < D.R.m, SeriesTie E (O u μ) w i

def ThetaConjTied_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ)
    (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  Tied Dx Tw E cc δ B χ O → ∀ w : D.what₂.places.Pl, ConjPrime D cc (D.what₂.places.resChar w) →
    ∃ (be : MvPowerSeries (Fin 2) ℂ_[D.what₂.places.resChar w]) (ep : ℂ_[D.what₂.places.resChar w]),
      IsBe be ∧ ep ∈ Wp (D.what₂.places.resChar w) ∧ ‖ep‖ = 1 ∧
      ∀ u μ, LevFree Dx u μ w → ∀ i < D.R.m,
        ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)), HasShape be ep (E.Th u μ w i c c')

end GlobalTheory.IndefiniteRowSideFullHecke.VandermondeConjugatePrimes
