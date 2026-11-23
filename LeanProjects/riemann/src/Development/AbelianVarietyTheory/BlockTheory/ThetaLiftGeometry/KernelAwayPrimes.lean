import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalToGlobal.Divisibility.CoefMod

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def IntAt {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) : Prop :=
  a ∈ Qbar ∧ ‖lamC lam a‖ ≤ 1

def WeylAt (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N : ℕ} (wt : D.what₂.Tau → DomWeight N)
    (Q : MvPolynomial (FrV D N) ℂ) : Prop :=
  ∃ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → D.what₂.Tau → MvPolynomial (Fin N × Fin N) ℤ),
    (∀ k, IntAt lam (a k)) ∧ (∀ k τ, f k τ ∈ delSq ℤ N (wt τ)) ∧
    Q = ∑ k, a k • Formalism.L2.DIV.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f k τ))

variable {D : D7}

def lastTrue (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (τ : D.what₂.Tau) : ℤ :=
  ((Tw.fm u μ).lam i τ).detShift - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

def ValInt (Tw : TwForms D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) {p : ℕ} [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) (i : ℕ) (v : (D.chTw u μ).Y i → ℂ) : Prop :=
  ∃ Q : MvPolynomial (FrV D (D.R.N i)) ℂ, WeylAt D lam ((Tw.fm u μ).lam i) Q ∧
    ∀ y, v y = evFr D Q (O.frm i y) * ∏ τ, (O.frm i y τ).det ^ lastTrue Tw u μ i τ

def nn (X : ErrX D) (ig : Fin 2) (u : D.what₂.Word) (j : ℕ) : D.what₂.LL :=
  ∏ τ : D.what₂.Tau, tauPib X ig τ ^ ⌊nuAbs D u j τ⌋₊

def loss (X : ErrX D) (ig : Fin 2) (u : D.what₂.Word) (i : ℕ) : D.what₂.LL :=
  nn X ig u (i + 1) * (D.host.g ig : D.what₂.LL) ^ (D.R.f * D.R.N i * D.R.N (i + 1))

def FamTie (D : D7) (ig : Fin 2) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  IsCurveIdeal D cc ∧ Nat.Coprime (Ideal.absNorm cc) (D.host.g ig) ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧
    vec22 D (tor0 D cc δ) e ∧ int22 D (tor0 D cc δ) e

def RepStd {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (g i : ℕ) : Prop :=
  letI := D.host.cmStar
  ∀ c : C.cls i, EqAt D g (O.lat i c).1 (O.L0 i).1

def StabTie {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (i : ℕ) : Prop :=
  letI := D.host.cmStar
  ∀ c : C.cls i, ∃ j : C.stab i c →* Matrix.unitaryGroup (Fin (D.R.N i)) D.host.E, Function.Injective j ∧
    ∀ γ, SDLat.smulLat ((j γ : Matrix.unitaryGroup (Fin (D.R.N i)) D.host.E) :
      Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) (O.lat i c).1 = (O.lat i c).1

def awayPr (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (ig : Fin 2) : Finset ℕ :=
  insert (D.host.g (1 - ig)) (insert (D.mem u).A.T (Dx.Qp μ))

def IdemPi (X : ErrX D) (ig : Fin 2) (ε : 𝓞 D.host.K) : Prop :=
  (∃ a : 𝓞 D.host.E, ((ε : D.host.K) : D.host.E) - 1 = ((X.piG ig : 𝓞 D.host.E) : D.host.E) ^ 4 * (a : D.host.E)) ∧
  ∃ a : 𝓞 D.host.E, ((ε : D.host.K) : D.host.E) =
    D.host.conj ((X.piG ig : 𝓞 D.host.E) : D.host.E) ^ 4 * (a : D.host.E)

def IsKerG (X : ErrX D) (ig : Fin 2) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (S : Finset ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Θ : VC D N N' → ℂ) : Prop :=
  ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (ε : 𝓞 D.host.K) (n : ℕ) (a : Fin n → ℂ)
    (t : Fin n → VC D N N') (Ψ : Fin n → LocallyConstant (Fin r → ℤ_[D.host.g ig]) ℂ),
    NNBasis D (tor0 D cc δ) δ (D.host.g ig) L L' b ∧ IdemPi X ig ε ∧
    (∀ k, a k ∈ Qbar) ∧
    (∀ k (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → ‖lamC lam (a k)‖ ≤ 1) ∧
    (∀ k, ∃ m : ℕ, 0 < m ∧ (∀ q : ℕ, q.Prime → q ∣ m → q ∈ S) ∧ m • t k ∈ La D (tor0 D cc δ) L L') ∧
    (∀ k, FactorsMod 1 (Ψ k) ∧ ∀ x, IsIntegral ℤ (Ψ k x)) ∧
    Θ = fun z => ∑ k, a k * U D (tor0 D cc δ) (t k)
      (XiF D (tor0 D cc δ) δ (D.host.g ig) 1 ε b (Ψ k) (e N N' L L')) z

def KerGTie (Dx : DivX D) (X : ErrX D) (ig : Fin 2) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (i : ℕ) : Prop :=
  letI := D.host.cmStar
  ∀ c c', IsKerG X ig cc δ e (awayPr Dx u μ ig) (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')

def LatTie {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ x : ((Tw.fm u μ).lat i).V, x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L ↔
    ∀ c, ValInt Tw O (E.lam w) i ((Tw.fm u μ).emb i x c)

def SizeG (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (ig : Fin 2) (i : ℕ) : Prop :=
  LiftErrorLocal.Dpi D u (i + 1) < (D.host.g ig : ℝ) - 1 ∧
  2 * D.R.f * D.R.N i + 1 < D.host.g ig ∧
  (∀ τ, ((Tw.fm u μ).lam i τ).spread < (D.host.g ig : ℤ)) ∧
  ∀ τ, ((Tw.fm u μ).lam (i + 1) τ).spread < (D.host.g ig : ℤ)

def ValLoss {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (X : ErrX D) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : LiftObj D (D.chTw u μ)) (ig : Fin 2) (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ φ : (D.chTw u μ).cls i → (D.chTw u μ).Y i → ℂ, (∀ c, ValInt Tw O (E.lam w) i (φ c)) →
    ∀ c', ValInt Tw O (E.lam w) (i + 1) (D.what₂.embLL (loss X ig u i) • (D.chTw u μ).K i φ c')

def FormLoss (Tw : TwForms D) (X : ErrX D) (u : D.what₂.Word) (μ : D.what₂.Tup) (ig : Fin 2)
    (w : D.what₂.places.Pl) (i : ℕ) : Prop :=
  ∀ x ∈ locW D.what₂.places w ((Tw.fm u μ).lat i).L, ∀ y : ((Tw.fm u μ).lat (i + 1)).V,
    (Tw.fm u μ).emb (i + 1) y = (D.chTw u μ).K i ((Tw.fm u μ).emb i x) →
    loss X ig u i • y ∈ locW D.what₂.places w ((Tw.fm u μ).lat (i + 1)).L

def KernelEntryIdealCondition (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (X : ErrX D)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  InducedCMType D → HostFieldConditions D → Pinned D →
  ∀ (ig : Fin 2), FamTie D ig cc δ e →
  ∀ (w : D.what₂.places.Pl), LiftErrorLocal.Over D ig w →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), D.host.g ig ≠ (D.mem u).A.T → D.host.g ig ∉ Dx.Qp μ →
  ∀ (O : LiftObj D (D.chTw u μ)), rhoThreeOf D (D.chTw u μ) O.mt →
  ∀ i, i < D.R.m → SizeG Tw u μ ig i →
    liftTie D (tor0 D cc δ) e O i → KerGTie Dx X ig cc δ e O i →
    RepStd O (D.host.g ig) i → RepStd O (D.host.g ig) (i + 1) → StabTie O i →
    ValLoss E X O ig w i ∧ (LatTie E O w i → LatTie E O w (i + 1) → FormLoss Tw X u μ ig w i)

theorem valInt_zero (Tw : TwForms D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) {p : ℕ}
    [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (i : ℕ) : ValInt Tw O lam i 0 :=
  ⟨0, ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, fun k => k.elim0, by simp⟩, fun y => by simp [evFr]⟩

theorem formLoss_of_valLoss {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (X : ErrX D) {u : D.what₂.Word}
    {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) (ig : Fin 2) (w : D.what₂.places.Pl) (i : ℕ)
    (h : ValLoss E X O ig w i) (h0 : LatTie E O w i) (h1 : LatTie E O w (i + 1)) : FormLoss Tw X u μ ig w i := by
  intro x hx y hy
  refine (h1 _).2 fun c' => ?_
  have := h _ ((h0 x).1 hx) c'
  rw [LinearMap.map_smulₛₗ, hy]
  exact this

theorem exp_le (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.f * D.R.N i * D.R.N (i + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m + D.R.t := by
    unfold Ranks.N
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _) (Nat.le_add_right _ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

end
