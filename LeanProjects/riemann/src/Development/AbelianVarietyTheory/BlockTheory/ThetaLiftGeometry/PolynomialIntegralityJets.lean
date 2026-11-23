import Mathlib
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

open Formalism.BasicNotions Formalism.MainNotions

def jetAt {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) : ℂ_[p] :=
  (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F

def JetsIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α, ‖jetAt F α‖ ≤ 1

def PolyIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (Q : MvPolynomial σ ℂ_[p]) : Prop :=
  ∀ β, ‖MvPolynomial.coeff β Q‖ ≤ 1

def FamTie (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) : Prop :=
  TaylorLogMetric.IsCurveIdeal D cc ∧ TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ TaylorLogMetric.IsChi D χ

def LevelTie {D : D7} (Dx : DivX D) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  O.S = insert (D.mem u).A.T (({D.host.g 0, D.host.g 1} : Finset ℕ) ∪ Dx.Qp μ)

def KerTie {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    {u : D.what₂.Word} {μ : D.what₂.Tup} (O : GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  ∀ i, i < D.R.m → GL3Theta.liftTie D (TaylorLogMetric.tor0 D cc δ) (B.eNat χ) O i

def coordChange (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ} (g : D.what₂.Tau → ℂ_[p])
    (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E)
    (k : D.what₂.Tau × Fin N' × Fin N) (x : (Bool × G.HH D) × Fin N × Fin N') : ℂ_[p] :=
  open Classical in
  if tauPl D x.1 = k.1 then
    g k.1 * ((P' k.1).map (TaylorLogMetric.tauEmb D lam k.1)) k.2.1 x.2.2 * (((P k.1).map (TaylorLogMetric.tauEmb D lam k.1))⁻¹) x.2.1 k.2.2
  else 0

def SerTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) : Prop :=
  ∃ P : ∀ j : ℕ, (D.chTw u μ).cls j → D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E,
    (∀ j, j ≤ D.R.m → ∀ c τ, TaylorLogMetric.LocBasisW D (TaylorLogMetric.tauEmb D (E.lam w) τ) (O.lat j c).1 (P j c τ)) ∧
    ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
      ∃ c0 : D.what₂.Tau → ℂ_[D.what₂.places.resChar w], (∀ τ, ‖c0 τ‖ = 1) ∧
        E.Th u μ w i c c' =
          linAt (coordChange D (E.lam w) (fun τ => c0 τ * TaylorLogMetric.lamC (E.lam w) (O.dgen τ)) (P i c) (P (i + 1) c'))
            (TaylorLogMetric.pSer D (E.lam w) (O.Th i c c'))

def EntInt {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)),
    JetsIntegral (E.Th u μ w i c c') ∧
    (∀ P : MvPolynomial (KM.XZ (Bool × G.HH D) (D.R.N i) (D.R.N (i + 1))) ℤ,
      PolyIntegral (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c') P)) ∧
    ∀ I : KM.ColChoice (D.R.N (i + 1)) (nuD D u i),
      PolyIntegral (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c')
        (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))

def JetInt_at (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw)
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  FamTie D cc δ χ →
  ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), LevelTie Dx (O u μ) → KerTie B χ (O u μ) →
    ∀ w : D.what₂.places.Pl, LevFree Dx u μ w → D.what₂.places.resChar w ≠ D.host.d → SerTie E (O u μ) w →
      EntInt E u μ w

def CoefAlg_at (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  FamTie D cc δ χ → ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), KerTie B χ (O u μ) →
    ∀ i, i < D.R.m → ∀ c c' α, TaylorLogMetric.taylor D ((O u μ).Th i c c') α ∈ TaylorLogMetric.Qbar

theorem not_mem_S {D : D7} {Dx : DivX D} {u : D.what₂.Word} {μ : D.what₂.Tup} {O : GL3Theta.LiftObj D (D.chTw u μ)}
    (h : LevelTie Dx O) (w : D.what₂.places.Pl) : LevFree Dx u μ w ↔ D.what₂.places.resChar w ∉ O.S := by
  rw [h, LevFree]
  simp only [Finset.mem_insert, Finset.mem_union]
  tauto

theorem polyIntegral_applyAt0 {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime]
    (F : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (h : JetsIntegral F) (P : MvPolynomial (KM.XZ Lt N0 N1) ℤ) :
    PolyIntegral (KM.applyAt0 N0 N1 l F P) := by
  classical
  intro β
  unfold KM.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun μ _ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · rw [mul_assoc, norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ _) (norm_nonneg _) (h _)
  · simp

example (p : ℕ) [hp : Fact p.Prime] :
    ¬ JetsIntegral (MvPowerSeries.monomial (Finsupp.single () 1) ((p : ℂ_[p])⁻¹) : MvPowerSeries Unit ℂ_[p]) := by
  intro h
  have h1 := h (Finsupp.single () 1)
  have h2 : ‖(p : ℂ_[p])‖ < 1 := by
    have : ((p : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h3 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [jetAt, MvPowerSeries.coeff_monomial_same] at h1
  rw [Finsupp.prod_single_index (by simp)] at h1
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, norm_inv] at h1
  have h4 := norm_pos_iff.2 h3
  rw [inv_le_one₀ h4] at h1
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets
