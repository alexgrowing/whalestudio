import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataKerI
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.SharpRestriction.GrowthBounds.KerTiesI

noncomputable section

namespace Formalism.MainNotions.GL3Columns

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.StandardLatticesGL3

abbrev dtG (D : D7) {N : ℕ} (g : GA D N) : (AE D)ˣ := Matrix.GeneralLinearGroup.det (g : GL (Fin N) (AE D))

def InUnitaryOneIdeles (D : D7) (t : (AE D)ˣ) : Prop := t * sgU D t = 1

def incU (D : D7) (a : D.host.Eˣ) : (AE D)ˣ := Units.map (inc D).toMonoidHom a

def CongOne (D : D7) (m : ℕ) (u : (AE D)ˣ) : Prop := ∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s

structure DtAd (D : D7) where
  q : (AE D)ˣ → D.Dt
  q_mul : ∀ s t, InUnitaryOneIdeles D s → InUnitaryOneIdeles D t → q (s * t) = q s * q t
  q_surj : ∀ x : D.Dt, ∃ t, InUnitaryOneIdeles D t ∧ q t = x
  q_UO : ∀ t, InUnitaryOneIdeles D t → (q t ∈ D.UO ↔ IntU D t)
  q_open : ∃ m : ℕ, 0 < m ∧ ∀ t, InUnitaryOneIdeles D t → IntU D t → CongOne D m t → q t = 1
  q_rat : letI := D.host.cmStar
    ∀ (z : unitary D.host.E) (a : D.host.Eˣ), (a : D.host.E) = (z : D.host.E) → q (incU D a) = D.e1Dt z
  q_det : letI := D.host.cmStar
    ∀ (N : ℕ) (g : GA D N) (L₀ L : SDLat D.host.E N), L₀.1 = stdL D N → Moves D (g : GL (Fin N) (AE D)) L.1 →
      (QuotientGroup.mk (q (dtG D g)) : D.Dt ⧸ D.UO) = D.relDet N L₀ L

def rhoA (D : D7) (m1 : D.Dt →* ℂˣ) (N' : ℕ) : D.Dt →* ℂˣ := m1⁻¹ * D.chiD ^ (-((N' / 2 : ℕ) : ℤ))

def rhoA' (D : D7) (m1 : D.Dt →* ℂˣ) (N : ℕ) : D.Dt →* ℂˣ := m1 * D.chiD ^ (((N / 2 : ℕ) : ℤ))

theorem rhoOf_eq (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : rhoOf D mt i = rhoA D (mt (i + 1)) (D.R.N (i + 1)) := rfl

theorem rhoOf'_eq (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : rhoOf' D mt i = rhoA' D (mt (i + 1)) (D.R.N i) := rfl

def dOrt (D : D7) (T : Tor D) : ℂ := ((Real.sqrt (area T.abelian₂ / Real.pi) : ℝ) : ℂ)

def sclP (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (P : MvPolynomial (Idx D N N') ℂ) : MvPolynomial (Idx D N N') ℂ :=
  MvPolynomial.aeval (fun k : Idx D N N' => MvPolynomial.C (s k.1) * MvPolynomial.X k) P

def applyO (D : D7) (T : Tor D) {N N' : ℕ} (P : MvPolynomial (Idx D N N') ℂ) (G : VC D N N' → ℂ) : ℂ :=
  applyAt0 D (sclP D (fun _ => dOrt D T) P) G

def xiC (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' n : ℕ} (r : Fin n → ℂ)
    (z : Fin n → Matrix (Fin N') (Fin N) D.host.E) (G : VC D N N' → ℂ) : VC D N N' → ℂ :=
  fun y => ∑ k, r k * Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z k)) G y

abbrev e00 (D : D7) (e : FamE D) (N N' : ℕ) : VC D N N' → ℂ := e N N' (stdL D N) (stdL D N')

structure ThetaD (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) where
  Th : MvPolynomial (Idx D N N') ℂ → (VC D N N' → ℂ) → ℂ
  gen : (VC D N N' → ℂ) → VC D N N' → ℂ
  gen_add : ∀ G ∈ TT D (tor0 D cc δ) N N', ∀ G' ∈ TT D (tor0 D cc δ) N N', gen (G + G') = gen G + gen G'
  gen_smul : ∀ (a : ℂ), ∀ G ∈ TT D (tor0 D cc δ) N N', gen (a • G) = a • gen G
  gen_diff : ∀ G ∈ TT D (tor0 D cc δ) N N', Differentiable ℂ (gen G)
  gen_jet : ∀ P, ∀ G ∈ TT D (tor0 D cc δ) N N', Th P G = applyO D (tor0 D cc δ) P (gen G)
  gen_heis : ∀ (x : Matrix (Fin N') (Fin N) D.host.E), ∀ G ∈ TT D (tor0 D cc δ) N N',
    gen (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ x) G) = U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ x) (gen G)
  ne : ∃ G ∈ TT D (tor0 D cc δ) N N', gen G ≠ 0

def ThetaD.IsResidueClassZero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} (Θ : ThetaD D cc δ N N') (c0 : ℂ) : Prop :=
  c0 ≠ 0 ∧ ∀ P, ∀ G ∈ TT D (tor0 D cc δ) N N', Θ.Th P G = c0 * applyO D (tor0 D cc δ) P G

def kjOne (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  ∀ (N N' : ℕ) (Θ : ThetaD D cc δ N N'), ∃ c0 : ℂ, Θ.IsResidueClassZero c0 ∧ ∀ G ∈ TT D (tor0 D cc δ) N N', Θ.gen G = c0 • G

def IsKJ (D : D7) (Q : DtAd D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} {e0 : VC D N N' → ℂ}
    (W : WeilO D cc δ N N' e0) (m1 : D.Dt →* ℂˣ) : Prop :=
  W.ep = 1 ∧ W.ep' = -1 ∧ W.chV.f = W.chV'.f ∧ W.chV.n = W.chV'.n ∧
    ∀ x : (AE D)ˣ, m1 (Q.q (x * (sgU D x)⁻¹)) = W.chV.f x

def kjVac (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even N → Even N' →
    ∀ (W : WeilO D cc δ N N' (e00 D e N N')) (m1 : D.Dt →* ℂˣ), IsKJ D Q W m1 →
    ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
      W.Om g g' (e00 D e N N') = fun y =>
        (((rhoA D m1 N' (Q.q (dtG D g)) * rhoA' D m1 N (Q.q (dtG D g')) : ℂˣ) : ℂ)) * e N N' L L' y

def KJ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even N → Even N' → ∀ Θ : ThetaD D cc δ N N', ∃ c0 : ℂ, c0 ≠ 0 ∧
    ∀ (W : WeilO D cc δ N N' (e00 D e N N')) (m1 : D.Dt →* ℂˣ), IsKJ D Q W m1 →
    ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
    ∀ (n : ℕ) (r : Fin n → ℂ) (z : Fin n → Matrix (Fin N') (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧
      ∀ z' : Fin n → Matrix (Fin N') (Fin N) D.host.E,
        (∀ k, CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z k) (z' k)) →
        ∀ P, Θ.Th P (W.Om g g' (xiC D cc δ r z (e00 D e N N'))) =
          c0 * (((rhoA D m1 N' (Q.q (dtG D g)) * rhoA' D m1 N (Q.q (dtG D g')) : ℂˣ) : ℂ)) *
            applyO D (tor0 D cc δ) P (xiC D cc δ r z' (e N N' L L'))

def kjDat (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even N → Even N' →
    ∀ (W : WeilO D cc δ N N' (e00 D e N N')) (m1 : D.Dt →* ℂˣ), IsKJ D Q W m1 →
    ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
    ∀ (n : ℕ) (r : Fin n → ℂ) (z : Fin n → Matrix (Fin N') (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧
      ∀ z' : Fin n → Matrix (Fin N') (Fin N) D.host.E,
        (∀ k, CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z k) (z' k)) →
        W.Om g g' (xiC D cc δ r z (e00 D e N N')) = fun y =>
          (((rhoA D m1 N' (Q.q (dtG D g)) * rhoA' D m1 N (Q.q (dtG D g')) : ℂˣ) : ℂ)) *
            xiC D cc δ r z' (e N N' L L') y

def HomDeg (D : D7) {N : ℕ} (Qp : MvPolynomial (FrV D N) ℂ) (dg : D.what₂.Tau → ℕ) : Prop :=
  ∀ α ∈ Qp.support, ∀ τ, (α.sum fun k n => if k.1 = τ then n else 0) = dg τ

structure AdLift (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (i : ℕ) where
  W : WeilO D cc δ (D.R.N i) (D.R.N (i + 1)) (e00 D e (D.R.N i) (D.R.N (i + 1)))
  isKJ : IsKJ D Q W (O.mt (i + 1))
  Θ : ThetaD D cc δ (D.R.N i) (D.R.N (i + 1))
  g : C.cls i → GA D (D.R.N i)
  g' : C.cls (i + 1) → GA D (D.R.N (i + 1))
  g_lat : ∀ c, Moves D (g c : GL (Fin (D.R.N i)) (AE D)) (O.lat i c).1
  g'_lat : ∀ c', Moves D (g' c' : GL (Fin (D.R.N (i + 1))) (AE D)) (O.lat (i + 1) c').1
  g_dt : ∀ c, Q.q (dtG D (g c)) = O.dt i c
  g'_dt : ∀ c', Q.q (dtG D (g' c')) = O.dt (i + 1) c'
  n : C.cls i → C.cls (i + 1) → ℕ
  r : ∀ c c', Fin (n c c') → ℂ
  z : ∀ c c', Fin (n c c') → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N i)) D.host.E
  r_alg : ∀ c c' k, r c c' k ∈ Qbar
  r_int : ∀ c c' k (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ O.S → ‖lamC lam (r c c' k)‖ ≤ 1
  z_S : ∀ c c' k, ∃ a : ℕ, 0 < a ∧ (∀ q : ℕ, q.Prime → q ∣ a → q ∈ O.S) ∧
    a • pt D (tor0 D cc δ) δ (z c c' k) ∈ La0 D (tor0 D cc δ) (D.R.N i) (D.R.N (i + 1))
  dg : D.what₂.Tau → ℕ

def termO (D : D7) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (i : ℕ)
    (c : C.cls i) (c' : C.cls (i + 1)) (G : VC D (D.R.N i) (D.R.N (i + 1)) → ℂ)
    (Qp : MvPolynomial (FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)) : ℂ :=
  (((rhoOf D O.mt i (O.dt i c) : ℂˣ) : ℂ) * ((rhoOf' D O.mt i (O.dt (i + 1) c') : ℂˣ) : ℂ)) *
    ((∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ * applyAt0 D (polD D O.dgen Qp (O.frm (i + 1) y')) G)

namespace AdLift

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {u : D.what₂.Word}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (A : AdLift D cc δ e Q O i)

def Mv (c : C.cls i) (c' : C.cls (i + 1)) (G : VC D (D.R.N i) (D.R.N (i + 1)) → ℂ) : Prop :=
  ∃ m : ℕ, 0 < m ∧
    (∃ z' : Fin (A.n c c') → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N i)) D.host.E, ∀ k, CloseTo D cc m (A.g c : GL (Fin (D.R.N i)) (AE D)) (A.g' c' : GL (Fin (D.R.N (i + 1))) (AE D)) (A.z c c' k) (z' k)) ∧
    ∀ z' : Fin (A.n c c') → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N i)) D.host.E, (∀ k, CloseTo D cc m (A.g c : GL (Fin (D.R.N i)) (AE D)) (A.g' c' : GL (Fin (D.R.N (i + 1))) (AE D)) (A.z c c' k) (z' k)) →
      G = xiC D cc δ (A.r c c') z' (e (D.R.N i) (D.R.N (i + 1)) (O.lat i c).1 (O.lat (i + 1) c').1)

def entry (c : C.cls i) (c' : C.cls (i + 1)) (Qp : MvPolynomial (FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)) : ℂ :=
  (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ *
    A.Θ.Th (polD D (fun _ => 1) Qp (O.frm (i + 1) y'))
      (A.W.Om (A.g c) (A.g' c') (xiC D cc δ (A.r c c') (A.z c c') (e00 D e (D.R.N i) (D.R.N (i + 1)))))

def IsDef (c0 : ℂ) : Prop :=
  ∀ c c' (Qp : MvPolynomial (FrV D (D.R.N i)) ℂ), HomDeg D Qp A.dg → ∀ (f : C.Y i → ℂ) (y' : C.Y (i + 1)),
    C.sharp i f = (fun y => evFr D Qp (O.frm i y)) →
    (c0 * ∏ τ, dOrt D (tor0 D cc δ) ^ A.dg τ) * C.Kmap i c c' f y' = (∏ τ, O.dgen τ ^ A.dg τ) * A.entry c c' Qp y'

def kjEntry : Prop :=
  ∀ c0, A.Θ.IsResidueClassZero c0 → ∀ c c' G, A.Mv c c' G → ∀ Qp, HomDeg D Qp A.dg → ∀ y',
    (∏ τ, O.dgen τ ^ A.dg τ) * A.entry c c' Qp y' = (c0 * ∏ τ, dOrt D (tor0 D cc δ) ^ A.dg τ) * termO D O i c c' G Qp y'

def kjPair : Prop :=
  ∀ c0, A.Θ.IsResidueClassZero c0 → A.IsDef c0 → ∀ c c' G, A.Mv c c' G → ∀ Qp, HomDeg D Qp A.dg → ∀ (f : C.Y i → ℂ) (y' : C.Y (i + 1)),
    C.sharp i f = (fun y => evFr D Qp (O.frm i y)) → C.Kmap i c c' f y' = termO D O i c c' G Qp y'

def ThIs : Prop := ∀ c c', A.Mv c c' (O.Th i c c')

def kjKer : Prop :=
  A.ThIs → ∀ c c', IsKer D (tor0 D cc δ) e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')

def kjSum : Prop :=
  ∀ c0, A.Θ.IsResidueClassZero c0 → A.IsDef c0 → A.ThIs → ∀ (φ : C.cls i → C.Y i → ℂ) (Qc : C.cls i → MvPolynomial (FrV D (D.R.N i)) ℂ),
    (∀ c, HomDeg D (Qc c) A.dg ∧ C.sharp i (φ c) = fun y => evFr D (Qc c) (O.frm i y)) →
    ∀ c' y', C.K i φ c' y' = ∑ c, (((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹) * termO D O i c c' (O.Th i c c') (Qc c) y'

theorem kjSum_of (h : A.kjPair) : A.kjSum := by
  intro c0 hc0 hd ht φ Qc hQ c' y'
  simp only [ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ColumnChain.wt]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [h c0 hc0 hd c c' (O.Th i c c') (ht c c') (Qc c) (hQ c).1 (φ c) y' (hQ c).2]

theorem kjPair_of (h : A.kjEntry) (hd : dOrt D (tor0 D cc δ) ≠ 0) : A.kjPair := by
  intro c0 hc0 hdef c c' G hG Qp hQ f y' hf
  have h1 := hdef c c' Qp hQ f y' hf
  rw [h c0 hc0 c c' G hG Qp hQ y'] at h1
  have hne : c0 * ∏ τ, dOrt D (tor0 D cc δ) ^ A.dg τ ≠ 0 :=
    mul_ne_zero hc0.1 (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ hd)
  exact mul_left_cancel₀ hne h1

end AdLift

def kjForm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (Tw : TwForms D) {u : D.what₂.Word}
    {μ : D.what₂.Tup} {O : LiftObj D (D.chTw u μ)} {i : ℕ} (A : AdLift D cc δ e Q O i) : Prop :=
  ∀ c0, A.Θ.IsResidueClassZero c0 → A.IsDef c0 → A.ThIs →
    ∀ (x : ((Tw.fm u μ).lat i).V) (y : ((Tw.fm u μ).lat (i + 1)).V),
      (Tw.fm u μ).emb (i + 1) y = (D.chTw u μ).K i ((Tw.fm u μ).emb i x) →
      ∀ Qc : (D.chTw u μ).cls i → MvPolynomial (FrV D (D.R.N i)) ℂ,
        (∀ c, HomDeg D (Qc c) A.dg ∧ (D.chTw u μ).sharp i ((Tw.fm u μ).emb i x c) = fun t => evFr D (Qc c) (O.frm i t)) →
        ∀ c' y', (Tw.fm u μ).emb (i + 1) y c' y' =
          ∑ c, (((Nat.card ((D.chTw u μ).stab i c) : ℕ) : ℂ)⁻¹) * termO D O i c c' (O.Th i c c') (Qc c) y'

theorem kjForm_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (Tw : TwForms D) {u : D.what₂.Word}
    {μ : D.what₂.Tup} {O : LiftObj D (D.chTw u μ)} {i : ℕ} (A : AdLift D cc δ e Q O i) (h : A.kjSum) : kjForm Tw A := by
  intro c0 hc0 hd ht x y hxy Qc hQ c' y'
  rw [hxy]
  exact h c0 hc0 hd ht _ Qc hQ c' y'

open Formalism.MainNotions.G in

def kjAtP {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    {u : D.what₂.Word} {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv}
    (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) {O : LiftObj D (D.chTw u (D.what₂.muAt w))} (A : ∀ j, AdLift D cc δ e Q O j) : Prop :=
  ∀ j < D.R.m, ∀ c0, (A j).Θ.IsResidueClassZero c0 → (A j).IsDef c0 → (A j).ThIs →
    ∀ (x : ((Tw.fm u (D.what₂.muAt w)).lat j).V) (y : ((Tw.fm u (D.what₂.muAt w)).lat (j + 1)).V),
      (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y = (D.chTw u (D.what₂.muAt w)).K j ((Tw.fm u (D.what₂.muAt w)).emb j x) →
      Ch.Kz j (Kp.cmp j x) = Kp.cmp (j + 1) y ∧
      ∀ Qc : (D.chTw u (D.what₂.muAt w)).cls j → MvPolynomial (FrV D (D.R.N j)) ℂ,
        (∀ k, HomDeg D (Qc k) (A j).dg ∧
          (D.chTw u (D.what₂.muAt w)).sharp j ((Tw.fm u (D.what₂.muAt w)).emb j x k) = fun t => evFr D (Qc k) (O.frm j t)) →
        ∀ (a' : Lv.comp (j + 1)) (L' : (Fl.Pj (j + 1)).Tup) y',
          (Tw.fm u (D.what₂.muAt w)).emb (j + 1) y (Kp.cls (j + 1) a' L') y' =
            ∑ k, (((Nat.card ((D.chTw u (D.what₂.muAt w)).stab j k) : ℕ) : ℂ)⁻¹) *
              termO D O j k (Kp.cls (j + 1) a' L') (O.Th j k (Kp.cls (j + 1) a' L')) (Qc k) y'

open Formalism.MainNotions.G in
theorem kernelAtPrime_pairCondition_of_lifts {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    {u : D.what₂.Word} {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} {Ch : Chain Lv}
    (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) {O : LiftObj D (D.chTw u (D.what₂.muAt w))} (A : ∀ j, AdLift D cc δ e Q O j)
    (hA : ∀ j < D.R.m, (A j).kjPair) : kjAtP Kp A := by
  intro j hj c0 hc0 hd ht x y hxy
  refine ⟨(Kp.cmp_K j hj x y hxy).symm, fun Qc hQ a' L' y' => ?_⟩
  exact kjForm_of Tw (A j) ((A j).kjSum_of (hA j hj)) c0 hc0 hd ht x y hxy Qc hQ _ y'

def liftTieH (D : D7) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (i : ℕ)
    (dg : D.what₂.Tau → ℕ) : Prop :=
  ∀ c c' (Qp : MvPolynomial (FrV D (D.R.N i)) ℂ), HomDeg D Qp dg → ∀ y' : C.Y (i + 1),
    C.unf i c c' (fun y => evFr D Qp (O.frm i y)) y' = applyAt0 D (polD D O.dgen Qp (O.frm (i + 1) y')) (O.Th i c c')

theorem liftTieH_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (hi : i < D.R.m) (A : AdLift D cc δ e Q O i)
    (h : A.kjPair) (c0 : ℂ) (h0 : A.Θ.IsResidueClassZero c0) (hd : A.IsDef c0) (ht : A.ThIs) : liftTieH D O i A.dg := by
  intro c c' Qp hQ y'
  have hsh : ∀ y, (∏ τ, (C.de i y τ) ^ (C.sSharp i τ)) ≠ 0 := fun y =>
    Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (C.de_ne i y τ)
  have hf : C.sharp i (fun y => (∏ τ, (C.de i y τ) ^ (C.sSharp i τ))⁻¹ * evFr D Qp (O.frm i y)) =
      fun y => evFr D Qp (O.frm i y) := by
    funext y
    simp only [ColumnChain.sharp, Formalism.BasicNotions.mulFun, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← mul_assoc, mul_inv_cancel₀ (hsh y), one_mul]
  have h1 := h c0 h0 hd c c' (O.Th i c c') (ht c c') Qp hQ _ y' hf
  simp only [ColumnChain.Kmap, LinearMap.smul_apply, LinearMap.comp_apply, hf, ColumnChain.divDe,
    Formalism.BasicNotions.mulFun, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, termO] at h1
  rw [(O.c13 i hi).1 c, (O.c13 i hi).2 c'] at h1
  have hρ : (((rhoOf D O.mt i (O.dt i c) : ℂˣ) : ℂ) * ((rhoOf' D O.mt i (O.dt (i + 1) c') : ℂˣ) : ℂ)) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have hde : (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ ≠ 0 :=
    inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (C.de_ne (i + 1) y' τ))
  exact mul_left_cancel₀ hde (mul_left_cancel₀ hρ h1)

abbrev matT (D : D7) {N : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (τ : D.what₂.Tau) : Matrix (Fin N) (Fin N) ℂ := γ.map (embT D τ)

def kjInvKer (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  letI := D.host.cmStar
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even N → Even N' →
    ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (γA : GA D N) (γA' : GA D N'),
      IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) →
      IsRat D (γA' : GL (Fin N') (AE D)) (γ' : Matrix (Fin N') (Fin N') D.host.E) →
    ∀ (n : ℕ) (r : Fin n → ℂ) (z : Fin n → Matrix (Fin N') (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧
      ∀ z' z'' : Fin n → Matrix (Fin N') (Fin N) D.host.E,
        (∀ k, CloseTo D cc m (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D)) (z k) (z' k)) →
        (∀ k, CloseTo D cc m ((γA * g : GA D N) : GL (Fin N) (AE D)) ((γA' * g' : GA D N') : GL (Fin N') (AE D)) (z k) (z'' k)) →
        xiC D cc δ r z'' (e N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)
            (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) L')) =
          pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E)
            (xiC D cc δ r z' (e N N' L L'))

def termA (D : D7) (Q : DtAd D) (m1 : D.Dt →* ℂˣ) {N N' : ℕ} (sd : D.what₂.Tau → ℤ) (s : D.what₂.Tau → ℂ) (g : GA D N) (g' : GA D N')
    (Qp : MvPolynomial (FrV D N) ℂ) (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : VC D N N' → ℂ) : ℂ :=
  (((rhoA D m1 N' (Q.q (dtG D g)) * rhoA' D m1 N (Q.q (dtG D g')) : ℂˣ) : ℂ)) *
    ((∏ τ, (y' τ).det ^ (sd τ))⁻¹ * applyAt0 D (polD D s Qp y') G)

def kjInvTerm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (Q : DtAd D) : Prop :=
  letI := D.host.cmStar
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even N → Even N' → ∀ (m1 : D.Dt →* ℂˣ) (eT : D.what₂.Tau → ℤ),
    (∀ z : unitary D.host.E, ((m1 (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, embT D τ (z : D.host.E) ^ (eT τ)) →
    ∀ (g : GA D N) (g' : GA D N')
      (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (γA : GA D N) (γA' : GA D N'),
      IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) →
      IsRat D (γA' : GL (Fin N') (AE D)) (γ' : Matrix (Fin N') (Fin N') D.host.E) →
    ∀ (Qp Qp' : MvPolynomial (FrV D N) ℂ),
      (∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ, evFr D Qp' y =
        (∏ τ, embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det ^ (eT τ - ((N' / 2 : ℕ) : ℤ))) *
          evFr D Qp (fun τ => (matT D (γ : Matrix (Fin N) (Fin N) D.host.E) τ).conjTranspose * y τ)) →
    ∀ (s : D.what₂.Tau → ℂ) (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (G : VC D N N' → ℂ), Differentiable ℂ G →
      (∀ τ, (y' τ).det ≠ 0) →
      termA D Q m1 (fun τ => eT τ - ((N / 2 : ℕ) : ℤ)) s (γA * g) (γA' * g') Qp'
          (fun τ => matT D (γ' : Matrix (Fin N') (Fin N') D.host.E) τ * y' τ)
          (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) =
        termA D Q m1 (fun τ => eT τ - ((N / 2 : ℕ) : ℤ)) s g g' Qp y' G

def MuTil (D : D7) (Q : DtAd D) {N : ℕ} (μ : HeckeU D N) (m1 : D.Dt →* ℂˣ) : Prop :=
  ∀ x : (AE D)ˣ, m1 (Q.q (x * (sgU D x)⁻¹)) = μ.f x

def types (D : D7) (Q : DtAd D) : Prop :=
  letI := D.host.cmStar
  ∀ (N₀ N N' : ℕ) (μ : HeckeU D N₀) (m1 : D.Dt →* ℂˣ) (eT : D.what₂.Tau → ℤ), Even N₀ → Even N → Even N' → MuTil D Q μ m1 →
    (∀ τ, μ.n τ = -2 * eT τ) →
    (∀ z : unitary D.host.E, ((m1 (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, embT D τ (z : D.host.E) ^ (eT τ)) ∧
    (∀ z : unitary D.host.E,
      ((rhoA D m1 N' (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, embT D τ (z : D.host.E) ^ (-(eT τ - ((N' / 2 : ℕ) : ℤ))) ∧
      ((rhoA' D m1 N (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, embT D τ (z : D.host.E) ^ (eT τ - ((N / 2 : ℕ) : ℤ))) ∧
    (∀ (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
      Mod1E ((rhoA D m1 N' t : ℂˣ) : ℂ) ∧ Mod1E ((rhoA' D m1 N t : ℂˣ) : ℂ)) ∧
    (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoA D m1 N' k ^ n = 1 ∧ rhoA' D m1 N k ^ n = 1)

def typesCh (D : D7) (Q : DtAd D) : Prop :=
  ∀ (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), (∀ i ≤ D.R.m, Even (D.R.N i)) →
    (∀ (i : ℕ) (h : i < D.R.m), ∃ (N₀ : ℕ) (μ : HeckeU D N₀), Even N₀ ∧ MuTil D Q μ (mt (i + 1)) ∧
      ∀ τ, ((μ.n τ : ℤ) : ℚ) = -2 * (D.hcW u τ).e ⟨i, h⟩) →
    rhoThreeOf D C mt

def br (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  ∀ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → InertK D p →
    ∀ (t : D.Dt) (iv : ℤ) (Ev Od : Finset D.what₂.Tau), Disjoint Ev Od → Ev.card = Od.card →
      (∀ τ ∈ Ev, nrmId D lam τ (idl (QuotientGroup.mk t)) = (p : ℝ) ^ (-iv)) →
      (∀ τ ∈ Od, nrmId D lam τ (idl (QuotientGroup.mk t)) = (p : ℝ) ^ iv) →
      (∀ τ, τ ∉ Ev → τ ∉ Od → nrmId D lam τ (idl (QuotientGroup.mk t)) = 1) →
      (∀ i < D.R.m,
        ‖lamC lam ((rhoOf D mt i t : ℂˣ) : ℂ)‖ = (p : ℝ) ^ (iv * (∑ τ ∈ Ev, C.sSharp i τ - ∑ τ ∈ Od, C.sSharp i τ)) ∧
        ‖lamC lam ((rhoOf' D mt i t : ℂˣ) : ℂ)‖ = (p : ℝ) ^ (-(iv * (∑ τ ∈ Ev, C.sDiv i τ - ∑ τ ∈ Od, C.sDiv i τ)))) ∧
      ∀ c : ℤ, (∏ _τ ∈ Ev, ((p : ℝ) ^ (-iv)) ^ c) * ∏ _τ ∈ Od, ((p : ℝ) ^ iv) ^ c = 1

def brOf (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), rhoThreeOf D C mt → br D C mt

def UnrAt (D : D7) {N : ℕ} (μ : HeckeU D N) (p : ℕ) : Prop :=
  ∀ u, IntU D u → (∀ q : ℕ, q.Prime → q ≠ p → ZeroAt D q ((u : AE D) - 1)) → μ.f u = 1

def brUnit (D : D7) (Q : DtAd D) : Prop :=
  ∀ (N₀ N N' : ℕ) (μ : HeckeU D N₀) (m1 : D.Dt →* ℂˣ) (p : ℕ), p.Prime → Even N₀ → MuTil D Q μ m1 → UnrAt D μ p →
    ∀ t, InUnitaryOneIdeles D t → IntU D t → (∀ q : ℕ, q.Prime → q ≠ p → ZeroAt D q ((t : AE D) - 1)) →
      rhoA D m1 N' (Q.q t) = 1 ∧ rhoA' D m1 N (Q.q t) = 1

def NearOne (D : D7) (n k : ℕ) {N : ℕ} (g : GL (Fin N) (AE D)) : Prop :=
  ∀ i j, ∃ a : ℕ, 0 < a ∧ Nat.Coprime a n ∧ ∃ s ∈ OhE D,
    (a : AE D) * ((g : Matrix (Fin N) (Fin N) (AE D)) i j - (1 : Matrix (Fin N) (Fin N) (AE D)) i j) = (n : AE D) ^ k * s

def repAd (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (N : ℕ) (g : GA D N) (n k : ℕ), 0 < n →
    ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γA : GA D N),
      IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) ∧ NearOne D n k ((γA * g : GA D N) : GL (Fin N) (AE D))

def valDet (D : D7) (Q : DtAd D) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N : ℕ) (g : GA D N), NearOne D p 1 (g : GL (Fin N) (AE D)) →
    ∃ (h : ℕ) (z : unitary D.host.E), PowRat D (Q.q (dtG D g)) h z ∧ PUnit D lam (z : D.host.E)

def repVal (D : D7) (Q : DtAd D) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N : ℕ) (g : GA D N), NearOne D p 1 (g : GL (Fin N) (AE D)) →
    ‖lamC lam ((D.chiD (Q.q (dtG D g)) : ℂˣ) : ℂ)‖ = 1 ∧
    ∀ i < D.R.m, ‖lamC lam ((rhoOf D mt i (Q.q (dtG D g)) : ℂˣ) : ℂ)‖ = 1 ∧
      ‖lamC lam ((rhoOf' D mt i (Q.q (dtG D g)) : ℂˣ) : ℂ)‖ = 1

theorem repVal_of (D : D7) (Q : DtAd D) (mt : ℕ → D.Dt →* ℂˣ) (h : valDet D Q) (hu : repUnitsOf D mt) : repVal D Q mt := by
  intro p _ lam N g hg
  obtain ⟨k, z, hz1, hz2⟩ := h p lam N g hg
  exact hu p lam _ k z hz1 hz2

def ThetaD.WB {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ} (Θ : ThetaD D cc δ N N') (e0 : VC D N N' → ℂ) : Prop :=
  normSq D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Θ.gen e0) = 1

def ThetaUnitAbsoluteValue (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  ∀ (N N' : ℕ), ∀ e0 ∈ TT D (tor0 D cc δ) N N', ∀ Θ : ThetaD D cc δ N N', Θ.WB e0 →
    ∃ c0 : ℂ, Θ.IsResidueClassZero c0 ∧ ‖c0‖ = (Real.sqrt (normSq D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') e0))⁻¹

private lemma unit_abs_of_normalisation_lemma (D : D7) (T : Tor D) {N N' : ℕ} (La' : AddSubgroup (VC D N N')) (c : ℂ)
    (G : VC D N N' → ℂ) : normSq D T La' (c • G) = ‖c‖ ^ 2 * normSq D T La' G := by
  unfold Formalism.MainNotions.TaylorLogMetric.normSq
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc, MeasureTheory.average]
  exact MeasureTheory.integral_const_mul _ _

theorem unit_abs_of_normalisation {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : kjOne D cc δ) : ThetaUnitAbsoluteValue D cc δ := by
  intro N N' e0 he Θ hWB
  obtain ⟨c0, hc0, hgen⟩ := h N N' Θ
  refine ⟨c0, hc0, ?_⟩
  unfold ThetaD.WB at hWB
  rw [hgen e0 he, unit_abs_of_normalisation_lemma] at hWB
  have hn : normSq D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') e0 = (‖c0‖⁻¹) ^ 2 := by
    have hc : ‖c0‖ ≠ 0 := norm_ne_zero_iff.mpr hc0.1
    field_simp
    rw [mul_comm]
    exact hWB
  rw [hn, Real.sqrt_sq (inv_nonneg.mpr (norm_nonneg _)), inv_inv]

def AdLift.WeightGeneratorsInLattice {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (A : AdLift D cc δ e Q O i) : Prop :=
  A.Θ.WB (e00 D e (D.R.N i) (D.R.N (i + 1)))

theorem AdLift.unit_abs_of_normalisation {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (A : AdLift D cc δ e Q O i) (h : kjOne D cc δ)
    (he : e00 D e (D.R.N i) (D.R.N (i + 1)) ∈ TT D (tor0 D cc δ) (D.R.N i) (D.R.N (i + 1))) (hw : A.WeightGeneratorsInLattice) :
    ∃ c0 : ℂ, A.Θ.IsResidueClassZero c0 ∧ ‖c0‖ = (Real.sqrt (normSq D (tor0 D cc δ) (La0 D (tor0 D cc δ) (D.R.N i) (D.R.N (i + 1)))
      (e00 D e (D.R.N i) (D.R.N (i + 1)))))⁻¹ := by
  exact Formalism.MainNotions.GL3Columns.unit_abs_of_normalisation h _ _ _ he A.Θ hw

def scal (D : D7) : Prop :=
  ∀ (N N' : ℕ) (s s' : D.what₂.Tau → ℂ) (Qp : MvPolynomial (FrV D N) ℂ) (dg : D.what₂.Tau → ℕ), HomDeg D Qp dg →
    ∀ (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ),
      polD D (fun τ => s τ * s' τ) Qp y' = MvPolynomial.C (∏ τ, s τ ^ dg τ) * polD D s' Qp y' ∧
      sclP D s (polD D s' Qp y') = polD D (fun τ => s τ * s' τ) Qp y'

def oddRat (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 →
    ∀ W : WeilO D cc δ N N' e0, W.ep = 1 → W.ep' = -1 → ∀ a a' : D.what₂.Tau → ℤ,
      (∀ τ, 2 * a τ = -W.chV'.n τ - (N' : ℤ)) → (∀ τ, 2 * a' τ = W.chV.n τ + (N : ℤ)) →
    ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (γA : GA D N) (γA' : GA D N'),
      IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) →
      IsRat D (γA' : GL (Fin N') (AE D)) (γ' : Matrix (Fin N') (Fin N') D.host.E) →
      ∀ F ∈ TT D (tor0 D cc δ) N N', W.Om γA γA' F = fun y =>
        (∏ τ, embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det ^ (-a τ) *
          embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det ^ (-a' τ)) *
        pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) F y

def AdmE (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  Crv D cc δ ∧ vec22 D (tor0 D cc δ) e ∧ RelativeDeterminantEquation D (tor0 D cc δ) e ∧ movesCompose D

def RankOK (D : D7) (i : ℕ) : Prop := 0 < D.R.N i ∧ 0 < D.R.N (i + 1) ∧ Even (D.R.N i) ∧ Even (D.R.N (i + 1))

def StatementKernelFirst (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := Crv D cc δ → kjOne D cc δ
def StatementVacuumVector (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop := AdmE D cc δ e → kjVac D cc δ e Q
def StatementKernelData (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  AdmE D cc δ e → kjVac D cc δ e Q → kjDat D cc δ e Q
def StatementKernelJacobi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  AdmE D cc δ e → kjOne D cc δ → kjDat D cc δ e Q → KJ D cc δ e Q
def StatementKernelEntry {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (A : AdLift D cc δ e Q O i) : Prop :=
  AdmE D cc δ e → RankOK D i → kjDat D cc δ e Q → scal D → A.kjEntry
def StatementAdjointLiftKernel {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (A : AdLift D cc δ e Q O i) : Prop :=
  AdmE D cc δ e → RankOK D i → A.kjKer
def StatementKernelInvariant (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop := AdmE D cc δ e → kjInvKer D cc δ e
def StatementTermInvariant (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (Q : DtAd D) : Prop := kjInvTerm D cc δ Q
def StatementTypes (D : D7) (Q : DtAd D) : Prop := types D Q
def StatementTypeCharacters (D : D7) (Q : DtAd D) : Prop := types D Q → typesCh D Q
def StatementBrauerOfRepresentation (D : D7) : Prop := rhoUse D → brOf D
def StatementBrauerUnit (D : D7) (Q : DtAd D) : Prop := brUnit D Q
def StatementAdjointRepresentation (D : D7) : Prop := repAd D
def StatementDeterminantValuation (D : D7) (Q : DtAd D) : Prop := relDetP D → valDet D Q
def StatementUnitAbsolute (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := kjOne D cc δ → ThetaUnitAbsoluteValue D cc δ
def StatementScalars (D : D7) : Prop := scal D
def StatementOddRationality (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := Crv D cc δ → admG1 D → IntertwinerUnitary D → admissible_poisson D → oddRat D cc δ

section Rel7

open Formalism.MainNotions.G

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

def applyQ {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) : ℂ_[l] :=
  let P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l] :=
    MvPolynomial.aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      MvPolynomial.C (y' v.1 b v.2.2) * MvPolynomial.X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th

def wwCB (D : D7) : Prop :=
  ∀ (k : Type) [CommRing k] (N : ℕ) (nu : Bool × HH D → YoungDiagram) (y : Bool × HH D → Fin N → ℕ → k),
    DeX N nu y = ∑ᶠ J : KM.ColChoice N nu, MvPolynomial.C (minY N nu J y) *
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)

def wwInj (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (nu : Bool × HH D → YoungDiagram)
    (ph : Module.Dual ℂ_[l] (MvPolynomial ((Bool × HH D) × ℕ × Fin N) ℂ_[l])),
    (∀ y, ph (DeX N nu y) = 0) → ∀ J, ph (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0

def wwKt (D : D7) : Prop :=
  ∀ (N0 N1 : ℕ) (nu : Bool × HH D → YoungDiagram) (I : KM.ColChoice N1 nu),
    ∃ cf : KM.ColChoice N0 nu → MvPolynomial ((Bool × HH D) × Fin N0 × Fin N1) ℤ,
      KM.Gxz N0 N1 nu I = ∑ᶠ J : KM.ColChoice N0 nu,
        MvPolynomial.rename Sum.inl (KM.nablaX N0 nu J) * MvPolynomial.rename Sum.inr (cf J)

def ww (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Bool × HH D → YoungDiagram)
    (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[l])
    (ph : Module.Dual ℂ_[l] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[l]))
    (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[l]),
    (∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[l], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (DeX N0 nu y)) →
    ∀ y' : Bool × HH D → Fin N1 → ℕ → ℂ_[l],
      applyQ l N0 N1 Th Q y' = ∑ᶠ I : KM.ColChoice N1 nu, minY N1 nu I y' * ph (KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I))

def wwEv (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Bool × HH D → YoungDiagram)
    (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[l]) (x : (Bool × HH D) × ℕ × Fin N0 → ℂ_[l])
    (I : KM.ColChoice N1 nu),
    MvPolynomial.eval x (KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I)) =
      (let P : MvPolynomial ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[l] :=
        MvPolynomial.aeval (fun v : (Bool × HH D) × ℕ × Fin N1 => ∑ a : Fin N0,
          MvPolynomial.C (x (v.1, v.2.1, a)) * MvPolynomial.X ((v.1, a, v.2.2) : (Bool × HH D) × Fin N0 × Fin N1))
          (KM.nablaX N1 nu I)
       ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th)

def BasR (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]) : Prop :=
  B.det ≠ 0 ∧
  (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) ∧
  ∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧
    ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)

def dgNu (D : D7) (u : D.what₂.Word) (i : ℕ) (τ : D.what₂.Tau) : ℕ :=
  ∑ z : Bool × HH D, if tauPl D z = τ then (nuD D u i z).card else 0

structure KFTie {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (O : LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) where
  B : ∀ i, (D.chTw u μ).cls i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ_[D.what₂.places.resChar w]
  B_bas : ∀ i, i ≤ D.R.m → ∀ c τ, BasR D (E.lam w) τ (O.lat i c).1 (B i c τ)
  c0 : ∀ i, (D.chTw u μ).cls i → (D.chTw u μ).cls (i + 1) → D.what₂.Tau → ℂ_[D.what₂.places.resChar w]
  unitAbs_eq_one : ∀ i c c' τ, ‖c0 i c c' τ‖ = 1
  th : ∀ i, i < D.R.m → ∀ c c', E.Th u μ w i c c' =
    atLin (fun (k : D.what₂.Tau × Fin (D.R.N (i + 1)) × Fin (D.R.N i)) (j : (Bool × HH D) × Fin (D.R.N i) × Fin (D.R.N (i + 1))) =>
        if tauPl D j.1 = k.1 then
          c0 i c c' k.1 * lamC (E.lam w) (O.dgen k.1) * B (i + 1) c' k.1 k.2.1 j.2.2 * (B i c k.1)⁻¹ j.2.1 k.2.2
        else 0)
      (fun j => MvPowerSeries.X j) (pSer D (E.lam w) (O.Th i c c'))
  prS_can : ∀ i, i < D.R.m → ∀ c (v : E.VQ u μ i c), ∃ Qp : MvPolynomial (FrV D (D.R.N i)) Qbar,
    (D.chTw u μ).sharp i (E.ev u μ i c v) =
      (fun y => evFr D (MvPolynomial.map (algebraMap Qbar ℂ) Qp) (O.frm i y)) ∧
    ∀ y : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ_[D.what₂.places.resChar w],
      E.prS u μ w i c v (DeX (D.R.N i) (nuD D u i) fun s => colsOf (y (tauPl D s))) =
        (∏ τ, (B i c τ).det ^ (-(D.chTw u μ).sSharp i τ)) *
          MvPolynomial.eval (fun k : FrV D (D.R.N i) => (B i c k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map (E.lam w) Qp)
  prT_can : ∀ i, i < D.R.m → ∀ c' (v' : E.VQ u μ (i + 1) c'),
    ∃ (Q' : MvPolynomial (FrV D (D.R.N (i + 1))) Qbar)
      (ph' : Module.Dual ℂ_[D.what₂.places.resChar w]
        (MvPolynomial ((Bool × HH D) × ℕ × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w])),
    (∀ y', (∏ τ, ((D.chTw u μ).de (i + 1) y' τ) ^ ((D.chTw u μ).sDiv i τ)) * E.ev u μ (i + 1) c' v' y' =
      evFr D (MvPolynomial.map (algebraMap Qbar ℂ) Q') (O.frm (i + 1) y')) ∧
    (∀ I, E.prT u μ w i c' v' I =
      ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (D.R.N (i + 1)) (nuD D u i) I))) ∧
    ∀ y' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w],
      ph' (DeX (D.R.N (i + 1)) (nuD D u i) fun s => colsOf (y' (tauPl D s))) =
        (∏ τ, (B (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)) *
          MvPolynomial.eval (fun k : FrV D (D.R.N (i + 1)) => (B (i + 1) c' k.1 * y' k.1) k.2.1 k.2.2)
            (MvPolynomial.map (E.lam w) Q')

namespace KFTie

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup}
  {O : LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : KFTie E O w)

def unS (i : ℕ) (c : (D.chTw u μ).cls i) : ℂ_[D.what₂.places.resChar w] :=
  lamC (E.lam w) ((rhoOf D O.mt i (O.dt i c) : ℂˣ) : ℂ) * ∏ τ, (T.B i c τ).det ^ ((D.chTw u μ).sSharp i τ)

def unT (i : ℕ) (c' : (D.chTw u μ).cls (i + 1)) : ℂ_[D.what₂.places.resChar w] :=
  lamC (E.lam w) ((rhoOf' D O.mt i (O.dt (i + 1) c') : ℂˣ) : ℂ) * ∏ τ, (T.B (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)

def cK (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : ℂ_[D.what₂.places.resChar w] :=
  (∏ z : Bool × HH D, T.c0 i c c' (tauPl D z) ^ (nuD D u i z).card)⁻¹

def UnitsLatticeIndependent : Prop := ∀ i (c₁ c₂ : (D.chTw u μ).cls i) (c₁' c₂' : (D.chTw u μ).cls (i + 1)) τ, T.c0 i c₁ c₁' τ = T.c0 i c₂ c₂' τ

theorem cK_of_C0Free (h : T.UnitsLatticeIndependent) (i : ℕ) (c₁ c₂ : (D.chTw u μ).cls i) (c₁' c₂' : (D.chTw u μ).cls (i + 1)) :
    T.cK i c₁ c₁' = T.cK i c₂ c₂' := by
  unfold KFTie.cK
  congr 1
  exact Finset.prod_congr rfl fun z _ => by rw [h i c₁ c₂ c₁' c₂']

def un (i : ℕ) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) : ℂ_[D.what₂.places.resChar w] :=
  T.cK i c c' * T.unS i c * T.unT i c'

def kfPair : Prop :=
  ∀ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : E.VQ u μ i c) (v' : E.VQ u μ (i + 1) c'),
    E.ev u μ (i + 1) c' v' = (D.chTw u μ).Kmap i c c' (E.ev u μ i c v) →
    ∀ I, E.prT u μ w i c' v' I =
      T.un i c c' * E.prS u μ w i c v (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c')
        (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I))

def kfSum : Prop :=
  ∀ i, i < D.R.m → ∀ (x : ((Tw.fm u μ).lat i).V) (y : ((Tw.fm u μ).lat (i + 1)).V),
    (Tw.fm u μ).emb (i + 1) y = (D.chTw u μ).K i ((Tw.fm u μ).emb i x) →
    ∀ (v : ∀ c, E.VQ u μ i c), (∀ c, E.ev u μ i c (v c) = (Tw.fm u μ).emb i x c) →
    ∀ (c' : (D.chTw u μ).cls (i + 1)) (v' : E.VQ u μ (i + 1) c'), E.ev u μ (i + 1) c' v' = (Tw.fm u μ).emb (i + 1) y c' →
    ∀ I, E.prT u μ w i c' v' I = ∑ c, ((Nat.card ((D.chTw u μ).stab i c) : ℂ_[D.what₂.places.resChar w]))⁻¹ *
      (T.un i c c' * E.prS u μ w i c (v c) (KM.applyAt0 (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (E.Th u μ w i c c')
        (KM.Gxz (D.R.N i) (D.R.N (i + 1)) (nuD D u i) I)))

def detB : Prop :=
  ∀ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl → ∀ i, i ≤ D.R.m → ∀ c τ,
    ‖(T.B i c τ).det‖ = nrmId D (E.lam w) τ (idl (QuotientGroup.mk (O.dt i c)))

def unUnit : Prop :=
  ∀ i, i < D.R.m → (∀ c, ‖T.unS i c‖ = 1) ∧ (∀ c', ‖T.unT i c'‖ = 1) ∧ ∀ c c', ‖T.cK i c c'‖ = 1

def UnIs : Prop := ∀ i, i < D.R.m → ∀ c c', E.un u μ w i c c' = T.un i c c'

end KFTie

def RhoAlg {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) : Prop :=
  ∀ i, i < D.R.m → (∀ c, ((rhoOf D O.mt i (O.dt i c) : ℂˣ) : ℂ) ∈ Qbar) ∧
    ∀ c', ((rhoOf' D O.mt i (O.dt (i + 1) c') : ℂˣ) : ℂ) ∈ Qbar

def ThAlg {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) : Prop :=
  ∀ i, i < D.R.m → ∀ c c', CoefIn D (O.Th i c c') Qbar

namespace KFTie

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup}
  {O : LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : KFTie E O w)

theorem unUnit_of (idl : D.Dt ⧸ D.UO → IdE D) (hp : RelDetPinned D idl) (hb : brRhoOf D (D.chTw u μ) O.mt) (hd : T.detB) :
    T.unUnit := by
  intro i hi
  have hbi := hb idl hp (D.what₂.places.resChar w) (E.lam w)
  refine ⟨fun c => ?_, fun c' => ?_, fun c c' => ?_⟩
  · unfold KFTie.unS
    rw [norm_mul, norm_prod, ((hbi (O.dt i c)).2 i hi).1, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun τ _ => ?_)
    rw [norm_zpow, hd idl hp i hi.le c τ]
    have hne : nrmId D (E.lam w) τ (idl (QuotientGroup.mk (O.dt i c))) ≠ 0 := by
      rw [← hd idl hp i hi.le c τ]
      exact norm_ne_zero_iff.mpr (T.B_bas i hi.le c τ).1
    rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hne)]
  · unfold KFTie.unT
    rw [norm_mul, norm_prod, ((hbi (O.dt (i + 1) c')).2 i hi).2, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun τ _ => ?_)
    rw [norm_zpow, hd idl hp (i + 1) hi c' τ]
    have hne : nrmId D (E.lam w) τ (idl (QuotientGroup.mk (O.dt (i + 1) c'))) ≠ 0 := by
      rw [← hd idl hp (i + 1) hi c' τ]
      exact norm_ne_zero_iff.mpr (T.B_bas (i + 1) hi c' τ).1
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hne)]
  · unfold KFTie.cK
    rw [norm_inv, norm_prod]
    simp [norm_pow, T.unitAbs_eq_one]

def parUnit : Prop :=
  InertK D (D.what₂.places.resChar w) → D.what₂.places.resChar w ≠ 2 → ∀ i, i ≤ D.R.m → ∀ c, ‖∏ τ, (T.B i c τ).det‖ = 1

theorem parUnit_of (idl : D.Dt ⧸ D.UO → IdE D) (hp : RelDetPinned D idl) (hb : brRhoOf D (D.chTw u μ) O.mt) (hd : T.detB)
    (hχ : chiUnitInert D) (ha : PowRatAll D) : T.parUnit := by
  intro hK h2 i hi c
  rw [norm_prod]
  simp_rw [hd idl hp i hi c]
  obtain ⟨k, z, hz⟩ := ha (O.dt i c)
  have h1 := hχ (D.what₂.places.resChar w) (E.lam w) h2 hK (O.dt i c) k z hz
  rw [(hb idl hp _ (E.lam w) (O.dt i c)).1, Finset.prod_inv_distrib] at h1
  exact inv_eq_one.mp h1

theorem norm_un (h : T.unUnit) {i : ℕ} (hi : i < D.R.m) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) :
    ‖T.un i c c'‖ = 1 := by
  unfold KFTie.un
  rw [norm_mul, norm_mul, (h i hi).2.2 c c', (h i hi).1 c, (h i hi).2.1 c']
  norm_num

end KFTie

def kf {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → InertK D (D.what₂.places.resChar w) → AllSplit D (D.what₂.places.resChar w) →
    ∀ T : KFTie E (O u μ) w, T.kfPair ∧ T.kfSum ∧ T.unUnit

def kfAll {D : D7} {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ)) : Prop :=
  ∀ u μ w, LevFree Dx u μ w → ∀ T : KFTie E (O u μ) w, T.kfPair ∧ T.kfSum ∧ T.unUnit

theorem kf_of_kfAll {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {O : ∀ u μ, LiftObj D (D.chTw u μ)}
    (h : kfAll E O) : kf E O := by
  intro u μ w hL _ _ T
  exact h u μ w hL T

theorem unUnit_ent {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {O : ∀ u μ, LiftObj D (D.chTw u μ)}
    (h : kfAll E O) (hu : ∀ u μ w, LevFree Dx u μ w → ∃ T : KFTie E (O u μ) w, T.UnIs) : E.UnUnit := by
  intro u μ w hL i hi c c'
  obtain ⟨T, hT⟩ := hu u μ w hL
  rw [hT i hi c c']
  exact KFTie.norm_un T (h u μ w hL T).2.2 hi c c'

def KFHyp (D : D7) {u : D.what₂.Word} {μ : D.what₂.Tup} (O : LiftObj D (D.chTw u μ)) : Prop :=
  ww D ∧ wwCB D ∧ wwInj D ∧ (∀ i < D.R.m, liftTieH D O i (dgNu D u i)) ∧ ThAlg O ∧ RhoAlg O

def StatementWeylChangeBasis (D : D7) : Prop := wwCB D
def StatementWeylMapInjective (D : D7) : Prop := wwCB D → wwInj D
def StatementWeylMapKernel (D : D7) : Prop := wwKt D
def StatementWeylLatticeMap (D : D7) : Prop := wwCB D → ww D
def StatementWeylMapEvaluation (D : D7) : Prop := wwEv D
def StatementKernelFormPair {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup}
    {O : LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : KFTie E O w) : Prop := KFHyp D O → T.kfPair
def StatementKernelFormSum {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup}
    {O : LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : KFTie E O w) : Prop := KFHyp D O → T.kfSum
def StatementParityUnit {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup}
    {O : LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : KFTie E O w) : Prop :=
  Pinned D → brRhoOf D (D.chTw u μ) O.mt → T.detB → chiUnitInert D → PowRatAll D → T.parUnit
def StatementDeterminantB {D : D7} {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {u : D.what₂.Word} {μ : D.what₂.Tup}
    {O : LiftObj D (D.chTw u μ)} {w : D.what₂.places.Pl} (T : KFTie E O w) : Prop := T.detB

open IsDedekindDomain in

def OverP (D : D7) (p : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop := (p : 𝓞 D.host.E) ∈ P.asIdeal

open IsDedekindDomain in

def ConjP (D : D7) (P Q : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∀ a b : 𝓞 D.host.E, (b : D.host.E) = D.host.conj (a : D.host.E) → (a ∈ P.asIdeal ↔ b ∈ Q.asIdeal)

open IsDedekindDomain in

def HalfP (D : D7) (p : ℕ) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  (∀ P ∈ S, OverP D p P) ∧ ∀ P Q, OverP D p P → ConjP D P Q → (P ∈ S ↔ Q ∉ S)

def SuppAt (D : D7) (p : ℕ) {N : ℕ} (g : GL (Fin N) (AE D)) : Prop := ∀ q : ℕ, q.Prime → q ≠ p → TrivAt D q g

open IsDedekindDomain in

def kfPhi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  ∀ N N' : ℕ, 0 < N → 0 < N' → Even N → Even N' →
    ∀ (W : WeilO D cc δ N N' (e00 D e N N')) (m1 : D.Dt →* ℂˣ), IsKJ D Q W m1 →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.E)), HalfP D p S →
    ∀ (n : ℕ) (r : Fin n → ℂ) (z : Fin n → Matrix (Fin N') (Fin N) D.host.E),
      (∀ k, ∃ a : ℕ, 0 < a ∧ Nat.Coprime a p ∧ a • pt D (tor0 D cc δ) δ (z k) ∈ La0 D (tor0 D cc δ) N N') →
    ∀ (g₁ : GA D N) (g₁' : GA D N'), TrivAt D p (g₁ : GL (Fin N) (AE D)) → TrivAt D p (g₁' : GL (Fin N') (AE D)) →
    ∃ Xi : ((∀ P : S, Matrix (Fin N') (Fin N) (EP D P.1)) → ℂ) →ₗ[ℂ] (VC D N N' → ℂ),
      ∀ (g : GA D N) (g' : GA D N'), SuppAt D p (g : GL (Fin N) (AE D)) → SuppAt D p (g' : GL (Fin N') (AE D)) →
      ∀ L L', Moves D ((g₁ * g : GA D N) : GL (Fin N) (AE D)) L → Moves D ((g₁' * g' : GA D N') : GL (Fin N') (AE D)) L' →
        W.Om (g₁ * g) (g₁' * g') (xiC D cc δ r z (e00 D e N N')) = fun y =>
          ((((m1 (Q.q (dtG D g)))⁻¹ * m1 (Q.q (dtG D g')) : ℂˣ) : ℂ)) *
            ((((∏ P : S, Real.sqrt (volP (YP D P.1 (stdL D N) (stdL D N')) (YP D P.1 L L')))⁻¹ : ℝ) : ℂ)) *
            Xi (Set.indicator {x | ∀ P : S, x P ∈ YP D P.1 L L'} 1) y

def kfChar (D : D7) (Q : DtAd D) : Prop :=
  ∀ (N₀ N N' : ℕ) (μ : HeckeU D N₀) (m1 : D.Dt →* ℂˣ) (p : ℕ), p.Prime → Even N₀ → MuTil D Q μ m1 → UnrAt D μ p →
    ∀ (ι : Type) [Fintype ι] (z : ι → (AE D)ˣ) (iv : ι → ℤ) (t t0 : (AE D)ˣ), InUnitaryOneIdeles D t → InUnitaryOneIdeles D t0 → (∀ v, InUnitaryOneIdeles D (z v)) →
      IntU D (t * (t0 * ∏ v, z v ^ iv v)⁻¹) →
      (∀ q : ℕ, q.Prime → q ≠ p → ZeroAt D q (((t * (t0 * ∏ v, z v ^ iv v)⁻¹ : (AE D)ˣ) : AE D) - 1)) →
      rhoA D m1 N' (Q.q t) = rhoA D m1 N' (Q.q t0) * ∏ v, rhoA D m1 N' (Q.q (z v)) ^ iv v ∧
      rhoA' D m1 N (Q.q t) = rhoA' D m1 N (Q.q t0) * ∏ v, rhoA' D m1 N (Q.q (z v)) ^ iv v

def StatementKernelCharacter (D : D7) (Q : DtAd D) : Prop := brUnit D Q → kfChar D Q
def StatementKernelPhi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  AdmE D cc δ e → modelXi D → kfPhi D cc δ e Q

def eJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ := if h : i < D.R.m then (D.hcW u τ).e ⟨i, h⟩ else 0

def sJ' (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ := sExp' D.R (eJ D u τ i) (i + 1)

def sJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ := sExp D.R (eJ D u τ i) (i + 1)

def wJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℚ := wG D.R (eJ D u τ i) (i + 1)

def lamZ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (r : ℕ) : ℚ :=
  if h : r < D.R.k then (D.hcW u τ).u ⟨r, h⟩ - ((D.R.k : ℚ) + 1) / 2 + ((r : ℚ) + 1) else 0

def lamTr (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ℕ → ℕ → ℚ
  | 0, r => lamZ D u τ r
  | j + 1, r => if r < D.R.N j then lamTr D u τ j r + sJ' D u τ j - sJ D u τ j
      else if r < D.R.N (j + 1) then -sJ D u τ j else 0

def nuTr (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i r : ℕ) : ℚ := lamTr D u τ i r + sJ' D u τ i

def lamNo (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j r : ℕ) : ℚ := lamTr D u τ j r + (j : ℚ) * ((D.R.t : ℚ) + 1) / 2

def wtI (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    (∀ i < D.R.m, (∀ r < D.R.N i, lamTr D u τ (i + 1) r = lamTr D u τ i r - ((D.R.t : ℚ) + 1) / 2) ∧
      (∀ r, D.R.N i ≤ r → r < D.R.N (i + 1) → lamTr D u τ (i + 1) r = -sJ D u τ i) ∧
      sJ' D u τ i - wJ D u τ i = (i : ℚ) * ((D.R.t : ℚ) + 1) / 2 ∧
      sJ D u τ i - wJ D u τ i = ((i : ℚ) + 1) * ((D.R.t : ℚ) + 1) / 2 ∧
      ∀ r < D.R.N i, nuTr D u τ i r = lamNo D u τ i r + wJ D u τ i) ∧
    ∀ j ≤ D.R.m, ∀ r < D.R.N j, lamNo D u τ j r =
      if r < D.R.k then lamZ D u τ r else -wJ D u τ ((r - D.R.k) / (D.R.t + 1))

def wtRec (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), ∀ i < D.R.m,
    (∀ C : ColumnChain D.R D.what₂.Tau (D.hcW u), (C.sSharp i τ : ℚ) = sJ' D u τ i ∧ (C.sDiv i τ : ℚ) = sJ D u τ i) ∧
    ∀ r < D.R.N i, DV.nuRow D u (i + 1) τ r = ((nuTr D u τ i r : ℚ) : ℝ)

structure WTPar (D : D7) (L : SizeData₂ D) : Prop where
  eta : L.etaSz ≤ L.sc.w'' D.R.n / 8
  mt : (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ L.sc.w'' D.R.n / 4
  sc8 : 8 * L.Sc ≤ L.sc.w'' D.R.n
  k4 : (D.R.k : ℝ) ≤ L.sc.w'' D.R.n / 4
  w8 : L.sc.w'' D.R.n ≤ L.sc.b' / 8
  sek : L.Sc + L.etaSz + D.R.k ≤ L.sc.b' / L.sc.x
  nx : (D.R.N D.R.m : ℝ) ≤ L.sc.b' / L.sc.x
  x3 : 3 ≤ L.sc.x
  k2 : 2 ≤ D.R.k
  bT_le : ∀ t, (L.bT t : ℝ) ≤ L.sc.b' * (1 + (L.sc.x ^ 2)⁻¹)
  aT_le : ∀ t, (L.aT t : ℝ) ≤ 2 * L.sc.a
  b'b : L.sc.b' ≤ L.sc.b
  b2 : 2 ≤ L.sc.b
  ba : 2 * L.sc.b ≤ L.sc.a
  off : ∀ u τ, (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → ∀ i : Fin D.R.k,
    -(1 / 2 : ℝ) ≤ (((D.hcW u τ).u i : ℚ) : ℝ) ∧ (((D.hcW u τ).u i : ℚ) : ℝ) ≤ 3 * L.Sc

def wtII (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), ∀ i < D.R.m,
    wJ D u τ i ≤ sJ D u τ i ∧ L.sc.w'' D.R.n - D.R.N D.R.m ≤ ((wJ D u τ i : ℚ) : ℝ) ∧ 0 < L.sc.w'' D.R.n - D.R.N D.R.m ∧
    (∀ r < D.R.N i, ∃ n : ℕ, nuTr D u τ i r = n) ∧ ∀ r, r + 1 < D.R.N i → nuTr D u τ i (r + 1) ≤ nuTr D u τ i r

def wtIII (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    (∀ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t →
      (∀ i < D.R.m, ((nuTr D u τ i 0 : ℚ) : ℝ) = (L.aT t : ℝ) + ((wJ D u τ i : ℚ) : ℝ) ∧
        0 ≤ ((wJ D u τ i : ℚ) : ℝ) ∧ ((wJ D u τ i : ℚ) : ℝ) ≤ 2 * L.sc.b' ∧
        ∀ r, 1 ≤ r → r < D.R.N i → ((nuTr D u τ i r : ℚ) : ℝ) ≤ 2 * L.sc.b') ∧
      ∀ j ≤ D.R.m, ∀ r, 1 ≤ r → r < D.R.N j → |((lamTr D u τ j r : ℚ) : ℝ)| ≤ 2 * L.sc.b') ∧
    (D.host.IsThin (D.eTau τ : D.R.GG) →
      (∀ i < D.R.m, ∀ r < D.R.N i, ((nuTr D u τ i r : ℚ) : ℝ) ≤ L.sc.b') ∧
      ∀ j ≤ D.R.m, ∀ r < D.R.N j, |((lamTr D u τ j r : ℚ) : ℝ)| ≤ L.sc.b') ∧
    ((D.eTau τ : D.R.GG) ∈ D.host.thickPlaces →
      (∀ i < D.R.m, ∀ r < D.R.N i, ((nuTr D u τ i r : ℚ) : ℝ) ≤ 2 * L.sc.b) ∧
      ∀ j ≤ D.R.m, ∀ r < D.R.N j, |((lamTr D u τ j r : ℚ) : ℝ)| ≤ 2 * L.sc.b) ∧
    ∀ i < D.R.m, ∀ r < D.R.N i, ((nuTr D u τ i r : ℚ) : ℝ) ≤ 3 * L.sc.a

def StatementWeightFirst (D : D7) : Prop := wtI D
def StatementWeightRecursion (D : D7) : Prop := wtI D → wtRec D
def StatementWeightSecond (D : D7) (L : SizeData₂ D) : Prop := WTPar D L → wtI D → wtII D L
def StatementWeightThird (D : D7) (L : SizeData₂ D) : Prop := WTPar D L → wtI D → wtII D L → wtIII D L

theorem N_cast (D : D7) (j : ℕ) : (D.R.N j : ℚ) = (D.R.k : ℚ) + (j : ℚ) * ((D.R.t : ℚ) + 1) := by
  simp only [Formalism.BasicNotions.Ranks.N]
  push_cast
  ring

theorem sJ'_sub_sJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) :
    sJ' D u τ i - sJ D u τ i = -(((D.R.t : ℚ) + 1) / 2) := by
  simp only [sJ', sJ, Formalism.BasicNotions.sExp', Formalism.BasicNotions.sExp, Nat.add_sub_cancel, N_cast]
  push_cast
  ring

theorem sJ'_sub_wJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) :
    sJ' D u τ i - wJ D u τ i = (i : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
  simp only [sJ', wJ, Formalism.BasicNotions.sExp', Formalism.BasicNotions.wG, N_cast]
  push_cast
  ring

theorem sJ_sub_wJ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) :
    sJ D u τ i - wJ D u τ i = ((i : ℚ) + 1) * ((D.R.t : ℚ) + 1) / 2 := by
  simp only [sJ, wJ, Formalism.BasicNotions.sExp, Formalism.BasicNotions.wG, Nat.add_sub_cancel, N_cast]
  push_cast
  ring

theorem lamNo_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) : ∀ r < D.R.N j, lamNo D u τ j r =
    if r < D.R.k then lamZ D u τ r else -wJ D u τ ((r - D.R.k) / (D.R.t + 1)) := by
  induction j with
  | zero =>
    intro r hr
    have hk : r < D.R.k := by simpa [Formalism.BasicNotions.Ranks.N] using hr
    simp [lamNo, lamTr, hk]
  | succ j ih =>
    intro r hr
    by_cases hrj : r < D.R.N j
    · have h1 : lamNo D u τ (j + 1) r = lamNo D u τ j r := by
        simp only [lamNo, lamTr, if_pos hrj]
        have h2 := sJ'_sub_sJ D u τ j
        push_cast
        linarith
      rw [h1, ih r hrj]
    · have hN0 : D.R.N j = D.R.k + j * (D.R.t + 1) := rfl
      have hN1 : D.R.N (j + 1) = D.R.k + j * (D.R.t + 1) + (D.R.t + 1) := by
        simp only [Formalism.BasicNotions.Ranks.N]
        ring
      have hr' := hr
      rw [hN1] at hr'
      have hrj' := hrj
      rw [hN0] at hrj'
      have hk : ¬ r < D.R.k := by
        generalize j * (D.R.t + 1) = a at *
        omega
      have hlo : j * (D.R.t + 1) ≤ r - D.R.k := by
        generalize j * (D.R.t + 1) = a at *
        omega
      have hhi : r - D.R.k < (j + 1) * (D.R.t + 1) := by
        rw [add_mul, one_mul]
        generalize j * (D.R.t + 1) = a at *
        omega
      have hdiv : (r - D.R.k) / (D.R.t + 1) = j := Nat.div_eq_of_lt_le hlo hhi
      simp only [lamNo, lamTr, if_neg hrj, if_pos hr, if_neg hk, hdiv]
      have h2 := sJ_sub_wJ D u τ j
      push_cast
      linarith

theorem wtI_thm (D : D7) : wtI D := by
  intro u τ
  refine ⟨fun i hi => ⟨fun r hr => ?_, fun r hr1 hr2 => ?_, sJ'_sub_wJ D u τ i, sJ_sub_wJ D u τ i,
    fun r hr => ?_⟩, fun j _ => lamNo_eq D u τ j⟩
  · simp only [lamTr, if_pos hr]
    have h1 := sJ'_sub_sJ D u τ i
    linarith
  · simp only [lamTr, if_neg (not_lt.mpr hr1), if_pos hr2]
  · simp only [nuTr, lamNo]
    have h1 := sJ'_sub_wJ D u τ i
    linarith

theorem wtRec_thm (D : D7) : wtRec D := by
  intro u τ i hi
  refine ⟨fun C => ⟨?_, ?_⟩, fun r hr => ?_⟩
  · rw [C.sSharp_eq i hi τ]
    simp only [sJ', eJ, dif_pos hi]
  · rw [C.sDiv_eq i hi τ]
    simp only [sJ, eJ, dif_pos hi]
  · have hi1 : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m := ⟨by omega, by omega⟩
    have hw : Formalism.BasicNotions.DV.wSz D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
      simp only [Formalism.BasicNotions.DV.wSz, dif_pos hi1, Nat.add_sub_cancel]
    have key : Formalism.BasicNotions.DV.nuRow D u (i + 1) τ r = (((Formalism.BasicNotions.DV.srcPar D u τ r + (D.hc τ).e ⟨i, hi⟩ -
        (((D.R.N i : ℚ) + (D.R.N (i + 1) : ℚ) - 1 - 2 * (r : ℚ)) / 2)) : ℚ) : ℝ) := by
      unfold Formalism.BasicNotions.DV.nuRow
      rw [hw, Nat.add_sub_cancel]
      push_cast
      ring
    rw [key]
    congr 1
    have hlam : lamTr D u τ i r = lamNo D u τ i r - (i : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
      simp only [lamNo]
      ring
    simp only [nuTr]
    rw [hlam, lamNo_eq D u τ i r hr]
    by_cases hk : r < D.R.k
    · simp only [if_pos hk, lamZ, dif_pos hk, Formalism.BasicNotions.DV.srcPar, sJ', eJ, dif_pos hi, Formalism.BasicNotions.sExp',
        D.hcW_e, N_cast]
      push_cast
      ring
    · have h2 : D.R.k ≤ r := not_lt.mp hk
      have hNi : r < D.R.k + i * (D.R.t + 1) := hr
      have hq : (r - D.R.k) / (D.R.t + 1) < i := by
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
        generalize i * (D.R.t + 1) = a at *
        omega
      have hqm : (r - D.R.k) / (D.R.t + 1) < D.R.m := hq.trans hi
      have h1 := Nat.div_add_mod (r - D.R.k) (D.R.t + 1)
      have hr' : (r : ℚ) = (D.R.k : ℚ) + ((D.R.t : ℚ) + 1) * (((r - D.R.k) / (D.R.t + 1) : ℕ) : ℚ) +
          (((r - D.R.k) % (D.R.t + 1) : ℕ) : ℚ) := by
        have e : r = D.R.k + ((D.R.t + 1) * ((r - D.R.k) / (D.R.t + 1)) + (r - D.R.k) % (D.R.t + 1)) := by
          rw [h1]
          omega
        conv_lhs => rw [e]
        push_cast
        ring
      simp only [if_neg hk, Formalism.BasicNotions.DV.srcPar, dif_neg hk, dif_pos hqm, wJ, Formalism.BasicNotions.wG, eJ, sJ', dif_pos hi,
        Formalism.BasicNotions.sExp', D.hcW_e, N_cast]
      push_cast
      linear_combination hr'

def IsRatU (D : D7) {N : ℕ} (γA : GA D N) : Prop :=
  letI := D.host.cmStar
  ∃ γ : Matrix.unitaryGroup (Fin N) D.host.E, IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E)

structure ClsInt (D : D7) (N : ℕ) where
  J : Subgroup (GA D N)
  I : (GA D N → ℂ) →ₗ[ℂ] ℂ
  unf : ∀ g : GA D N, I (fun h => ((Nat.card {γA : GA D N // IsRatU D γA ∧ g⁻¹ * (γA * h) ∈ J} : ℕ) : ℂ)) = 1

def ClsInt.gam {D : D7} {N : ℕ} (X : ClsInt D N) (g : GA D N) : ℕ :=
  Nat.card {γA : GA D N // IsRatU D γA ∧ g⁻¹ * γA * g ∈ X.J}

def ClsInt.IsReps {D : D7} {N : ℕ} (X : ClsInt D N) (R : Finset (GA D N)) : Prop :=
  ∀ h : GA D N, ∃! g, g ∈ R ∧ ∃ γA : GA D N, IsRatU D γA ∧ g⁻¹ * (γA * h) ∈ X.J

def ClassSumIntegralAlt (D : D7) : Prop :=
  ∀ (N : ℕ) (X : ClsInt D N) (R : Finset (GA D N)), X.IsReps R → ∀ f : GA D N → ℂ,
    (∀ γA h, IsRatU D γA → f (γA * h) = f h) → (∀ h, ∀ j ∈ X.J, f (h * j) = f h) →
    X.I f = ∑ g ∈ R, ((X.gam g : ℕ) : ℂ)⁻¹ * f g

theorem IsRatU.mul {D : D7} {N : ℕ} {a b : GA D N} (ha : IsRatU D a) (hb : IsRatU D b) : IsRatU D (a * b) := by
  obtain ⟨γ, hγ⟩ := ha
  obtain ⟨γ', hγ'⟩ := hb
  refine ⟨γ * γ', ?_⟩
  unfold IsRat at hγ hγ' ⊢
  rw [Subgroup.coe_mul, Units.val_mul, hγ, hγ']
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem IsRatU.inv {D : D7} {N : ℕ} {a : GA D N} (ha : IsRatU D a) : IsRatU D a⁻¹ := by
  obtain ⟨γ, hγ⟩ := ha
  refine ⟨γ⁻¹, ?_⟩
  unfold IsRat at hγ ⊢
  rw [Subgroup.coe_inv, Matrix.coe_units_inv, hγ]
  apply Matrix.inv_eq_right_inv
  have h1 : ((γ * γ⁻¹ : _) : Matrix (Fin N) (Fin N) D.host.E) = 1 := by
    rw [mul_inv_cancel]
    rfl
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * (γ⁻¹ : _) = 1 := h1
  calc (γ : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * ((γ⁻¹ : _) : Matrix (Fin N) (Fin N) D.host.E).map (inc D)
      = ((γ : Matrix (Fin N) (Fin N) D.host.E) * (γ⁻¹ : _)).map (inc D) := by
        ext i j
        simp [Matrix.mul_apply, map_sum, map_mul]
    _ = 1 := by
        rw [h2]
        ext i j
        simp [Matrix.one_apply]

def ClsInt.cnt {D : D7} {N : ℕ} (X : ClsInt D N) (g h : GA D N) : ℕ :=
  Nat.card {γA : GA D N // IsRatU D γA ∧ g⁻¹ * (γA * h) ∈ X.J}

theorem ClsInt.cnt_eq {D : D7} {N : ℕ} (X : ClsInt D N) (g h γ0 : GA D N) (h0 : IsRatU D γ0) (hJ : g⁻¹ * (γ0 * h) ∈ X.J) :
    X.cnt g h = X.gam g := by
  unfold ClsInt.cnt ClsInt.gam
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1 * γ0⁻¹, x.2.1.mul h0.inv, by
        have h1 := X.J.mul_mem x.2.2 (X.J.inv_mem hJ)
        convert h1 using 1
        group⟩
      invFun := fun y => ⟨y.1 * γ0, y.2.1.mul h0, by
        have h1 := X.J.mul_mem y.2.2 hJ
        convert h1 using 1
        group⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }

theorem ClsInt.cnt_zero {D : D7} {N : ℕ} (X : ClsInt D N) (g h : GA D N)
    (hn : ¬ ∃ γA : GA D N, IsRatU D γA ∧ g⁻¹ * (γA * h) ∈ X.J) : X.cnt g h = 0 := by
  unfold ClsInt.cnt
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun x => hn ⟨x.1, x.2⟩⟩

theorem ClsInt.gam_ne {D : D7} {N : ℕ} (X : ClsInt D N) (g : GA D N) : X.gam g ≠ 0 := by
  intro hg
  have hz : ∀ h, X.cnt g h = 0 := by
    intro h
    by_cases hex : ∃ γA : GA D N, IsRatU D γA ∧ g⁻¹ * (γA * h) ∈ X.J
    · obtain ⟨γ0, hγ0, hJ⟩ := hex
      rw [X.cnt_eq g h γ0 hγ0 hJ, hg]
    · exact X.cnt_zero g h hex
  have hu := X.unf g
  have hfun : (fun h => ((Nat.card {γA : GA D N // IsRatU D γA ∧ g⁻¹ * (γA * h) ∈ X.J} : ℕ) : ℂ)) = 0 := by
    funext h
    have h1 := hz h
    unfold ClsInt.cnt at h1
    simp [h1]
  rw [hfun, map_zero] at hu
  exact zero_ne_one hu

theorem class_sum_integral_holds (D : D7) : ClassSumIntegralAlt D := by
  intro N X R hR f hL hJ
  have key : f = ∑ g ∈ R, (((X.gam g : ℕ) : ℂ)⁻¹ * f g) • (fun h => ((X.cnt g h : ℕ) : ℂ)) := by
    funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨g0, ⟨hg0R, γ0, hγ0, hJ0⟩, huniq⟩ := hR h
    rw [Finset.sum_eq_single g0]
    · rw [X.cnt_eq g0 h γ0 hγ0 hJ0]
      have hgam : ((X.gam g0 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast X.gam_ne g0
      have hf : f h = f g0 := by
        rw [← hL γ0 h hγ0]
        have h1 : γ0 * h = g0 * (g0⁻¹ * (γ0 * h)) := by group
        rw [h1, hJ g0 _ hJ0]
      rw [hf]
      field_simp
    · intro g hgR hne
      rw [X.cnt_zero g h (fun ⟨γ, hγ, hJg⟩ => hne (huniq g ⟨hgR, γ, hγ, hJg⟩)), Nat.cast_zero, mul_zero]
    · intro hn
      exact absurd hg0R hn
  conv_lhs => rw [key]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [map_smul, smul_eq_mul]
  have hu := X.unf g
  unfold ClsInt.cnt
  rw [hu, mul_one]

structure CSSet (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) where
  posN : 0 < N
  posN' : 0 < N'
  ev : Even (N * N')
  e0 : VC D N N' → ℂ
  unitaryTransvection_zero_first_mem_closure : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')
  W : WeilO D cc δ N N' e0
  ep : W.ep = 1
  ep' : W.ep' = -1
  a : D.what₂.Tau → ℤ
  a' : D.what₂.Tau → ℤ
  a_eq : ∀ τ, 2 * a τ = -W.chV'.n τ - (N' : ℤ)
  a'_eq : ∀ τ, 2 * a' τ = W.chV.n τ + (N : ℤ)

def csI (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  ∀ (N N' : ℕ) (S : CSSet D cc δ N N') (Θ : ThetaD D cc δ N N'), ∃ c0 : ℂ, Θ.IsResidueClassZero c0 ∧
    ∀ (g : GA D N) (g' : GA D N'), ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ P,
      Θ.Th P (S.W.Om g g' F) = c0 * applyO D (tor0 D cc δ) P (S.W.Om g g' F)

theorem csI_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : kjOne D cc δ) : csI D cc δ := by
  intro N N' S Θ
  obtain ⟨c0, hc0, -⟩ := h N N' Θ
  exact ⟨c0, hc0, fun g g' F hF P => hc0.2 P _ (S.W.maps g g' F hF)⟩

def csII (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ (N N' : ℕ) (S : CSSet D cc δ N N')
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (γA : GA D N) (γA' : GA D N'),
    IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) →
    IsRat D (γA' : GL (Fin N') (AE D)) (γ' : Matrix (Fin N') (Fin N') D.host.E) →
    ∀ (g : GA D N) (g' : GA D N'), ∀ F ∈ TT D (tor0 D cc δ) N N',
      S.W.Om (γA * g) (γA' * g') F = fun y =>
        (∏ τ, embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det ^ (-S.a τ) *
          embT D τ (γ' : Matrix (Fin N') (Fin N') D.host.E).det ^ (-S.a' τ)) *
        pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (S.W.Om g g' F) y

theorem csII_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : oddRat D cc δ) : csII D cc δ := by
  intro N N' S γ γ' γA γA' hγ hγ' g g' F hF
  rw [S.W.mul _ _ _ _ F hF]
  exact h N N' S.posN S.posN' S.ev S.e0 S.unitaryTransvection_zero_first_mem_closure S.W.nz S.W S.ep S.ep' S.a S.a' S.a_eq S.a'_eq
    γ γ' γA γA' hγ hγ' (S.W.Om g g' F) (S.W.maps g g' F hF)

def actS (D : D7) {N N' : ℕ} (γ : Matrix (Fin N) (Fin N) D.host.E) (P : MvPolynomial (Idx D N N') ℂ) : MvPolynomial (Idx D N N') ℂ :=
  MvPolynomial.aeval (fun k : Idx D N N' => ∑ a' : Fin N,
    MvPolynomial.C ((starRingEnd ℂ) (embT D k.1 (γ a' k.2.2))) * MvPolynomial.X ((k.1, k.2.1, a') : Idx D N N')) P

def csIII (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ (N N' : ℕ) (S : CSSet D cc δ N N') (Θ : ThetaD D cc δ N N') (c0 : ℂ), Θ.IsResidueClassZero c0 →
    ∀ (X : ClsInt D N) (R : Finset (GA D N)), X.IsReps R →
    ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ Pg : GA D N → MvPolynomial (Idx D N N') ℂ,
      (∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γA g : GA D N),
        IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) →
        Pg (γA * g) = (∏ τ, embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det ^ (S.a τ)) •
          actS D (γ : Matrix (Fin N) (Fin N) D.host.E) (Pg g)) →
      (∀ g, ∀ j ∈ X.J, ∀ α, MvPolynomial.coeff α (Pg (g * j)) • S.W.Om (g * j) 1 F = MvPolynomial.coeff α (Pg g) • S.W.Om g 1 F) →
      ∀ g' : GA D N', X.I (fun g => Θ.Th (Pg g) (S.W.Om g g' F)) =
        c0 * ∑ g ∈ R, ((X.gam g : ℕ) : ℂ)⁻¹ * applyO D (tor0 D cc δ) (Pg g) (S.W.Om g g' F)

def csIIIf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop :=
  letI := D.host.cmStar
  ∀ (N N' : ℕ) (S : CSSet D cc δ N N') (Θ : ThetaD D cc δ N N') (c0 : ℂ), Θ.IsResidueClassZero c0 →
    ∀ (X : ClsInt D N) (R : Finset (GA D N)), X.IsReps R →
    ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ Qg : GA D N → MvPolynomial (FrV D N) ℂ,
      (∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γA g : GA D N),
        IsRat D (γA : GL (Fin N) (AE D)) (γ : Matrix (Fin N) (Fin N) D.host.E) →
        ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ, evFr D (Qg (γA * g)) y =
          (∏ τ, embT D τ (γ : Matrix (Fin N) (Fin N) D.host.E).det ^ (S.a τ)) *
            evFr D (Qg g) (fun τ => (matT D (γ : Matrix (Fin N) (Fin N) D.host.E) τ).conjTranspose * y τ)) →
      (∀ g, ∀ j ∈ X.J, ∀ α, MvPolynomial.coeff α (Qg (g * j)) • S.W.Om (g * j) 1 F = MvPolynomial.coeff α (Qg g) • S.W.Om g 1 F) →
      ∀ (g' : GA D N') (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ),
        X.I (fun g => (∏ τ, (y' τ).det ^ (S.a' τ)) * Θ.Th (polD D (fun _ => 1) (Qg g) y') (S.W.Om g g' F)) =
          c0 * ∑ g ∈ R, ((X.gam g : ℕ) : ℂ)⁻¹ *
            (applyO D (tor0 D cc δ) (polD D (fun _ => 1) (Qg g) y') (S.W.Om g g' F) * ∏ τ, (y' τ).det ^ (S.a' τ))

def StatementClassSumFirst (D : D7) : Prop := ClassSumIntegralAlt D
def StatementClassSumThird (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := Crv D cc δ → ClassSumIntegralAlt D → csII D cc δ → csIII D cc δ
def StatementClassSumThirdFinite (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Prop := csIII D cc δ → csIIIf D cc δ

abbrev LaC (D : D7) (N : ℕ) (nu : Bool × HH D → YoungDiagram) : Type := KM.ColChoice N nu → ℂ

def hvC (D : D7) (N : ℕ) (nu : Bool × HH D → YoungDiagram) (x : Bool × HH D → Fin N → ℕ → ℂ) : LaC D N nu :=
  fun J => minY N nu J x

def Vnu (D : D7) (N : ℕ) (nu : Bool × HH D → YoungDiagram) : Submodule ℂ (LaC D N nu) :=
  Submodule.span ℂ (Set.range (hvC D N nu))

def l2 {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} (φ : LaC D N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} (φ ψ : LaC D N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def canC {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} (φ : LaC D N nu) (y : Bool × HH D → Fin N → ℕ → ℂ) : ℂ :=
  prC φ (hvC D N nu y)

def VnuMap (D : D7) {N N' : ℕ} (nu : Bool × HH D → YoungDiagram) (f : Bool × HH D → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC D N nu) : LaC D N' nu :=
  fun I => ∑ᶠ J : KM.ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def PIJ (D : D7) {N N' : ℕ} (nu : Bool × HH D → YoungDiagram) (s : D.what₂.Tau → ℂ) (I : KM.ColChoice N' nu)
    (J : KM.ColChoice N nu) : MvPolynomial (Idx D N N') ℂ :=
  ∏ z, ∏ c : Fin ((nu z).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen c) =>
    MvPolynomial.C (s (tauPl D z)) * MvPolynomial.X ((tauPl D z, I z c i, J z c k) : Idx D N N'))

def AOp (D : D7) {N N' : ℕ} (nu : Bool × HH D → YoungDiagram) (s : D.what₂.Tau → ℂ) (Θ : VC D N N' → ℂ)
    (φ : LaC D N nu) : LaC D N' nu :=
  fun I => ∑ᶠ J : KM.ColChoice N nu, applyAt0 D (PIJ D nu s I J) Θ * φ J

abbrev frC (D : D7) {N : ℕ} (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) : Bool × HH D → Fin N → ℕ → ℂ :=
  fun z => colsOf (y (tauPl D z))

def InducedNormInvariantMetric (D : D7) : Prop :=
  ∀ (N : ℕ) (nu : Bool × HH D → YoungDiagram),
    (∀ k : Bool × HH D → Matrix (Fin N) (Fin N) ℂ, (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
      (∀ φ ∈ Vnu D N nu, VnuMap D nu k φ ∈ Vnu D N nu ∧ l2 (VnuMap D nu k φ) = l2 φ) ∧
      ((∀ z, (nu z).colLen 0 ≤ N) → l2 (hvC D N nu fun z => colsOf (k z)) = 1)) ∧
    ∀ ip : LaC D N nu →ₗ⋆[ℂ] LaC D N nu →ₗ[ℂ] ℂ,
      (∀ k : Bool × HH D → Matrix (Fin N) (Fin N) ℂ, (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
        (∀ φ ∈ Vnu D N nu, ∀ ψ ∈ Vnu D N nu, ip (VnuMap D nu k φ) (VnuMap D nu k ψ) = ip φ ψ) ∧
        ip (hvC D N nu fun z => colsOf (k z)) (hvC D N nu fun z => colsOf (k z)) = 1) →
      ∀ φ ∈ Vnu D N nu, ip φ φ = (l2 φ : ℂ)

def IsometryOntoDualFrames (D : D7) : Prop :=
  ∀ (N : ℕ) (nu : Bool × HH D → YoungDiagram),
    (∀ φ ∈ Vnu D N nu, (∀ ψ ∈ Vnu D N nu, ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ) ∧
      ∃ ψ ∈ Vnu D N nu, l2 ψ = l2 φ ∧ prC φ ψ = (l2 φ : ℂ)) ∧
    ∀ Λ : Vnu D N nu →ₗ[ℂ] ℂ, ∃ φ ∈ Vnu D N nu, ∀ ψ : Vnu D N nu, Λ ψ = prC φ (ψ : LaC D N nu)

def isoB (D : D7) : Prop :=
  ∀ (N N' : ℕ) (nu : Bool × HH D → YoungDiagram) (s : D.what₂.Tau → ℂ) (Θ : VC D N N' → ℂ) (φ : LaC D N nu)
    (Q : MvPolynomial (FrV D N) ℂ), (∀ y, evFr D Q y = canC φ (frC D y)) →
    ∀ y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ,
      applyAt0 D (polD D s Q y') Θ = canC (AOp D nu s Θ φ) (frC D y')

def isoFun (D : D7) : Prop :=
  ∀ (N N' : ℕ) (nu : Bool × HH D → YoungDiagram) (s : D.what₂.Tau → ℂ) (Θ : VC D N N' → ℂ),
    ∀ φ ∈ Vnu D N nu, AOp D nu s Θ φ ∈ Vnu D N' nu

def isoScale (D : D7) : Prop :=
  ∀ (N N' : ℕ) (nu : Bool × HH D → YoungDiagram) (c s : D.what₂.Tau → ℂ) (Θ : VC D N N' → ℂ) (φ : LaC D N nu),
    AOp D nu (fun τ => c τ * s τ) Θ φ = (∏ z : Bool × HH D, c (tauPl D z) ^ (nu z).card) • AOp D nu s Θ φ

def IpTie {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : LiftObj D C) (i : ℕ) : Prop :=
  (∀ c (f : C.Y i → ℂ), ∀ φ ∈ Vnu D (D.R.N i) (nuD D u i), C.sharp i f = (fun y => canC φ (frC D (O.frm i y))) →
    M.ipV i c f f = (l2 φ : ℂ)) ∧
  ∀ c' (f' : C.Y (i + 1) → ℂ), ∀ ψ ∈ Vnu D (D.R.N (i + 1)) (nuD D u i),
    (∀ y', (∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ)) * f' y' = canC ψ (frC D (O.frm (i + 1) y'))) →
    M.ipV (i + 1) c' f' f' = (l2 ψ : ℂ)

def isoNorm {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : LiftObj D C) (i : ℕ) : Prop :=
  ∀ c c' (f : C.Y i → ℂ), ∀ φ ∈ Vnu D (D.R.N i) (nuD D u i), C.sharp i f = (fun y => canC φ (frC D (O.frm i y))) →
    M.ipV (i + 1) c' (C.wt i c • C.Kmap i c c' f) (C.wt i c • C.Kmap i c c' f) =
      ((((Nat.card (C.stab i c) : ℕ) : ℝ)⁻¹ ^ 2 * l2 (AOp D (nuD D u i) O.dgen (O.Th i c c') φ) : ℝ) : ℂ)

def StatementIsogenyA1 (D : D7) : Prop := InducedNormInvariantMetric D
def StatementIsogenyA2 (D : D7) : Prop := IsometryOntoDualFrames D
def StatementIsogenyB (D : D7) : Prop := isoB D
def StatementIsogenyFunctions (D : D7) : Prop := isoFun D
def StatementIsogenyScale (D : D7) : Prop := isoScale D
def StatementIsogenyNorm {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : LiftObj D C) (i : ℕ) : Prop :=
  i < D.R.m → isoB D → isoFun D → liftTieH D O i (dgNu D u i) → IpTie M O i → isoNorm M O i

end Rel7

def kjAll (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  ∀ (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (O : LiftObj D C) (i : ℕ) (A : AdLift D cc δ e Q O i),
    RankOK D i → A.kjEntry ∧ A.kjPair ∧ A.kjKer

def KernelJacobiProperties (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  kjOne D cc δ ∧ kjVac D cc δ e Q ∧ kjDat D cc δ e Q ∧ KJ D cc δ e Q ∧ kjAll D cc δ e Q ∧ kjInvKer D cc δ e ∧ kjInvTerm D cc δ Q

def CharacterProperties (D : D7) (Q : DtAd D) : Prop :=
  types D Q ∧ typesCh D Q ∧ brUnit D Q ∧ repAd D ∧ scal D ∧ (rhoUse D → brOf D) ∧ (relDetP D → valDet D Q)

def ConclusionW (D : D7) : Prop :=
  wwCB D ∧ wwInj D ∧ wwKt D ∧ ww D ∧ wwEv D ∧ InducedNormInvariantMetric D ∧ IsometryOntoDualFrames D ∧ isoB D ∧ isoFun D ∧ isoScale D

open Formalism.MainNotions.G in

def kfRec (D : D7) : Prop :=
  ∀ (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : LiftObj D (D.chTw u μ))
    (w : D.what₂.places.Pl), LevFree Dx u μ w → ∀ T : KFTie E O w,
    T.detB ∧ ((∀ i < D.R.m, liftTieH D O i (dgNu D u i)) → ThAlg O → RhoAlg O → T.kfPair ∧ T.kfSum)

def isoRec (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (A : ColumnsAtT D.R C) (P : PeriodMap D.R C)
    (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (O : LiftObj D C), ∀ i < D.R.m,
    liftTieH D O i (dgNu D u i) → IpTie M O i → isoNorm M O i

def division_rows_rational_lattice (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  ConclusionW D ∧ (∀ L : SizeData₂ D, WTPar D L → wtII D L ∧ wtIII D L) ∧ kfRec D ∧ (modelXi D → kfPhi D cc δ e Q) ∧ kfChar D Q ∧
    (admG1 D → IntertwinerUnitary D → admissible_poisson D → csIII D cc δ ∧ csIIIf D cc δ) ∧ isoRec D

def aux₃ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop :=
  KernelJacobiProperties D cc δ e Q ∧ CharacterProperties D Q ∧ (admG1 D → IntertwinerUnitary D → admissible_poisson D → oddRat D cc δ) ∧ division_rows_rational_lattice D cc δ e Q

def Stmt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) (Q : DtAd D) : Prop := AdmE D cc δ e → aux₃ D cc δ e Q

open Formalism.MainNotions.G in

theorem aux₃.atP {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (hp : aux₃ D cc δ e Q)
    {Gt : GatTies D} {c : LatCmp D} {Tw : TwForms D}
    {u : D.what₂.Word} {w : D.what₂.places.Pl} [Fact (D.what₂.places.resChar w).Prime]
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)}
    {Lv : Levels Fl} {Ch : Chain Lv}
    (Kp : LocalToGlobal₂ D Gt c Tw u w h Ch) {O : LiftObj D (D.chTw u (D.what₂.muAt w))} (A : ∀ j, AdLift D cc δ e Q O j)
    (hr : ∀ j < D.R.m, RankOK D j) : kjAtP Kp A := by
  exact kernelAtPrime_pairCondition_of_lifts Kp A (fun j hj => ((hp.1.2.2.2.2.1) u _ O j (A j) (hr j hj)).2.1)

theorem aux₃.liftTieH {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (hp : aux₃ D cc δ e Q)
    {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {O : LiftObj D C} {i : ℕ} (hi : i < D.R.m)
    (A : AdLift D cc δ e Q O i) (hr : RankOK D i) (c0 : ℂ) (h0 : A.Θ.IsResidueClassZero c0) (hd : A.IsDef c0) (ht : A.ThIs) :
    liftTieH D O i A.dg := by
  exact liftTieH_of hi A ((hp.1.2.2.2.2.1) u C O i A hr).2.1 c0 h0 hd ht

theorem unit_abs_of_proposition {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (hp : aux₃ D cc δ e Q) : ThetaUnitAbsoluteValue D cc δ := by
  exact unit_abs_of_normalisation hp.1.1

theorem csI_of_conditions {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (hp : aux₃ D cc δ e Q) : csI D cc δ := by
  exact csI_of hp.1.1

theorem csII_of_conditions {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (hp : aux₃ D cc δ e Q)
    (h1 : admG1 D) (h2 : IntertwinerUnitary D) (h3 : admissible_poisson D) : csII D cc δ := by
  exact csII_of (hp.2.2.1 h1 h2 h3)

open Formalism.MainNotions.G in

theorem kfAll_of_conditions {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e : FamE D} {Q : DtAd D} (hp : aux₃ D cc δ e Q)
    {Dx : DivX D} {Tw : TwForms D} {E : KerEnt D Dx Tw} {O : ∀ u μ, LiftObj D (D.chTw u μ)}
    (idl : D.Dt ⧸ D.UO → IdE D) (hi : RelDetPinned D idl) (hu : rhoUse D)
    (h3 : ∀ u μ, rhoThreeOf D (D.chTw u μ) (O u μ).mt)
    (hK : ∀ u μ, ∀ i < D.R.m, liftTieH D (O u μ) i (dgNu D u i)) (hT : ∀ u μ, ThAlg (O u μ)) (hR : ∀ u μ, RhoAlg (O u μ)) :
    kfAll E O := by
  intro u μ w hL T
  obtain ⟨hdB, hkf⟩ := (hp.2.2.2.2.2.1) Dx Tw E u μ (O u μ) w hL T
  obtain ⟨h1, h2⟩ := hkf (hK u μ) (hT u μ) (hR u μ)
  exact ⟨h1, h2, KFTie.unUnit_of T idl hi ((hu u (D.chTw u μ) (O u μ).mt (h3 u μ)).2.2) hdB⟩

def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ x (i : Fm.Ix x) (cc : Ideal (𝓞 (Fm.D x i).host.K)) (δ : ℂ) (e : FamE (Fm.D x i)) (Q : DtAd (Fm.D x i)),
    AdmE (Fm.D x i) cc δ e → aux₃ (Fm.D x i) cc δ e Q

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ConclusionOnFamily Fm

end Formalism.MainNotions.GL3Columns
