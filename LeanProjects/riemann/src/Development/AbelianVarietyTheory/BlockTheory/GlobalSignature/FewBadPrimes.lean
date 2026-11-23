import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX

variable {R : Ranks}

def condE (H : Host R) : ℕ := H.QS * H.q * H.d

example (H : Host R) : condE H = H.condN := rfl

def dlogH (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d) 1).re

example (D : D7) : dlogH D.host = dlogL D 1 := rfl

def frobH (H : Host R) (p : ℕ) : R.A :=
  R.iotaInv (Classical.epsilon (fun g : R.GG =>
    g ∈ {g : R.GG | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ∧ H.galE σ = g})).2

example (D : D7) (p : ℕ) : frobH D.host p = G.hP D p := rfl

def logPowerBoundClassPrimes (H : Host R) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
    l = ⌈Real.logb p (((R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊}

def GoodH (H : Host R) (s : Scale) (p : ℕ) (t0 : R.A) : Prop :=
  G.IsGoodOrbit (addOrderOf (frobH H p))
    (Finset.univ.filter (fun i : Fin (addOrderOf (frobH H p)) => t0 + (i : ℕ) • frobH H p ∈ H.TT))
    (logPowerBoundClassPrimes H s) (G.KG s) (G.rG s) s.delta1 (G.hG s) s.x

example {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (p : ℕ) (t0 : G.HH D) :
    GoodH D.host L.sc p t0 ↔ G.Good X p t0 := Iff.rfl

def IsOrigins {φ : Formalism.HC.Frame} (bs : φ.A → φ.A → φ.A) : Prop :=
  (∀ h t, ∃ i : ℕ, bs h t + i • h = t) ∧ ∀ h t, bs h (t + h) = bs h t

example {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : IsOrigins (φ := D.R.toFrame) X.bs := ⟨X.bs_orb, X.bs_step⟩

open Classical in

def FewBad (H : Host R) (s : Scale) (bs : R.A → R.A → R.A) : Prop :=
  ∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
      s.x ^ (s.eps / 4) ≤ (addOrderOf (frobH H p) : ℝ)),
    Real.log p / p * ((H.TT.filter (fun t => ¬ GoodH H s p (bs (frobH H p) t))).card : ℝ) ≤
  (H.TT.card : ℝ) * s.x ^ (-2 + s.eps)

def CharOf (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ ψ : R.GG →* ℂˣ, ∀ (a : ℕ) (h : a.Coprime H.condN),
    χ (a : ZMod N) = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ)

example (D : D7) {N : ℕ} (χ : DirichletCharacter ℂ N) : CharOf D.host χ ↔ GlobalTheoryTheory.IsCharED D χ := Iff.rfl

def RealBoxes (H : Host R) (Y eps : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), CharOf H χ → GlobalTheoryTheory.IsRealChar χ →
    (H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps) χ) ∧
    (H.q ∣ N → ¬ H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps) χ)

example (D : D7) (Y eps : ℝ) : RealBoxes D.host Y eps ↔ GlobalTheoryTheory.BoxE D Y eps := Iff.rfl

def BoxesInWindow (s : Scale) (H : Host R) : Prop :=
  ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H ∧ Boxq Y s.eps H.q H.d ∧ RealBoxes H Y s.eps

example (s : Scale) (D : D7) : BoxesInWindow s D.host ↔
    ∃ Y : ℝ, PairWin s Y ∧ QDRows_at D Y s.eps ∧ Boxes_at D Y s.eps ∧ GlobalTheoryTheory.BoxE D Y s.eps := Iff.rfl

example (s : Scale) (D : D7) (h : BoxesInWindow s D.host) : BoxesW D s ∧ QDRowsW D s :=
  let ⟨Y, h1, h2, h3, h4⟩ := h
  ⟨⟨Y, h1, h3, h4⟩, Y, h1, h2⟩

def ArithData (C : FC) (s : Scale) (H : Host R) (q0 : ℕ)
    (bs : R.A → R.A → R.A) : Prop :=
  HostVal s C.P.Cpde H ∧ H.CT2 = C.CT2 ∧
  BoxesInWindow s H ∧ |dlogH H| ≤ s.x ^ s.eps ∧ QDq s.x s.eps 4 H.q H.d ∧
  4 * H.Lw * H.T2.card ≤ R.n0 ∧
  IsOrigins bs ∧ FewBad H s bs ∧
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E) ∧
    π - 1 ∈ Ideal.span {((condE H : ℕ) : 𝓞 H.E)}) ∧
  Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
  (H.pde ≡ 1 [MOD Nat.lcm 15 (condE H)] ∧ H.pde' ≡ 1 [MOD Nat.lcm 15 (condE H)]) ∧
  (q0.Prime ∧ 5 ≤ q0 ∧ (q0 : ℝ) ≤ (condE H : ℝ) ^ C.P.Cpde ∧
    ∃ r' : ℕ, IsLeast {l : ℕ | l.Prime ∧ ¬ l ∣ condE H * (H.pde - 1) * (H.pde' - 1)} r' ∧
      q0 ≡ 1 [MOD r' * condE H]) ∧
  H.levelPrimes = {H.g 0, H.g 1, H.pde, H.pde', q0}

def hostAt (H : Host R) (hc : H.ccK = ⊤) (u0 : R.A) (S : Finset ℕ) (hS : ∀ l ∈ S, Nat.Coprime l H.QS) : Host R :=
  { H with
    u0 := u0
    levelPrimes := H.levelPrimes ∪ S
    g_level := fun i => Finset.mem_union_left _ (H.g_level i)
    pde_level := ⟨Finset.mem_union_left _ H.pde_level.1, Finset.mem_union_left _ H.pde_level.2⟩
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := fun p hp => (Finset.mem_union.1 hp).elim (H.level_coprimeS p) (hS p) }

theorem ArithData.ccK_eq {C : FC} {s : Scale} {H : Host R} {q0 : ℕ}
    {bs : R.A → R.A → R.A} (h : ArithData C s H q0 bs) : H.ccK = ⊤ := by
  have h1 := h.1
  unfold HostVal at h1
  casesm* _ ∧ _
  assumption

def bTop (C : FC) (s : Scale) (R : Ranks) : ℝ :=
  s.b' + 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ)

def numWords (C : FC) (s : Scale) (R : Ranks) : ℕ :=
  ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊

def Over {C : FC} (p : Pt C) (s : Scale) (H : Host R) (hc : H.ccK = ⊤)
    (bs : R.A → R.A → R.A) (a b : ℕ → ℤ)
    (code : Finset (Fin (R.k - 2) → Bool)) (off : ℕ → ℕ → ℝ) (u0 : R.A) (T : code → ℕ) : Prop :=
  (∃ hS : ∀ l ∈ Finset.univ.image T, Nat.Coprime l H.QS,
    (⟨p.D.R, p.D.host⟩ : Σ R' : Ranks, Host R') = ⟨R, hostAt H hc u0 (Finset.univ.image T) hS⟩) ∧
  p.L.sc = s ∧
  (∀ (h t : G.HH p.D) (h' t' : R.A), h.val = h'.val → t.val = t'.val →
    (p.ta.Gx.bs h t).val = (bs h' t').val) ∧
  (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧
  (∀ t : p.D.host.TT, p.L.aT t = a (t : p.D.R.A).val ∧ p.L.bT t = b (t : p.D.R.A).val) ∧
  ∃ e : p.D.what₂.Word ≃ code,
    (∀ u (l : Fin (R.k - 2)), wordBits p.D u l.1 = (e u).1 l) ∧ ∀ u, (p.D.mem u).A.T = T (e u)

def ObjectsExist (Q : PtProp) : Prop :=
  ∃ Cdg : ℝ, 0 < Cdg ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ C8 : ℝ, 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
        ∀ (R : Ranks), RankVal s R →
        ∀ (H : Host R) (q0 : ℕ) (bs : R.A → R.A → R.A)
          (hH : ArithData C s H q0 bs),
        ∀ a b : ℕ → ℤ, Win s R.k (H.TT.image Formalism.HC.Frame.A.val) (bTop C s R) a b →
        ∀ code : Finset (Fin (R.k - 2) → Bool), code.card = numWords C s R →
          ∃ off : ℕ → ℕ → ℝ, ∀ u0 : R.A, ∃ (T : code → ℕ) (p : Pt C),
            Over p s H hH.ccK_eq bs a b code off u0 T ∧
            (∀ u, p.L.AdmT u (p.D.mem u).A.T) ∧
            Val C cD ch p.L ∧ p.Has Q ∧ ChProviso_at p.L 3 ∧
            (∀ w, s.b ^ ((R.m : ℝ) / 2) ≤ (T w : ℝ) ∧ (T w : ℝ) ≤ s.b ^ (25 * (R.m : ℝ))) ∧
            FactDGam p.D Cdg

example {Q Q' : PtProp} (hQ : ∀ D L g x y K X c e, Q D L g x y K X c e → Q' D L g x y K X c e)
    (h : ObjectsExist Q) : ObjectsExist Q' := by
  obtain ⟨Cdg, h0, h⟩ := h
  refine ⟨Cdg, h0, fun eps h1 h2 C8 h8 => ?_⟩
  obtain ⟨K0, h⟩ := h eps h1 h2 C8 h8
  refine ⟨K0, fun C hC hP hL => ?_⟩
  obtain ⟨c1, h⟩ := h C hC hP hL
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch hch
  refine ⟨x0, fun s hs hx R hR H q0 bs hH a b hw code hc => ?_⟩
  obtain ⟨off, h⟩ := h s hs hx R hR H q0 bs hH a b hw code hc
  refine ⟨off, fun u0 => ?_⟩
  obtain ⟨T, p, h3, h4, h5, h6, h7⟩ := h u0
  exact ⟨T, p, h3, h4, h5, hQ _ _ _ _ _ _ _ _ _ h6, h7⟩

end GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

end
