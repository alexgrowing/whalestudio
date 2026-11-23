import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SubThreeMulLogTwoLe
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData

theorem hval_lt (e : Formalism.HC.Frame) (h : e.A) : hval e h < e.ord := Formalism.HC.Frame.A.val_lt h

def hOfNat (e : Formalism.HC.Frame) (n : ℕ) : e.A := e.ofNat n

theorem hval_hOfNat (e : Formalism.HC.Frame) (n : ℕ) (hn : n < e.ord) : hval e (hOfNat e n) = n := e.val_ofNat_of_lt hn

theorem hOfNat_hval (e : Formalism.HC.Frame) (h : e.A) : hOfNat e (hval e h) = h := e.ofNat_val h

theorem hval_injective (e : Formalism.HC.Frame) : Function.Injective (hval e) := Formalism.HC.Frame.A.val_injective e

theorem card_HA (e : Formalism.HC.Frame) : Fintype.card e.A = e.ord := e.card_A

private theorem cftData_congr {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A] {N N' q q' d d' : ℕ} [NeZero N]
    (hN : N = N') (hq : q = q') (hd : d = d') (r : (ZMod N)ˣ →* Multiplicative (E0 × A))
    (r' : (ZMod N')ˣ →* Multiplicative (E0 × A))
    (h : ∀ (p : ℕ) (h1 : Nat.Coprime p N) (h2 : Nat.Coprime p N'),
      r (ZMod.unitOfCoprime p h1) = r' (ZMod.unitOfCoprime p h2)) : cftData q d r = cftData q' d' r' := by
  subst hN; subst hq; subst hd
  have hr : r = r' := by
    ext1 u
    have hu : u = ZMod.unitOfCoprime (u : ZMod N).val (ZMod.val_coe_unit_coprime u) := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
    rw [hu]
    exact h _ _ _
  rw [hr]

theorem arithOf_heq {φ φ' : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (H' : Formalism.HC.HostRaw φ') (h : φ = φ') (hq : H.q = H'.q)
    (hd : H.d = H'.d) (hQ : H.QS = H'.QS) (ha : artNum H = artNum H') : HEq (arithOf H) (arithOf H') := by
  subst h
  have hN : H.condN = H'.condN := by
    show H.QS * H.q * H.d = H'.QS * H'.q * H'.d
    rw [hq, hd, hQ]
  haveI : NeZero H.condN :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero) H.hyp.2.1.ne_zero⟩
  apply heq_of_eq
  unfold arithOf
  refine cftData_congr hN hq hd _ _ (fun p h1 h2 => ?_)
  have h3 := congrFun ha p
  unfold artNum at h3
  rw [dif_pos h1, dif_pos h2, Prod.mk.injEq] at h3
  have h4 := Formalism.HC.Frame.A.val_injective _ h3.2
  show Multiplicative.ofAdd ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.art _).1.2),
      Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H.art _).1.1)),
      φ.iotaInv (H.art _).2) =
    Multiplicative.ofAdd ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H'.art _).1.2),
      Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (H'.art _).1.1)),
      φ.iotaInv (H'.art _).2)
  rw [h3.1, h4]

theorem sum_lifts (D : D7) (m : ℕ) (hm : D.R.m = m) (G : ℕ → ℝ) :
    ∑ j ∈ SizeData₂.lifts D, G j = ∑ j : Fin m, G (j.val + 1) := by
  unfold SizeData₂.lifts
  rw [hm, Fin.sum_univ_eq_sum_range (fun j => G (j + 1)) m, Finset.range_eq_Ico,
    Finset.sum_Ico_add' G 0 m 1]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

variable {eps : ℝ} (Fm : FamP eps) (x : ℝ)

def eqTT (i : Fm.Ix x) : (Fm.D x i).host.TT ≃ ↥(Fm.TTn x) :=
  Equiv.ofBijective
    (fun t => ⟨(t : (Fm.D x i).R.A).val, by
      rw [← Fm.TT_eq x i]; exact Finset.mem_image_of_mem _ t.2⟩)
    ⟨fun a b h => Subtype.ext (Formalism.HC.Frame.A.val_injective _ (congrArg Subtype.val h)),
     fun τ => by
      obtain ⟨n, hn⟩ := τ
      have hn' : n ∈ (Fm.D x i).host.TT.image Formalism.HC.Frame.A.val := by rw [Fm.TT_eq x i]; exact hn
      obtain ⟨s, hs, hsn⟩ := Finset.mem_image.mp hn'
      exact ⟨⟨s, hs⟩, Subtype.ext hsn⟩⟩

theorem sum_TT (i : Fm.Ix x) (F : ℕ → ℝ) :
    ∑ t : (Fm.D x i).host.TT, F (t : (Fm.D x i).R.A).val = ∑ τ : ↥(Fm.TTn x), F τ.1 :=
  Equiv.sum_comp (eqTT Fm x i) (fun τ => F τ.1)

theorem card_TT (i : Fm.Ix x) : (Fm.D x i).host.TT.card = Fintype.card ↥(Fm.TTn x) := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (eqTT Fm x i)

theorem TTn_lt (i : Fm.Ix x) {n : ℕ} (hn : n ∈ Fm.TTn x) : n < (Fm.D x i).R.ord := by
  rw [← Fm.TT_eq x i, Finset.mem_image] at hn
  obtain ⟨s, -, rfl⟩ := hn
  exact Formalism.HC.Frame.A.val_lt _

theorem scale_ext (s s' : Scale) (h1 : s.x = s'.x) (h2 : s.eps = s'.eps) (h3 : s.J = s'.J) : s = s' := by
  cases s; cases s'
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3; rfl

variable {x}

theorem sc_eq (hx : Fm.x1 < x) (i i' : Fm.Ix x) : (Fm.L x i).sc = (Fm.L x i').sc :=
  scale_ext _ _ ((Fm.L_x x i hx).trans (Fm.L_x x i' hx).symm) ((Fm.L_eps x i).trans (Fm.L_eps x i').symm)
    ((Fm.L_J x i).trans (Fm.L_J x i').symm)

theorem rdE_eq (i i' : Fm.Ix x) : (Fm.D x i).host.rdE = (Fm.D x i').host.rdE := Fm.rd_eq x i i'

def quadraticLogDerivL (d : ℕ) (hd : d.Prime) (s : ℂ) : ℝ :=
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) s /
    DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) s).re

theorem log_deriv_L_eq_quadratic (D : D7) (s : ℂ) : dlogL D s = quadraticLogDerivL D.host.d D.host.hyp.2.1 s := rfl

theorem quadratic_log_deriv_congr {d d' : ℕ} (h : d = d') (hd : d.Prime) (hd' : d'.Prime) (s : ℂ) :
    quadraticLogDerivL d hd s = quadraticLogDerivL d' hd' s := by
  subst h; rfl

theorem logDerivative_at_one_eq (i i' : Fm.Ix x) : (Fm.L x i).logDerivativeAtOne = (Fm.L x i').logDerivativeAtOne := by
  rw [(Fm.L x i).logDerivative_at_one_eq, (Fm.L x i').logDerivative_at_one_eq, log_deriv_L_eq_quadratic, log_deriv_L_eq_quadratic]
  exact quadratic_log_deriv_congr (Fm.d_eq x i i') _ _ _

theorem La_eq (hx : Fm.x1 < x) (i i' : Fm.Ix x) : (Fm.L x i).La = (Fm.L x i').La := by
  unfold SizeData₂.La
  rw [sc_eq Fm hx i i', rdE_eq Fm i i']

theorem B_zero_shape_eq_index (hx : Fm.x1 < x) (i i' : Fm.Ix x) : (Fm.L x i).B0 = (Fm.L x i').B0 := by
  unfold SizeData₂.B0
  rw [sc_eq Fm hx i i', Fm.R_eq x i i']

theorem Nc_eq (hx : Fm.x1 < x) (i i' : Fm.Ix x) : (Fm.L x i).Nc = (Fm.L x i').Nc := by
  have hT : (Fm.D x i).host.T2.card = (Fm.D x i').host.T2.card := by rw [Fm.realisedChain_torus_eq x i i']
  unfold SizeData₂.Nc
  rw [hT, sc_eq Fm hx i i', Fm.R_eq x i i']

theorem GamL_eq (hx : Fm.x1 < x) (i i' : Fm.Ix x) : GamL (Fm.L x i) = GamL (Fm.L x i') := by
  have hm : ((Fm.D x i).R.m : ℝ) = ((Fm.D x i').R.m : ℝ) := by rw [Fm.R_eq x i i']
  have hf : ((Fm.D x i).R.f : ℝ) = ((Fm.D x i').R.f : ℝ) := by rw [Fm.R_eq x i i']
  unfold GamL
  rw [Fm.CGam_eq x i, Fm.CGam_eq x i', hm, hf, sc_eq Fm hx i i']

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def IOsum : ℝ := ∑ w ∈ L.supp, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * L.io w

def lgG (D : D7) : ℝ := Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

def Count_at (C : ℝ) : Prop :=
  ∀ u, ((∑ j ∈ SizeData₂.lifts D, (1 / (D.R.f : ℝ)) * ∑ τ : D.what₂.Tau, Real.log (wj D j τ * D.host.v / Real.pi)) +
        (D.R.m : ℝ) * lgG D - C * (L.La + (D.R.m : ℝ) ^ 2 * L.La / D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)) ∧
    Real.log ((D.mem u).A.T : ℝ) ≤ C * D.R.m * L.sc.L ∧
    ∀ u', |Real.log ((D.mem u).A.T : ℝ) - Real.log ((D.mem u').A.T : ℝ)| ≤ C * Real.log D.R.k

def SlopesM_at (C : ℝ) : Prop :=
  ∀ u, -(C * D.host.TT.card * L.sc.a * L.La * (1 + (D.R.m : ℝ) / D.R.k)) ≤ ((D.fm u).lat 0).mu ∧
    ((D.fm u).lat 0).muMax ≤ C * D.host.TT.card * L.sc.a * L.La

def LoU (C : ℝ) (u : D.what₂.Word) : ℝ :=
  C * IOsum L + C * D.host.TT.card * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ) +
    C * L.sc.X'' D.R.n + 1

def SlopesN_at (C : ℝ) : Prop :=
  ∀ u, (D.div.Nu u).muMax ≤ ((D.fm u).lat 0).muMax + L.Ga + L.Fo - L.Ee u + C * D.R.m * L.B0 ∧
    ((D.fm u).lat 0).mu + L.Ga + L.Fo - L.Ee u - LoU L C u ≤ (D.div.Nu u).mu

def Lat_at (D : D7) : Prop :=
  (∀ u, 0 < (D.div.Nu u).rank ∧ (D.div.Nu u).mu ≤ (D.div.Nu u).muMax) ∧ D.div.RR.muMinDual = -D.div.RR.muMax

def Frame_at (D : D7) (etaB eB : ℝ) : Prop :=
  ∃ η e : ℝ, 0 ≤ η ∧ η ≤ etaB ∧ 0 ≤ e ∧ e ≤ eB ∧
    ∀ HH : ℝ, sFrame D.div.Nu D.div.h - D.div.RR.muMinDual ≤ HH → 0 < HH →
      sFrame D.div.Nu D.div.h - Real.log (Fintype.card D.what₂.Word : ℝ) -
        (1 - D.what₂.delp)⁻¹ * (4 * uFrame D.div.Nu D.div.h * Real.log (1 + HH / uFrame D.div.Nu D.div.h) +
          (η + 4 * Real.sqrt e) * HH) ≤ D.div.RR.muDual

structure Reads (e : Formalism.HC.Frame) (m : ℕ) (TT : Finset e.A) (a : e.A → ℝ) (w : Fin m → E0 × e.A → ℝ) : Prop where
  he : D.R.toFrame = e
  hm : D.R.m = m
  hTT : ∀ h, h ∈ TT ↔ hval e h ∈ D.host.TT.image Formalism.HC.Frame.A.val
  ha : ∀ (t : D.host.TT) h, hval e h = (t : D.R.A).val → a h = (L.aT t : ℝ)
  hw : ∀ (j : Fin m) (g : E0 × e.A) (τ : D.what₂.Tau),
    gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode e g → w j g = wj D (j.val + 1) τ

def Loss_at (C eL : ℝ) : Prop :=
  IOsum L ≤ C * D.host.TT.card * D.R.m * L.sc.b * L.sc.x ^ (eL * L.sc.eps) ∧
  ∀ (e : Formalism.HC.Frame) (m : ℕ) (AD : ArithData e.A) (N : ℕ) (TT : Finset e.A) (a : e.A → ℝ)
    (w : Fin m → E0 × e.A → ℝ), Reads L e m TT a w → HEq AD (arithOf D.host.toHostRaw) →
    (∀ j t ρ, t ∈ TT → InPhi ρ → a t / w j ρ ≤ N) →
    (∑ t ∈ TT, ∑ j : Fin m, ASK AD N (a t) t (w j)) - L.Ga ≤
      C * D.host.TT.card * D.R.m * L.sc.b * L.sc.x ^ (eL * L.sc.eps)

def Nodes_at : Prop :=
  ∀ (e : Formalism.HC.Frame) (m : ℕ) (T2 : Finset e.A) (u0 : e.A) (w : Fin m → E0 × e.A → ℝ), D.R.toFrame = e → D.R.m = m →
    (∀ h, h ∈ T2 ↔ ∃ s ∈ D.host.T2, h = (e).dig s) → D.host.u0.val = hval e u0 →
    (∀ (j : Fin m) (g : E0 × e.A) (τ : D.what₂.Tau),
      gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode e g → w j g = wj D (j.val + 1) τ) →
    (∀ j g, (¬ ∃ τ : D.what₂.Tau, gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = mcode e g) → w j g = 1) →
    (∀ j ρ, InPhi ρ → 1 ≤ w j ρ) ∧
    (∀ j ρ, IsThickAt T2 u0 ρ → L.sc.b ≤ w j ρ ∧ w j ρ ≤ L.sc.b + L.etaSz + 1) ∧
    (∀ j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w j ρ ≤ 2 * L.sc.b')

def Char_at (x eps c6 C5 : ℝ) : Prop :=
  ∀ (e : Formalism.HC.Frame) (AD : ArithData e.A), D.R.toFrame = e → HEq AD (arithOf D.host.toHostRaw) →
    ∃ ell : AddChar (E0 × e.A) ℂ → ℂ,
      (∀ ψ : AddChar (E0 × e.A) ℂ, ψ ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
        (∀ n : ℕ, n ≠ 0 → χ (n : ZMod N) = primVal AD ψ n) → ell ψ = GlobalTheoryTheory.logDerivativeAtOne χ) ∧
      L.logDerivativeAtOne = (ell chC).re ∧
      (ChThin_at D x eps c6 →
        ThinScales AD ell (Real.exp (x ^ (eps / 3))) (Real.exp (-(c6 * x ^ (eps / 8))))) ∧
      (ChQD_at D x eps C5 → ValuesAtX AD ell x eps C5)

def Win_at (eK c6 : ℝ) : Prop :=
  (D.R.m : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2 + L.sc.eps / 2) ∧ L.sc.x * D.R.m ≤ D.R.k ∧
  (D.R.k : ℝ) ≤ L.sc.x ^ eK ∧ (D.R.k : ℝ) ≤ L.sc.a ∧
  0 ≤ L.La ∧ L.La ≤ 2 * L.sc.x ^ L.sc.eps ∧
  D.R.k * L.sc.b' ≤ L.sc.a ∧ L.sc.X'' D.R.n ≤ L.sc.a ∧
  (∀ t, (L.aT t : ℝ) ≤ 2 * L.sc.a) ∧
  Real.log (Fintype.card D.what₂.Word : ℝ) ≤ ((D.R.k : ℝ) - 3) * Real.log 2 ∧
  2 * (D.R.f : ℝ) * (L.sc.x + 1) * Real.exp (-(c6 * L.sc.x ^ (L.sc.eps / 8))) ≤ 1 / L.sc.x ∧
  6 * (D.R.f : ℝ) * (L.sc.x + 1) * (L.etaSz + 1) ≤ L.sc.b / L.sc.x ∧
  L.sc.x ^ ((1 : ℝ) / 2 - L.sc.eps) ≤ D.R.m ∧
  (D.R.k : ℝ) ≤ (D.R.n : ℝ) ^ 2 * L.sc.x ^ ((1 : ℝ) / 2 - L.sc.eps) ∧
  L.sc.x ^ (-L.sc.eps) ≤ (D.host.T2.card : ℝ) / D.R.n ∧
  (∀ t, |(L.aT t : ℝ) / L.sc.b - L.sc.x| ≤ 1) ∧
  0 < D.host.v

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

def CountF : Prop := ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, Count_at (Fm.L x i) C
def SlopesMF : Prop := ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, SlopesM_at (Fm.L x i) C
def SlopesNF : Prop := ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, SlopesN_at (Fm.L x i) C
def LatF : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Lat_at (Fm.D x i)
def NodesF : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Nodes_at (Fm.L x i)

def FrameF (CH : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∃ etaB eB : ℝ, 0 ≤ etaB ∧ 0 ≤ eB ∧ eB ≤ 1 / 4 ∧
    (etaB + 4 * Real.sqrt eB) * x ^ CH ≤ 6 ∧ ∀ i : Fm.Ix x, Frame_at (Fm.D x i) etaB eB

def LossF (eL : ℝ) : Prop :=
  ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, x ∈ Fm.Win → ∃ (i0 : Fm.Ix x) (av bv : ℕ → ℤ),
    (∀ t ∈ Fm.TTn x, aWin (Fm.L x i0) (av t) ∧ (Fm.L x i0).sc.b' ≤ (bv t : ℝ) ∧ (bv t : ℝ) ≤ Fm.bTop x) ∧
    ∀ i : Fm.Ix x, (∀ t : (Fm.D x i).host.TT,
        (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val) → Loss_at (Fm.L x i) C eL

def CharF : Prop :=
  ∀ c6 C5 : ℝ, ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Char_at (Fm.L x i) x eps c6 C5

def WinF : Prop :=
  ∀ c6 : ℝ, 0 < c6 → ∃ eK x0 : ℝ, 0 ≤ eK ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x, Win_at (Fm.L x i) eK c6

end Family

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

theorem sgnZ_injective : Function.Injective sgnZ := by
  intro s s' h
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl <;>
    simp [sgnZ] at h ⊢

theorem iotaHInv_injective (e : Formalism.HC.Frame) : Function.Injective e.iotaInv := fun a b h => by
  rw [← e.iota_iotaInv a, h, e.iota_iotaInv]

theorem gcode_injective (e : Formalism.HC.Frame) : Function.Injective (gcode e) := by
  intro g g' h
  unfold gcode at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Prod.ext (Prod.ext (sgnZ_injective h2) (sgnZ_injective h1))
    (Formalism.HC.Frame.A.val_injective _ h3)

theorem mcode_injective (e : Formalism.HC.Frame) : Function.Injective (mcode e) := by
  intro g g' h
  unfold mcode at h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (hval_injective e h.2)

theorem card_PhiSet (e : Formalism.HC.Frame) : (PhiSet (H := e.A)).card = 2 * e.ord := by
  have h : PhiSet (H := e.A) =
      (Finset.univ : Finset (ZMod 2 × e.A)).image (fun p => (((0 : ZMod 2), p.1), p.2)) := by
    ext g
    simp only [PhiSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, InPhi]
    constructor
    · intro hg
      exact ⟨(g.1.2, g.2), Prod.ext (Prod.ext hg.symm rfl) rfl⟩
    · rintro ⟨p, rfl⟩
      rfl
  rw [h, Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_prod, ZMod.card, card_HA]
  · intro p p' hp
    simp only [Prod.mk.injEq, true_and] at hp
    exact Prod.ext hp.1 hp.2

def plMap (D : D7) (e : Formalism.HC.Frame) (τ : D.what₂.Tau) : E0 × e.A :=
  ((gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG)).1, hOfNat e (gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG)).2)

theorem mcode_plMap (D : D7) (e : Formalism.HC.Frame) (he : D.R.toFrame = e) (τ : D.what₂.Tau) :
    mcode e (plMap D e τ) = gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) := by
  have hlt : (gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG)).2 < e.ord := by
    rw [← he]; exact Formalism.HC.Frame.A.val_lt _
  unfold mcode plMap
  exact Prod.ext rfl (hval_hOfNat e _ hlt)

theorem plMap_injective (D : D7) (e : Formalism.HC.Frame) (he : D.R.toFrame = e) : Function.Injective (plMap D e) := by
  intro τ τ' h
  have h1 : gcode _ ((D.eTau τ : D.R.Psi) : D.R.GG) = gcode _ ((D.eTau τ' : D.R.Psi) : D.R.GG) := by
    rw [← mcode_plMap D e he τ, h, mcode_plMap D e he τ']
  exact D.eTau.injective (Subtype.ext (gcode_injective _ h1))

theorem plMap_mem (D : D7) (e : Formalism.HC.Frame) (τ : D.what₂.Tau) : plMap D e τ ∈ PhiSet (H := e.A) := by
  simp only [PhiSet, Finset.mem_filter, Finset.mem_univ, true_and, InPhi, plMap, gcode]
  have h := (Formalism.HC.Frame.mem_Psi_iff _).mp (D.eTau τ).2
  rw [h]; simp [sgnZ]

theorem card_Tau (D : D7) : Fintype.card D.what₂.Tau = D.R.f := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr D.eTau]
  exact (factCardPsi D.R D.host).1

theorem image_plMap (D : D7) (e : Formalism.HC.Frame) (he : D.R.toFrame = e) :
    (Finset.univ : Finset D.what₂.Tau).image (plMap D e) = PhiSet (H := e.A) := by
  apply Finset.eq_of_subset_of_card_le
  · intro g hg
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.mp hg
    exact plMap_mem D e τ
  · rw [Finset.card_image_of_injective _ (plMap_injective D e he), Finset.card_univ, card_Tau, card_PhiSet,
      ← he]
    exact le_of_eq rfl

theorem sum_PhiSet (D : D7) (e : Formalism.HC.Frame) (he : D.R.toFrame = e) (G : E0 × e.A → ℝ) :
    ∑ g ∈ PhiSet (H := e.A), G g = ∑ τ : D.what₂.Tau, G (plMap D e τ) := by
  rw [← image_plMap D e he, Finset.sum_image (fun a _ b _ h => plMap_injective D e he h)]

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ}

structure Mod (Fm : FamP eps) (x : ℝ) where
  i0 : Fm.Ix x
  av : ℕ → ℤ
  bv : ℕ → ℤ
  pt : (Fm.D x i0).R.A → Fm.Ix x
  point_base_value : ∀ u0, (Fm.D x (pt u0)).host.u0.val = hval _ u0
  pt_w : ∀ u0 (t : (Fm.D x (pt u0)).host.TT),
    (Fm.L x (pt u0)).aT t = av (t : (Fm.D x (pt u0)).R.A).val ∧
    (Fm.L x (pt u0)).bT t = bv (t : (Fm.D x (pt u0)).R.A).val

namespace Mod

variable (M : Mod Fm x)

abbrev e : Formalism.HC.Frame := (Fm.D x M.i0).R.toFrame
abbrev m : ℕ := (Fm.D x M.i0).R.m
abbrev f : ℕ := (Fm.D x M.i0).R.f
abbrev q : ℕ := (Fm.D x M.i0).host.q
abbrev d : ℕ := (Fm.D x M.i0).host.d
abbrev AD : ArithData M.e.A := arithOf (Fm.D x M.i0).host.toHostRaw

instance : Fact M.q.Prime := ⟨(Fm.D x M.i0).host.hyp.1⟩
instance : Fact M.d.Prime := ⟨(Fm.D x M.i0).host.hyp.2.1⟩

theorem he (u0 : M.e.A) : (Fm.D x (M.pt u0)).R.toFrame = M.e := congrArg Ranks.toFrame (Fm.R_eq x (M.pt u0) M.i0)
theorem hm (u0 : M.e.A) : (Fm.D x (M.pt u0)).R.m = M.m := congrArg Ranks.m (Fm.R_eq x (M.pt u0) M.i0)
theorem hf (u0 : M.e.A) : (Fm.D x (M.pt u0)).R.f = M.f := congrArg Ranks.f (Fm.R_eq x (M.pt u0) M.i0)

theorem hAD (u0 : M.e.A) : HEq M.AD (arithOf (Fm.D x (M.pt u0)).host.toHostRaw) :=
  arithOf_heq _ _ (M.he u0).symm (Fm.q_eq x _ _) (Fm.d_eq x _ _) (Fm.QS_eq x _ _) (Fm.art_eq x _ _)

open Classical in

def w (u0 : M.e.A) (j : Fin M.m) (g : E0 × M.e.A) : ℝ :=
  if h : ∃ τ : (Fm.D x (M.pt u0)).what₂.Tau,
      gcode _ (((Fm.D x (M.pt u0)).eTau τ : (Fm.D x (M.pt u0)).R.Psi) : (Fm.D x (M.pt u0)).R.GG) = mcode M.e g
  then wj (Fm.D x (M.pt u0)) (j.val + 1) h.choose else 1

theorem w_tie (u0 : M.e.A) (j : Fin M.m) (g : E0 × M.e.A) (τ : (Fm.D x (M.pt u0)).what₂.Tau)
    (h : gcode _ (((Fm.D x (M.pt u0)).eTau τ : (Fm.D x (M.pt u0)).R.Psi) : (Fm.D x (M.pt u0)).R.GG) = mcode M.e g) :
    M.w u0 j g = wj (Fm.D x (M.pt u0)) (j.val + 1) τ := by
  have hex : ∃ τ : (Fm.D x (M.pt u0)).what₂.Tau,
      gcode _ (((Fm.D x (M.pt u0)).eTau τ : (Fm.D x (M.pt u0)).R.Psi) : (Fm.D x (M.pt u0)).R.GG) = mcode M.e g :=
    ⟨τ, h⟩
  have hc : hex.choose = τ :=
    (Fm.D x (M.pt u0)).eTau.injective (Subtype.ext (gcode_injective _ (hex.choose_spec.trans h.symm)))
  unfold w
  rw [dif_pos hex, hc]

theorem w_off (u0 : M.e.A) (j : Fin M.m) (g : E0 × M.e.A)
    (h : ¬ ∃ τ : (Fm.D x (M.pt u0)).what₂.Tau,
      gcode _ (((Fm.D x (M.pt u0)).eTau τ : (Fm.D x (M.pt u0)).R.Psi) : (Fm.D x (M.pt u0)).R.GG) = mcode M.e g) :
    M.w u0 j g = 1 := by
  unfold w
  rw [dif_neg h]

theorem w_plMap (u0 : M.e.A) (j : Fin M.m) (τ : (Fm.D x (M.pt u0)).what₂.Tau) :
    M.w u0 j (plMap (Fm.D x (M.pt u0)) M.e τ) = wj (Fm.D x (M.pt u0)) (j.val + 1) τ :=
  M.w_tie u0 j _ τ (mcode_plMap _ _ (M.he u0) τ).symm

def TT : Finset M.e.A := Finset.univ.filter (fun h => hval M.e h ∈ Fm.TTn x)
def T2 : Finset M.e.A := (Fm.D x M.i0).host.T2.image M.e.dig
def a (h : M.e.A) : ℝ := (M.av (hval M.e h) : ℝ)

theorem mem_TT (h : M.e.A) : h ∈ M.TT ↔ hval M.e h ∈ Fm.TTn x := by simp [TT]
theorem mem_thick_set_model_iff (h : M.e.A) : h ∈ M.T2 ↔ ∃ s ∈ (Fm.D x M.i0).host.T2, h = M.e.dig s := by
  simp only [T2, Finset.mem_image]
  exact ⟨fun ⟨s, a, b⟩ => ⟨s, a, b.symm⟩, fun ⟨s, a, b⟩ => ⟨s, a, b.symm⟩⟩

def eT : ↥(Fm.TTn x) ≃ ↥M.TT where
  toFun τ := ⟨hOfNat M.e τ.1, by
    rw [mem_TT, hval_hOfNat _ _ (TTn_lt Fm x M.i0 τ.2)]; exact τ.2⟩
  invFun h := ⟨hval M.e h.1, (M.mem_TT h.1).mp h.2⟩
  left_inv τ := Subtype.ext (hval_hOfNat _ _ (TTn_lt Fm x M.i0 τ.2))
  right_inv h := Subtype.ext (hOfNat_hval _ _)

def eP : Fin M.f ≃ ↥(PhiSet (H := M.e.A)) :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, card_PhiSet]; rfl)).symm

theorem card_TT' : M.TT.card = Fintype.card ↥(Fm.TTn x) := by
  rw [← Fintype.card_coe]; exact (Fintype.card_congr M.eT).symm

theorem card_thick_set_model_eq : M.T2.card = (Fm.D x M.i0).host.T2.card := by
  have hlt : ∀ s ∈ (Fm.D x M.i0).host.T2, s < M.e.n0 := by
    intro s hs
    have h1 := (Fm.D x M.i0).host.second_set_range s hs
    have h2 := (Fm.D x M.i0).host.two_le_Lw
    have h3 : s ≤ 4 * (Fm.D x M.i0).host.Lw * s := Nat.le_mul_of_pos_left s (by omega)
    exact lt_of_le_of_lt h3 h1
  exact Finset.card_image_of_injOn (fun a ha b hb hab => M.e.dig_inj (hlt a ha) (hlt b hb) hab)

theorem sum_places (u0 : M.e.A) (j : Fin M.m) (F : ℝ → ℝ) :
    ∑ ρ : Fin M.f, F (M.w u0 j (M.eP ρ).1) = ∑ τ : (Fm.D x (M.pt u0)).what₂.Tau, F (wj (Fm.D x (M.pt u0)) (j.val + 1) τ) := by
  rw [Equiv.sum_comp M.eP (fun g => F (M.w u0 j g.1)), Finset.sum_coe_sort (PhiSet (H := M.e.A)) (fun g => F (M.w u0 j g)),
    sum_PhiSet (Fm.D x (M.pt u0)) M.e (M.he u0)]
  exact Finset.sum_congr rfl (fun τ _ => by rw [M.w_plMap u0 j τ])

def data (N : ℕ) (CH etaB eB : ℝ) (ηv ev : M.e.A → ℝ) :
    Data M.e.A (fun u0 => (Fm.D x (M.pt u0)).what₂.Word) ↥(Fm.TTn x) M.m M.f where
  x := x
  ε := eps
  a := (Fm.L x M.i0).sc.a
  b := (Fm.L x M.i0).sc.b
  b' := (Fm.L x M.i0).sc.b'
  k := ((Fm.D x M.i0).R.k : ℝ)
  L := (Fm.L x M.i0).sc.L
  La := (Fm.L x M.i0).La
  B0 := (Fm.L x M.i0).B0
  Nc := (Fm.L x M.i0).Nc
  gam := Real.eulerMascheroniConstant
  LpL := (Fm.L x M.i0).logDerivativeAtOne
  v := (Fm.D x M.i0).host.v
  lg := lgG (Fm.D x M.i0)
  logGam := Real.log (GamL (Fm.L x M.i0))
  aT τ := (M.av τ.1 : ℝ)
  w u0 j ρ := M.w u0 j (M.eP ρ).1
  d u0 u := (((Fm.D x (M.pt u0)).div.Nu u).rank : ℝ)
  T u0 u := (((Fm.D x (M.pt u0)).mem u).A.T : ℝ)
  muN u0 u := ((Fm.D x (M.pt u0)).div.Nu u).mu
  muMaxN u0 u := ((Fm.D x (M.pt u0)).div.Nu u).muMax
  h u0 u := (Fm.D x (M.pt u0)).div.h u
  muM u0 u := (((Fm.D x (M.pt u0)).fm u).lat 0).mu
  muMaxM u0 u := (((Fm.D x (M.pt u0)).fm u).lat 0).muMax
  EeJ u0 u j := ∑ w ∈ (Fm.L x (M.pt u0)).supp, SizeData₂.sz w ((Fm.L x (M.pt u0)).E u (j.val + 1) w)
  muCC u0 := (Fm.D x (M.pt u0)).div.RR.muDual
  muMinCC u0 := (Fm.D x (M.pt u0)).div.RR.muMinDual
  Fo u0 := (Fm.L x (M.pt u0)).Fo
  Ga u0 := (Fm.L x (M.pt u0)).Ga
  Ta u0 := ∑ w ∈ (Fm.L x (M.pt u0)).supp, SizeData₂.sz w ((Fm.L x (M.pt u0)).tau w)
  ASK u0 := ∑ t ∈ M.TT, ∑ j : Fin M.m, ASK M.AD N (M.a t) t (M.w u0 j)
  IO u0 := IOsum (Fm.L x (M.pt u0))
  HH _ := x ^ CH * (Fm.L x M.i0).sc.b
  del u0 := (Fm.D x (M.pt u0)).what₂.delp
  η := ηv
  e := ev
  delBar := Real.exp (-(x ^ (Fm.ez / 7)))
  etaBar := etaB
  eBar := eB

end Mod

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ}

namespace Mod

variable (M : Mod Fm x) (hx : Fm.x1 < x) (u0 : M.e.A)

include hx in
theorem s_sc : (Fm.L x (M.pt u0)).sc = (Fm.L x M.i0).sc := sc_eq Fm hx _ _
include hx in
theorem s_x : (Fm.L x M.i0).sc.x = x := Fm.L_x x M.i0 hx
theorem s_eps : (Fm.L x M.i0).sc.eps = eps := Fm.L_eps x M.i0
theorem s_m : ((Fm.D x (M.pt u0)).R.m : ℝ) = (M.m : ℝ) := congrArg Nat.cast (M.hm u0)
theorem s_f : ((Fm.D x (M.pt u0)).R.f : ℝ) = (M.f : ℝ) := congrArg Nat.cast (M.hf u0)
theorem s_k : ((Fm.D x (M.pt u0)).R.k : ℝ) = ((Fm.D x M.i0).R.k : ℝ) :=
  congrArg (fun R : Ranks => (R.k : ℝ)) (Fm.R_eq x (M.pt u0) M.i0)
theorem s_n : (Fm.D x (M.pt u0)).R.n = (Fm.D x M.i0).R.n := congrArg Ranks.n (Fm.R_eq x (M.pt u0) M.i0)
include hx in
theorem s_La : (Fm.L x (M.pt u0)).La = (Fm.L x M.i0).La := La_eq Fm hx _ _
include hx in
theorem point_base_constants_eq : (Fm.L x (M.pt u0)).B0 = (Fm.L x M.i0).B0 := B_zero_shape_eq_index Fm hx _ _
include hx in
theorem s_Nc : (Fm.L x (M.pt u0)).Nc = (Fm.L x M.i0).Nc := Nc_eq Fm hx _ _
theorem s_dl : (Fm.L x (M.pt u0)).logDerivativeAtOne = (Fm.L x M.i0).logDerivativeAtOne := logDerivative_at_one_eq Fm _ _
theorem s_v : (Fm.D x (M.pt u0)).host.v = (Fm.D x M.i0).host.v := by
  unfold Host.v; rw [rdE_eq Fm (M.pt u0) M.i0]
theorem s_lg : lgG (Fm.D x (M.pt u0)) = lgG (Fm.D x M.i0) := by
  unfold lgG; rw [Fm.g_eq x (M.pt u0) M.i0]
theorem s_card : ((Fm.D x (M.pt u0)).host.TT.card : ℝ) = (Fintype.card ↥(Fm.TTn x) : ℝ) :=
  congrArg Nat.cast (card_TT Fm x (M.pt u0))

theorem sum_aT (F : ℝ → ℝ) :
    ∑ t : (Fm.D x (M.pt u0)).host.TT, F ((Fm.L x (M.pt u0)).aT t : ℝ) = ∑ τ : ↥(Fm.TTn x), F (M.av τ.1 : ℝ) := by
  rw [← sum_TT Fm x (M.pt u0) (fun n => F (M.av n : ℝ))]
  exact Finset.sum_congr rfl (fun t _ => by rw [(M.pt_w u0 t).1])

variable (N : ℕ) (CH etaB eB : ℝ) (ηv ev : M.e.A → ℝ)

theorem logOm_eq : (Fm.L x (M.pt u0)).logOm = (M.data N CH etaB eB ηv ev).logOm := by
  unfold SizeData₂.logOm Data.logOm
  rw [M.s_v u0, M.s_dl u0]
  rfl

theorem main_eq (u : (Fm.D x (M.pt u0)).what₂.Word) :
    (Fm.L x (M.pt u0)).MAIN u = ∑ τ : ↥(Fm.TTn x), ((M.m : ℝ) * (ph (M.av τ.1 : ℝ) -
      (M.av τ.1 : ℝ) * (M.data N CH etaB eB ηv ev).logOm) -
      (M.av τ.1 : ℝ) * Real.log (((Fm.D x (M.pt u0)).mem u).A.T : ℝ)) := by
  unfold SizeData₂.MAIN
  rw [M.s_m u0, M.logOm_eq u0 N CH etaB eB ηv ev]
  exact M.sum_aT u0 (fun y => (M.m : ℝ) * (ph y - y * (M.data N CH etaB eB ηv ev).logOm) -
      y * Real.log (((Fm.D x (M.pt u0)).mem u).A.T : ℝ))

theorem sumA_eq : ∑ t : (Fm.D x (M.pt u0)).host.TT, ((Fm.L x (M.pt u0)).aT t : ℝ) =
    (M.data N CH etaB eB ηv ev).sumA := M.sum_aT u0 (fun y => y)

theorem mem_lifts (j : Fin M.m) : j.val + 1 ∈ SizeData₂.lifts (Fm.D x (M.pt u0)) := by
  unfold SizeData₂.lifts
  rw [M.hm u0, Finset.mem_Icc]
  have := j.isLt
  omega

include hx in
theorem data_DIV (C : Consts)
    (h : ∀ u0 : M.e.A, ∀ u, (Fm.D x (M.pt u0)).div.RR.muDual + (Fm.D x (M.pt u0)).div.h u - (Fm.L x (M.pt u0)).Fo ≤
      (Fm.L x (M.pt u0)).MAIN u +
      C.cDiv * ((Fm.D x (M.pt u0)).host.TT.card : ℝ) * (Fm.L x (M.pt u0)).sc.a * (Fm.L x (M.pt u0)).La +
      C.cDiv * ((Fm.D x (M.pt u0)).R.m : ℝ) * ((Fm.L x (M.pt u0)).B0 + (Fm.L x (M.pt u0)).Nc) *
        (Fm.L x (M.pt u0)).sc.x ^ (C.eDiv * (Fm.L x (M.pt u0)).sc.eps)) :
    (M.data N CH etaB eB ηv ev).DIV C := by
  intro u0 u
  have h1 := h u0 u
  rw [M.main_eq u0 N CH etaB eB ηv ev u, M.s_card u0, M.s_sc hx u0, M.s_La hx u0, M.s_m u0, M.point_base_constants_eq hx u0,
    M.s_Nc hx u0, M.s_x hx, M.s_eps] at h1
  exact h1

include hx in
theorem data_EComp5 (C : Consts)
    (h : ∀ u0 : M.e.A, ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x (M.pt u0)),
      |(∑ w ∈ (Fm.L x (M.pt u0)).supp, SizeData₂.sz w ((Fm.L x (M.pt u0)).E u j w)) -
        (∑ t : (Fm.D x (M.pt u0)).host.TT, ((Fm.L x (M.pt u0)).aT t : ℝ)) * lgG (Fm.D x (M.pt u0))| ≤
        C.cE * (Fm.L x (M.pt u0)).B0) :
    EComp5 (M.data N CH etaB eB ηv ev) C := by
  intro u0 u
  have h1 : ∀ j : Fin M.m, |(M.data N CH etaB eB ηv ev).EeJ u0 u j -
      (M.data N CH etaB eB ηv ev).sumA * (M.data N CH etaB eB ηv ev).lg| ≤
      C.cE * (M.data N CH etaB eB ηv ev).B0 := by
    intro j
    have h2 := h u0 u (j.val + 1) (M.mem_lifts u0 j)
    rw [M.sumA_eq u0 N CH etaB eB ηv ev, M.s_lg u0, M.point_base_constants_eq hx u0] at h2
    exact h2
  have h3 : (M.data N CH etaB eB ηv ev).Ee u0 u - (M.m : ℝ) * (M.data N CH etaB eB ηv ev).sumA *
      (M.data N CH etaB eB ηv ev).lg = ∑ j : Fin M.m, ((M.data N CH etaB eB ηv ev).EeJ u0 u j -
      (M.data N CH etaB eB ηv ev).sumA * (M.data N CH etaB eB ηv ev).lg) := by
    unfold Data.Ee
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h3]
  calc |∑ j : Fin M.m, ((M.data N CH etaB eB ηv ev).EeJ u0 u j -
      (M.data N CH etaB eB ηv ev).sumA * (M.data N CH etaB eB ηv ev).lg)|
      ≤ ∑ j : Fin M.m, |(M.data N CH etaB eB ηv ev).EeJ u0 u j -
      (M.data N CH etaB eB ηv ev).sumA * (M.data N CH etaB eB ηv ev).lg| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin M.m, C.cE * (M.data N CH etaB eB ηv ev).B0 := Finset.sum_le_sum (fun j _ => h1 j)
    _ = C.cE * (M.m : ℝ) * (M.data N CH etaB eB ηv ev).B0 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

include hx in
theorem data_HComp (C : Consts)
    (h : ∀ u0 : M.e.A, ∀ u u',
      |((Fm.D x (M.pt u0)).div.h u + (∑ t : (Fm.D x (M.pt u0)).host.TT, ((Fm.L x (M.pt u0)).aT t : ℝ)) *
          Real.log (((Fm.D x (M.pt u0)).mem u).A.T : ℝ)) -
        ((Fm.D x (M.pt u0)).div.h u' + (∑ t : (Fm.D x (M.pt u0)).host.TT, ((Fm.L x (M.pt u0)).aT t : ℝ)) *
          Real.log (((Fm.D x (M.pt u0)).mem u').A.T : ℝ))| ≤
      C.cH * (((Fm.D x (M.pt u0)).host.TT.card : ℝ) * (Fm.L x (M.pt u0)).sc.a * (Fm.L x (M.pt u0)).La +
        ((Fm.D x (M.pt u0)).R.m : ℝ) * (Fm.L x (M.pt u0)).B0)) :
    (M.data N CH etaB eB ηv ev).HComp C := by
  intro u0 u u'
  have h1 := h u0 u u'
  rw [M.sumA_eq u0 N CH etaB eB ηv ev, M.s_card u0, M.s_sc hx u0, M.s_La hx u0, M.s_m u0, M.point_base_constants_eq hx u0] at h1
  unfold Data.sumA at h1
  rw [Finset.sum_mul, Finset.sum_mul] at h1
  exact h1

include hx in
theorem data_Count5 (C : Consts) (h : ∀ u0 : M.e.A, Count_at (Fm.L x (M.pt u0)) C.cCount) :
    Count5 (M.data N CH etaB eB ηv ev) C := by
  intro u0 u
  obtain ⟨h1, h2, h3⟩ := h u0 u
  have hs : (∑ j ∈ SizeData₂.lifts (Fm.D x (M.pt u0)), (1 / ((Fm.D x (M.pt u0)).R.f : ℝ)) *
      ∑ τ : (Fm.D x (M.pt u0)).what₂.Tau,
        Real.log (wj (Fm.D x (M.pt u0)) j τ * (Fm.D x (M.pt u0)).host.v / Real.pi)) =
      ∑ j : Fin M.m, (1 / (M.f : ℝ)) * ∑ ρ : Fin M.f,
        Real.log ((M.data N CH etaB eB ηv ev).w u0 j ρ * (M.data N CH etaB eB ηv ev).v / Real.pi) := by
    rw [sum_lifts (Fm.D x (M.pt u0)) M.m (M.hm u0), M.s_f u0, M.s_v u0]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (M.sum_places u0 j (fun y => Real.log (y * (Fm.D x M.i0).host.v / Real.pi))).symm
  rw [hs, M.s_m u0, M.s_lg u0, M.s_La hx u0, M.s_k u0] at h1
  rw [M.s_m u0, M.s_sc hx u0] at h2
  refine ⟨h1, h2, fun u' => ?_⟩
  have h4 := h3 u'
  rw [M.s_k u0] at h4
  exact h4

include hx in
theorem data_Slopes (C : Consts) (h : ∀ u0 : M.e.A, SlopesM_at (Fm.L x (M.pt u0)) C.cSlope) :
    (M.data N CH etaB eB ηv ev).Slopes C := by
  intro u0 u
  obtain ⟨h1, h2⟩ := h u0 u
  rw [M.s_card u0, M.s_sc hx u0, M.s_La hx u0, M.s_m u0, M.s_k u0] at h1
  rw [M.s_card u0, M.s_sc hx u0, M.s_La hx u0] at h2
  exact ⟨h1, h2⟩

theorem Ee_eq (u : (Fm.D x (M.pt u0)).what₂.Word) :
    (Fm.L x (M.pt u0)).Ee u = (M.data N CH etaB eB ηv ev).Ee u0 u := by
  unfold SizeData₂.Ee Data.Ee
  exact sum_lifts (Fm.D x (M.pt u0)) M.m (M.hm u0)
    (fun j => ∑ w ∈ (Fm.L x (M.pt u0)).supp, SizeData₂.sz w ((Fm.L x (M.pt u0)).E u j w))

include hx in
theorem model_slopes_five (C : Consts) (h : ∀ u0 : M.e.A, SlopesN_at (Fm.L x (M.pt u0)) C.cSl1) :
    QuotientSlopeBoundsWith (M.data N CH etaB eB ηv ev) C ((Fm.L x M.i0).sc.X'' (Fm.D x M.i0).R.n) := by
  intro u0 u
  obtain ⟨h1, h2⟩ := h u0 u
  unfold LoU at h2
  rw [M.Ee_eq u0 N CH etaB eB ηv ev u, M.s_m u0, M.point_base_constants_eq hx u0] at h1
  rw [M.Ee_eq u0 N CH etaB eB ηv ev u, M.s_card u0, M.s_m u0, M.s_sc hx u0, M.s_k u0, M.s_n u0] at h2
  exact ⟨h1, h2⟩

theorem s_eq : (M.data N CH etaB eB ηv ev).s u0 =
    sFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h := by
  unfold Data.s wmean sFrame Rsum dU
  rw [Nat.cast_sum]
  rfl

theorem uF_eq : (M.data N CH etaB eB ηv ev).uF u0 =
    uFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h := by
  unfold Data.uF uFrame
  rw [M.s_eq u0 N CH etaB eB ηv ev]
  rfl

theorem data_SlopeIneq
    (h : ∀ u0 : M.e.A, ∀ HH : ℝ,
      sFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h - (Fm.D x (M.pt u0)).div.RR.muMinDual ≤ HH → 0 < HH →
      sFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h -
          Real.log (Fintype.card (Fm.D x (M.pt u0)).what₂.Word : ℝ) -
        (1 - (Fm.D x (M.pt u0)).what₂.delp)⁻¹ * (4 * uFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h *
            Real.log (1 + HH / uFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h) +
          (ηv u0 + 4 * Real.sqrt (ev u0)) * HH) ≤ (Fm.D x (M.pt u0)).div.RR.muDual) :
    (M.data N CH etaB eB ηv ev).SlopeIneq := by
  intro u0 _ _ _ _ _ h6 h7
  rw [M.s_eq u0 N CH etaB eB ηv ev] at h6 ⊢
  rw [M.uF_eq u0 N CH etaB eB ηv ev]
  exact h u0 _ h6 h7

include hx in
theorem data_HHBound (C : Consts) (hC : C.cHH = CH)
    (h : ∀ u0 : M.e.A, sFrame (Fm.D x (M.pt u0)).div.Nu (Fm.D x (M.pt u0)).div.h + (Fm.D x (M.pt u0)).div.RR.muMax ≤
      (Fm.L x (M.pt u0)).sc.x ^ CH * (Fm.L x (M.pt u0)).sc.b)
    (hd : ∀ u0 : M.e.A, (Fm.D x (M.pt u0)).div.RR.muMinDual = -(Fm.D x (M.pt u0)).div.RR.muMax) :
    (M.data N CH etaB eB ηv ev).HHBound C := by
  intro u0
  have h1 := h u0
  rw [M.s_sc hx u0, M.s_x hx] at h1
  have hx0 : 0 < x := lt_trans (lt_trans one_pos Fm.one_lt_family_threshold) hx
  have hb : 0 < (Fm.L x M.i0).sc.b := Real.exp_pos _
  refine ⟨?_, mul_pos (Real.rpow_pos_of_pos hx0 _) hb, ?_⟩
  · rw [M.s_eq u0 N CH etaB eB ηv ev]
    show _ - (Fm.D x (M.pt u0)).div.RR.muMinDual ≤ x ^ CH * (Fm.L x M.i0).sc.b
    rw [hd u0]; linarith
  · rw [hC]; exact le_refl _

end Mod

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

theorem loss_bound_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ L.B0 := by
  have h : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  unfold SizeData₂.B0 sizeBudget bSize
  positivity

theorem Nc_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ L.Nc := by
  have h : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity

theorem sc_a_pos (s : Scale) : 0 < s.a := by
  have h : 0 < s.x := lt_trans one_pos s.one_lt_alt
  unfold Scale.a Scale.b
  positivity

theorem sc_b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.X'
  exact div_pos (sc_a_pos s) (Real.exp_pos _)

theorem up {C C' X : ℝ} (h : C ≤ C') (hX : 0 ≤ X) : C * X ≤ C' * X := mul_le_mul_of_nonneg_right h hX

variable {eps : ℝ} {Fm : FamP eps} {x : ℝ}

namespace Mod

variable (M : Mod Fm x) (hx : Fm.x1 < x)
variable (N : ℕ) (CH etaB eB : ℝ) (ηv ev : M.e.A → ℝ)

theorem tiePts : TiePts Fm x M.e M.m M.f M.q M.d M.pt M.av M.bv := fun u0 =>
  ⟨M.he u0, M.hm u0, M.hf u0, Fm.q_eq x _ _, Fm.d_eq x _ _, M.point_base_value u0, M.pt_w u0⟩

include hx in
theorem tieGlobal : TieGlobal Fm x M.pt (M.data N CH etaB eB ηv ev) ((Fm.L x M.i0).sc.X'' (Fm.D x M.i0).R.n)
    (Fm.L x M.i0).etaSz (Fm.L x M.i0).sc.X' := fun u0 =>
  ⟨(congrArg Scale.a (M.s_sc hx u0)).symm, (congrArg Scale.b (M.s_sc hx u0)).symm,
    (congrArg Scale.b' (M.s_sc hx u0)).symm, (M.s_k u0).symm, (congrArg Scale.L (M.s_sc hx u0)).symm,
    (M.s_La hx u0).symm, (M.point_base_constants_eq hx u0).symm, (M.s_Nc hx u0).symm, rfl, (M.s_dl u0).symm, (M.s_v u0).symm,
    (M.s_lg u0).symm, congrArg Real.log (GamL_eq Fm hx _ _), by rw [M.s_sc hx u0, M.s_n u0],
    Fm.eta_eq x _ _, (congrArg Scale.X' (M.s_sc hx u0)).symm⟩

theorem tieLocal : TieLocal Fm x M.pt (M.data N CH etaB eB ηv ev) := fun _ =>
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tieArith (ell : AddChar (E0 × M.e.A) ℂ → ℂ)
    (hell : ∀ ψ : AddChar (E0 × M.e.A) ℂ, ψ ≠ 0 → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      (∀ n : ℕ, n ≠ 0 → χ (n : ZMod N) = primVal M.AD ψ n) → ell ψ = GlobalTheoryTheory.logDerivativeAtOne χ) :
    TieArith Fm x M.pt M.av M.AD ell M.TT M.T2 M.a M.w :=
  ⟨M.mem_TT, fun u0 h => by rw [M.mem_thick_set_model_iff, Fm.realisedChain_torus_eq x M.i0 (M.pt u0)], fun _ => rfl, M.w_tie, hell⟩

theorem ident (ell : AddChar (E0 × M.e.A) ℂ → ℂ) (hl : (Fm.L x M.i0).logDerivativeAtOne = (ell chC).re) :
    Ident (M.data N CH etaB eB ηv ev) M.AD N ell M.TT M.a M.w M.eT M.eP :=
  ⟨fun τ => by
      show (M.av τ.1 : ℝ) = (M.av (hval M.e (hOfNat M.e τ.1)) : ℝ)
      rw [hval_hOfNat _ _ (TTn_lt Fm x M.i0 τ.2)],
    fun _ _ _ => rfl, rfl, hl, fun _ => rfl⟩

theorem top_of (u0 : M.e.A) {n : ℕ} (hn : n ∈ Fm.TTn x) :
    ∃ t : (Fm.D x (M.pt u0)).host.TT, (t : (Fm.D x (M.pt u0)).R.A).val = n := by
  have hn' : n ∈ (Fm.D x (M.pt u0)).host.TT.image Formalism.HC.Frame.A.val := by rw [Fm.TT_eq]; exact hn
  obtain ⟨s, hs, hsn⟩ := Finset.mem_image.mp hn'
  exact ⟨⟨s, hs⟩, hsn⟩

theorem reads (u0 : M.e.A) : Reads (Fm.L x (M.pt u0)) M.e M.m M.TT M.a (M.w u0) :=
  ⟨M.he u0, M.hm u0, fun h => by rw [M.mem_TT, Fm.TT_eq], fun t h hh => by
    show (M.av (hval M.e h) : ℝ) = _
    rw [hh, (M.pt_w u0 t).1], M.w_tie u0⟩

theorem fPl_eq : fPl M.e.A = (M.f : ℝ) := by
  unfold fPl; rw [card_PhiSet]; rfl

include hx in
theorem av_facts {eK c6 : ℝ} (hW : Win_at (Fm.L x (M.pt 0)) eK c6) {n : ℕ} (hn : n ∈ Fm.TTn x) :
    (Fm.L x M.i0).sc.a ≤ (M.av n : ℝ) ∧ (M.av n : ℝ) ≤ 2 * (Fm.L x M.i0).sc.a ∧
      |(M.av n : ℝ) / (Fm.L x M.i0).sc.b - x| ≤ 1 := by
  obtain ⟨t, ht⟩ := M.top_of 0 hn
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -, -, -, -, h16, -⟩ := hW
  have h1 := ((Fm.L x (M.pt 0)).aT_win t).1
  have h2 := h9 t
  have h3 := h16 t
  rw [(M.pt_w 0 t).1, ht, M.s_sc hx 0] at h1 h2 h3
  rw [M.s_x hx] at h3
  exact ⟨h1, h2, h3⟩

end Mod

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds
  Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

def mkC (Cd Cabs Cc Cs C1 Cl eL CH : ℝ) : Consts := ⟨Cd, Cabs, Cd, Cd, Cc, Cs, C1, Cl, eL, CH⟩

theorem exp_neg_le_half {y : ℝ} (hy : 1 ≤ y) : Real.exp (-y) ≤ 1 / 2 := by
  have h1 : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h4 : (Real.exp 1)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h2
  rw [h3] at h1
  linarith [h1, h4, (by norm_num : (2 : ℝ)⁻¹ = 1 / 2)]

variable {eps : ℝ}

set_option maxHeartbeats 1600000 in

theorem linkGLOBAL_of (Fm : FamP eps) (Cabs CH C0 eL : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 ≤ CH) (heL : 0 ≤ eL)
    (hCount : CountF Fm) (hSM : SlopesMF Fm)
    (hSN : LinkG Fm → LinkMu Fm → SlopesNF Fm)
    (hLat : LinkDIV Fm Cabs CH → LatF Fm)
    (hNodes : NodesF Fm)
    (hFr : ChosenProviso Fm C0 → ChosenCode Fm C0 CH → LinkS Fm C0 → LinkIRR Fm → LinkDIV Fm Cabs CH → FrameF Fm CH)
    (hLoss : ∀ Cb : ℝ, 0 < Cb → ChosenTT Fm → ChosenBad Fm Cb → LinkG Fm → LossF Fm eL)
    (hChar : CharF Fm)
    (hWin : ThickSetEventually Fm → WinF Fm) (hCov : Fm.CoverAll) :
    LinkGLOBAL Fm Cabs CH C0 Cabs eL := by
  intro hCh hIn
  obtain ⟨C5, c6, Cb, hC5, hc6, hCb, cT2, cTT, cBad, ⟨xQD, hQD⟩, ⟨xTh, hTh⟩, cPr, cCo⟩ := hCh
  obtain ⟨lG, lS, lI, lD, lMu⟩ := hIn
  obtain ⟨Cc, xC, hCc, hC⟩ := hCount
  obtain ⟨Cs, xS, hCs, hS⟩ := hSM
  obtain ⟨C1, xN, hC1, hN⟩ := hSN lG lMu
  obtain ⟨xL, hL⟩ := hLat lD
  obtain ⟨xO, hO⟩ := hNodes
  obtain ⟨xF, hF⟩ := hFr cPr cCo lS lI lD
  obtain ⟨Cl, xLo, hCl, hLo⟩ := hLoss Cb hCb cTT cBad lG
  obtain ⟨xCh, hChr⟩ := hChar c6 C5
  obtain ⟨eK, xW, heK, hW⟩ := hWin cT2 c6 hc6
  obtain ⟨xTT, hTT⟩ := cTT
  obtain ⟨xI, hI⟩ := lI
  obtain ⟨Cd, xD, hD⟩ := lD
  have hCd' : (0 : ℝ) ≤ max Cd 0 := le_max_right _ _
  have hCdle : Cd ≤ max Cd 0 := le_max_left _ _
  refine ⟨max Cd 0 + Cc + Cs + C1 + Cl + 6, CH, eK, C5,
    Fm.x1 + 1 + |xQD| + |xTh| + |xC| + |xS| + |xN| + |xL| + |xO| + |xF| + |xLo| + |xCh| + |xW| + |xTT| + |xI| + |xD|,
    fun x hx hxw => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have habs : 0 ≤ |xQD| ∧ 0 ≤ |xTh| ∧ 0 ≤ |xC| ∧ 0 ≤ |xS| ∧ 0 ≤ |xN| ∧ 0 ≤ |xL| ∧ 0 ≤ |xO| ∧ 0 ≤ |xF| ∧ 0 ≤ |xLo| ∧
      0 ≤ |xCh| ∧ 0 ≤ |xW| ∧ 0 ≤ |xTT| ∧ 0 ≤ |xI| ∧ 0 ≤ |xD| :=
    ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _,
      abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _, abs_nonneg _⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ := habs
  have hx1 : Fm.x1 < x := by linarith
  have hxQD : x ≥ xQD := by linarith [le_abs_self xQD]
  have hxTh : x ≥ xTh := by linarith [le_abs_self xTh]
  have hxC : x ≥ xC := by linarith [le_abs_self xC]
  have hxS : x ≥ xS := by linarith [le_abs_self xS]
  have hxN : x ≥ xN := by linarith [le_abs_self xN]
  have hxL : x ≥ xL := by linarith [le_abs_self xL]
  have hxO : x ≥ xO := by linarith [le_abs_self xO]
  have hxF : x ≥ xF := by linarith [le_abs_self xF]
  have hxLo : x ≥ xLo := by linarith [le_abs_self xLo]
  have hxCh : x ≥ xCh := by linarith [le_abs_self xCh]
  have hxW : x ≥ xW := by linarith [le_abs_self xW]
  have hxTT : x ≥ xTT := by linarith [le_abs_self xTT]
  have hxI : x ≥ xI := by linarith [le_abs_self xI]
  have hxD : x ≥ xD := by linarith [le_abs_self xD]
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith

  obtain ⟨i0, av, bv, hadm, hloss⟩ := hLo x hxLo hxw
  have hcov : ∀ u0 : (Fm.D x i0).R.A, ∃ i : Fm.Ix x, (Fm.D x i).host.u0.val = hval _ u0 ∧
      ∀ t : (Fm.D x i).host.TT, (Fm.L x i).aT t = av (t : (Fm.D x i).R.A).val ∧
        (Fm.L x i).bT t = bv (t : (Fm.D x i).R.A).val :=
    fun u0 => hCov x hx1 i0 (hval _ u0) av bv (hval_lt _ u0) hadm
  choose pt hpt1 hpt2 using hcov
  let M : Mod Fm x := ⟨i0, av, bv, pt, hpt1, hpt2⟩
  have iq : Fact M.q.Prime := ⟨(Fm.D x i0).host.hyp.1⟩
  have id : Fact M.d.Prime := ⟨(Fm.D x i0).host.hyp.2.1⟩

  obtain ⟨etaB, eB, hη0, he0, he4, h6, hFa⟩ := hF x hxF
  have hFa' : ∀ u0 : M.e.A, Frame_at (Fm.D x (M.pt u0)) etaB eB := fun u0 => hFa (M.pt u0)
  unfold Frame_at at hFa'
  choose ηv ev hηv0 hηvB hev0 hevB hfr using hFa'

  obtain ⟨ell, hell1, hell2, hell3, hell4⟩ := hChr x hxCh i0 M.e M.AD rfl HEq.rfl

  have heps : 0 < eps := by have h := (Fm.L x i0).sc.eps_pos; rwa [Fm.L_eps] at h
  have hez : 0 < Fm.ez := div_pos heps (lt_of_lt_of_le one_pos Fm.one_le_J)
  have heps1 : eps ≤ 1 := by have h := (Fm.L x i0).sc.eps_lt; rw [Fm.L_eps] at h; linarith
  have hsx : (Fm.L x i0).sc.x = x := Fm.L_x x i0 hx1
  have hse : (Fm.L x i0).sc.eps = eps := Fm.L_eps x i0
  have hWu : ∀ u0 : M.e.A, Win_at (Fm.L x (M.pt u0)) eK c6 := fun u0 => hW x hxW (M.pt u0)
  have hW0 := hW x hxW i0
  unfold Win_at at hW0
  rw [hsx, hse] at hW0
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, -, -, w11, w12, w13, w14, w15, -, w17⟩ := hW0
  have ha0 := sc_a_pos (Fm.L x i0).sc
  have hb'0 := sc_b'_pos (Fm.L x i0).sc
  have hb0 : 0 < (Fm.L x i0).sc.b := Real.exp_pos _
  have hab : (Fm.L x i0).sc.a = x * (Fm.L x i0).sc.b := by
    show (Fm.L x i0).sc.x * (Fm.L x i0).sc.b = _
    rw [hsx]
  have hLx : (Fm.L x i0).sc.L = x ^ eps := by
    show (Fm.L x i0).sc.x ^ (Fm.L x i0).sc.eps = _
    rw [hsx, hse]
  have hxe : 1 ≤ x ^ eps := Real.one_le_rpow hx1' heps.le
  have hb1 : 1 ≤ (Fm.L x i0).sc.b := by
    show 1 ≤ Real.exp (Fm.L x i0).sc.L
    rw [hLx]; exact Real.one_le_exp (by linarith)
  have hk5 := (Fm.D x i0).R.k_ge
  have hk1 : (1 : ℝ) ≤ ((Fm.D x i0).R.k : ℝ) := by exact_mod_cast (by omega : 1 ≤ (Fm.D x i0).R.k)
  have hnod := fun u0 : M.e.A => hO x hxO (M.pt u0) M.e M.m M.T2 u0 (M.w u0) (M.he u0) (M.hm u0)
    (fun h => by rw [M.mem_thick_set_model_iff, Fm.realisedChain_torus_eq x M.i0 (M.pt u0)]) (M.point_base_value u0) (M.w_tie u0) (M.w_off u0)
  have hcut : ∀ (u0 : M.e.A) (j : Fin M.m) (t : M.e.A) (ρ : E0 × M.e.A), t ∈ M.TT → InPhi ρ →
      M.a t / M.w u0 j ρ ≤ (⌈2 * (Fm.L x i0).sc.a⌉₊ : ℝ) := by
    intro u0 j t ρ ht hρ
    obtain ⟨ha1, ha2, -⟩ := M.av_facts hx1 (hWu 0) ((M.mem_TT t).mp ht)
    have hw1 := (hnod u0).1 j ρ hρ
    have hat : 0 ≤ M.a t := le_trans ha0.le ha1
    calc M.a t / M.w u0 j ρ ≤ M.a t := div_le_self hat hw1
      _ ≤ 2 * (Fm.L x i0).sc.a := ha2
      _ ≤ _ := Nat.le_ceil _
  have hDu := fun u0 : M.e.A => hD x hxD (M.pt u0)
  have hLau : ∀ u0 : M.e.A, 0 ≤ (Fm.L x (M.pt u0)).La := fun u0 => (hWu u0).2.2.2.2.1
  have hnT : (1 : ℝ) ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) := by
    have h1 := (hTT x hxTT i0).1
    have hd : 0 < (Fm.L x i0).sc.delta1 := by
      unfold Scale.delta1; rw [hsx]; exact Real.rpow_pos_of_pos hx0 _
    have hn : (0 : ℝ) < ((Fm.D x i0).R.n : ℝ) := by
      have : 0 < (Fm.D x i0).R.n := (Fm.D x i0).R.toFrame.ord_pos
      exact_mod_cast this
    have h2 : (0 : ℝ) < ((Fm.D x i0).host.TT.card : ℝ) := lt_of_lt_of_le (by positivity) h1
    rw [card_TT Fm x i0] at h2
    exact_mod_cast Nat.succ_le_of_lt (Nat.cast_pos.mp h2)
  have hXpp0 : 0 ≤ (Fm.L x i0).sc.X'' (Fm.D x i0).R.n := by
    unfold Scale.X'' Scale.w''
    exact div_nonneg ha0.le (div_nonneg hb'0.le (mul_nonneg (by rw [hsx]; exact hx0.le) (Nat.cast_nonneg _)))
  have hX' : (Fm.L x i0).sc.X' = Real.exp (x ^ (eps / 3)) := by
    show Real.exp ((Fm.L x i0).sc.x ^ ((Fm.L x i0).sc.eps / 3)) = _
    rw [hsx, hse]

  have L1 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HidaSetting (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    ⟨hx0, hb0, ha0.le, hb'0.le, lt_of_lt_of_le one_pos hk1, w17, Nat.mul_pos two_pos (Fm.D x i0).R.toFrame.ord_pos,
      fun τ => le_trans ha0.le (M.av_facts hx1 (hWu 0) τ.2).1,
      fun u0 j ρ => lt_of_lt_of_le one_pos ((hnod u0).1 j _ (Finset.mem_filter.mp (M.eP ρ).2).2),
      fun u0 u => Nat.cast_pos.mpr ((hL x hxL (M.pt u0)).1 u).1,
      fun u0 u => Nat.cast_pos.mpr ((Fm.D x (M.pt u0)).mem u).A.T_prime.pos,
      fun u0 u => ((hL x hxL (M.pt u0)).1 u).2, hC1,
      (by
        have h := Real.exp_lt_exp.mpr (show -(x ^ (Fm.ez / 7)) < 0 by
          have := Real.rpow_pos_of_pos hx0 (Fm.ez / 7); linarith)
        rwa [Real.exp_zero] at h), hη0, he0, he4⟩
  have L2 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).DIV (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    apply M.data_DIV hx1
    intro u0 u
    have h := (hDu u0).2.2.2.2.2.2.1 u
    have hX1 : 0 ≤ ((Fm.D x (M.pt u0)).host.TT.card : ℝ) * ((Fm.L x (M.pt u0)).sc.a * (Fm.L x (M.pt u0)).La) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sc_a_pos _).le (hLau u0))
    have hX2 : 0 ≤ ((Fm.D x (M.pt u0)).R.m : ℝ) * (((Fm.L x (M.pt u0)).B0 + (Fm.L x (M.pt u0)).Nc) *
        (Fm.L x (M.pt u0)).sc.x ^ (Cabs * (Fm.L x (M.pt u0)).sc.eps)) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (add_nonneg (loss_bound_nonneg _) (Nc_nonneg _))
        (Real.rpow_nonneg (lt_trans one_pos (Fm.L x (M.pt u0)).sc.one_lt_alt).le _))
    have e1 := up hCdle hX1
    have e2 := up hCdle hX2
    show _ ≤ _ + max Cd 0 * _ * _ * _ + max Cd 0 * _ * _ * _ ^ (Cabs * _)
    simp only [mul_assoc] at h e1 e2 ⊢
    linarith
  have L3 : EComp5 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    apply M.data_EComp5 hx1
    intro u0 u j hj
    exact le_trans ((hDu u0).2.2.2.2.2.2.2.1 u j hj) (up hCdle (loss_bound_nonneg _))
  have L4 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HComp (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    apply M.data_HComp hx1
    intro u0 u u'
    exact le_trans ((hDu u0).2.2.2.2.2.2.2.2 u u') (up hCdle (add_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sc_a_pos _).le) (hLau u0))
      (mul_nonneg (Nat.cast_nonneg _) (loss_bound_nonneg _))))
  have L5 : Count5 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    M.data_Count5 hx1 _ _ _ _ _ _ _ (fun u0 => hC x hxC (M.pt u0))
  have L6 : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).Slopes (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    M.data_Slopes hx1 _ _ _ _ _ _ _ (fun u0 => hS x hxS (M.pt u0))
  have L7 : QuotientSlopeBoundsWith (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)
      ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) :=
    M.model_slopes_five hx1 _ _ _ _ _ _ _ (fun u0 => hN x hxN (M.pt u0))
  have L8 : LossBounds (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) := by
    intro u0
    obtain ⟨hio, hask⟩ := hloss (M.pt u0) (M.pt_w u0)
    have h1 := hask M.e M.m M.AD ⌈2 * (Fm.L x i0).sc.a⌉₊ M.TT M.a (M.w u0) (M.reads u0) (M.hAD u0) (hcut u0)
    rw [M.s_card u0, M.s_m u0, M.s_sc hx1 u0, M.s_x hx1, M.s_eps] at h1 hio
    exact ⟨h1, hio⟩
  have liftZP_newton : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).SlopeIneq := M.data_SlopeIneq _ _ _ _ _ _ hfr
  have ParameterUpperBound : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).HHBound (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH) :=
    M.data_HHBound hx1 _ _ _ _ _ _ _ rfl (fun u0 => (hDu u0).2.1) (fun u0 => (hL x hxL (M.pt u0)).2)
  have liftZP_unit : (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev).FParams := fun u0 =>
    ⟨(hI x hxI (M.pt u0)).1, (hI x hxI (M.pt u0)).2, hηv0 u0, hηvB u0, hev0 u0, hevB u0⟩

  have hK6 : (6 : ℝ) ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k1 : max Cd 0 ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k2 : Cc ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k3 : Cs ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k4 : C1 ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have k5 : Cl ≤ max Cd 0 + Cc + Cs + C1 + Cl + 6 := by linarith
  have E0 : ErrWindows0 (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)
      ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) eK (max Cd 0 + Cc + Cs + C1 + Cl + 6) :=
    ⟨hx1', heps, heps1, hb1, le_of_eq hab.symm, hnT, w1, w2, heK, hk1, w3, w4, (by show 0 ≤ (Fm.L x i0).sc.L; rw [hLx]; linarith),
      (by show (Fm.L x i0).sc.L ≤ 2 * x ^ eps; rw [hLx]; linarith), w5, w6, hb'0.le, w7, hXpp0, w8,
      fun τ => ⟨le_trans ha0.le (M.av_facts hx1 (hWu 0) τ.2).1, (M.av_facts hx1 (hWu 0) τ.2).2.1⟩,
      loss_bound_nonneg _, Nc_nonneg _,
      fun u0 => by
        have h := (hWu u0).2.2.2.2.2.2.2.2.2.1
        rw [M.s_k u0] at h
        exact h,
      exp_neg_le_half (Real.one_le_rpow hx1' (by positivity : 0 ≤ Fm.ez / 7)), hη0, he0,
      ⟨hCd', k1, hCd', k1, hCd', k1, hCc, k2, hCs, k3, hC1, k4, hCl, k5, hCabs, heL, hCH⟩⟩
  have E1 : ErrWindows (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) (mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH)
      ((Fm.L x i0).sc.X'' (Fm.D x i0).R.n) eK (max Cd 0 + Cc + Cs + C1 + Cl + 6) := by
    refine ⟨E0, ?_⟩
    show (etaB + 4 * Real.sqrt eB) * (x ^ CH * (Fm.L x i0).sc.b) ≤
      (max Cd 0 + Cc + Cs + C1 + Cl + 6) * x ^ eps * ((Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a)
    have s1 : (etaB + 4 * Real.sqrt eB) * (x ^ CH * (Fm.L x i0).sc.b) ≤ 6 * (Fm.L x i0).sc.b := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h6 hb0.le
    have s2 : (Fm.L x i0).sc.b ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a := by
      rw [hab]
      calc (Fm.L x i0).sc.b = 1 * (1 * (Fm.L x i0).sc.b) := by ring
        _ ≤ (Fintype.card ↥(Fm.TTn x) : ℝ) * (x * (Fm.L x i0).sc.b) :=
          mul_le_mul hnT (mul_le_mul_of_nonneg_right hx1' hb0.le) (by linarith) (by linarith)
    have s3 : (6 : ℝ) ≤ (max Cd 0 + Cc + Cs + C1 + Cl + 6) * x ^ eps :=
      calc (6 : ℝ) ≤ (max Cd 0 + Cc + Cs + C1 + Cl + 6) * 1 := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hxe (by linarith)
    calc _ ≤ 6 * (Fm.L x i0).sc.b := s1
      _ ≤ 6 * ((Fintype.card ↥(Fm.TTn x) : ℝ) * (Fm.L x i0).sc.a) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right s3 (by positivity)
  have hcardH : (Fintype.card M.e.A : ℝ) = ((Fm.D x i0).R.n : ℝ) := by rw [card_HA]; rfl
  have B1 : BNBounds (M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev) M.T2 := by
    constructor
    · apply le_of_eq
      show (Fm.L x i0).B0 = (2 * (Fintype.card M.e.A : ℝ)) * (M.m : ℝ) * (Fm.L x i0).sc.b * x ^ eps
      rw [hcardH]
      unfold SizeData₂.B0 sizeBudget bSize Scale.b Scale.L Ranks.f
      rw [hsx, hse]; push_cast; ring
    · apply le_of_eq
      show (Fm.L x i0).Nc = (M.T2.card : ℝ) * ((Fm.D x i0).R.k : ℝ) * (Fm.L x i0).sc.b * x ^ eps /
        ((Fintype.card M.e.A : ℝ) * ((Fintype.card M.e.A : ℝ) * x ^ (-eps)))
      rw [hcardH, M.card_thick_set_model_eq]
      unfold SizeData₂.Nc budgetNc rankBudget bSize Scale.b Scale.L
      rw [hsx, hse]
  have R1 : GrowthInequalityRemainingHyps M.AD ell ⌈2 * (Fm.L x i0).sc.a⌉₊ M.TT M.T2 M.a M.w x eps (Fm.L x i0).sc.b
      (Fm.L x i0).sc.b' (Fm.L x i0).etaSz (Fm.L x i0).sc.X' (Real.exp (-(c6 * x ^ (eps / 8)))) C5 :=
    ⟨⟨(Fm.L x i0).etaSz_pos.le, Real.exp_pos _, hb'0,
      le_of_eq (by rw [← hab]; exact div_mul_cancel₀ _ (Real.exp_pos _).ne'), (Real.exp_pos _).le,
      fun t ht => (M.av_facts hx1 (hWu 0) ((M.mem_TT t).mp ht)).2.2,
      ⟨fun u0 j ρ hρ => lt_of_lt_of_le one_pos ((hnod u0).1 j ρ hρ),
        fun u0 j ρ hρ => by
          have h := (hnod u0).2.1 j ρ hρ
          rw [M.s_sc hx1 u0, Fm.eta_eq x (M.pt u0) M.i0] at h
          exact h,
        fun u0 j ρ hρ hρ' => by
          have h := (hnod u0).2.2 j ρ hρ hρ'
          rw [M.s_sc hx1 u0] at h
          exact h⟩,
      fun u0 j t ρ ht hρ => hcut u0 j t ρ ht hρ⟩,
      by rw [hX']; exact hell3 (hTh x hxTh i0), hell4 (hQD x hxQD i0)⟩
  have W1 : CostWindows x (fPl M.e.A) (Fm.L x i0).sc.b (Fm.L x i0).etaSz (Real.exp (-(c6 * x ^ (eps / 8)))) := by
    rw [M.fPl_eq]; exact ⟨w11, w12⟩
  have S1 : RestSize eps x (Fintype.card M.e.A) M.TT.card M.T2.card M.m (Fm.L x i0).sc.b
      ((Fm.D x i0).R.k : ℝ) (Fm.L x i0).sc.a := by
    have h1 := (hTT x hxTT i0).1
    unfold Scale.delta1 at h1
    rw [hsx, hse, card_TT Fm x i0, ← M.card_TT'] at h1
    refine ⟨by rw [hab]; have := mul_pos hx0 hb0; linarith, ?_, ?_, w13, ?_⟩
    · rw [hcardH]; exact h1
    · rw [hcardH, M.card_thick_set_model_eq]; exact w15
    · rw [hcardH]; exact w14
  exact ⟨i0, M.m, M.f, M.pt, av, bv, ↥(Fm.TTn x), inferInstance,
    M.data ⌈2 * (Fm.L x i0).sc.a⌉₊ CH etaB eB ηv ev, mkC (max Cd 0) Cabs Cc Cs C1 Cl eL CH,
    (Fm.L x i0).sc.X'' (Fm.D x i0).R.n, ell, ⌈2 * (Fm.L x i0).sc.a⌉₊, M.TT, M.T2, M.a, M.w, M.eT, M.eP,
    (Fm.L x i0).etaSz, (Fm.L x i0).sc.X', Real.exp (-(c6 * x ^ (eps / 8))),
    M.tiePts, M.tieGlobal hx1 _ _ _ _ _ _, M.tieLocal _ _ _ _ _ _, M.tieArith ell hell1, rfl, rfl, le_refl _, le_refl _,
    le_refl _, M.ident _ _ _ _ _ _ ell hell2,
    ⟨L1, L2, L3, L4, L5, L6, L7, L8, liftZP_newton, ParameterUpperBound, liftZP_unit⟩, E1, B1, R1, W1, S1⟩

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions Formalism.D5 Formalism.FrobeniusOrbits Formalism.LFunctionChainParameters.LHost Formalism.RankGapBounds.WeightedMeanData

def gOfM (e : Formalism.HC.Frame) (ρ : E0 × e.A) : e.GG := ((if ρ.1.2 = 0 then 1 else -1, 1), e.iota ρ.2)

theorem sgnZ_ite (z : ZMod 2) : sgnZ (if z = 0 then 1 else -1) = z := by
  revert z; decide

theorem gOfM_mem (e : Formalism.HC.Frame) (ρ : E0 × e.A) : gOfM e ρ ∈ e.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff]; rfl

theorem gcode_gOfM (e : Formalism.HC.Frame) (ρ : E0 × e.A) (h : InPhi ρ) : gcode e (gOfM e ρ) = mcode e ρ := by
  unfold gcode mcode gOfM hval
  have h1 : ρ.1.1 = 0 := h
  refine Prod.ext (Prod.ext ?_ ?_) rfl
  · show sgnZ 1 = ρ.1.1
    rw [h1]; rfl
  · show sgnZ (if ρ.1.2 = 0 then 1 else -1) = ρ.1.2
    exact sgnZ_ite _

def NumN_at {D : D7} (L : SizeData₂ D) : Prop :=
  1 ≤ L.sc.w'' D.R.n ∧ 1 ≤ L.sc.b' ∧ L.sc.w'' D.R.n + L.etaSz ≤ 2 * L.sc.b' ∧
  ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x + L.etaSz ≤ 2 * L.sc.b'

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  exact Real.one_le_exp (Real.rpow_nonneg hx.le _)

theorem thick_set_lt_level {R : Ranks} (H : Host R) {s : ℕ} (hs : s ∈ H.T2) : s < R.n0 := by
  have h1 := H.second_set_range s hs
  have h2 := H.two_le_Lw
  have : s ≤ 4 * H.Lw * s := Nat.le_mul_of_pos_left s (by omega)
  omega

theorem mem_thick {R : Ranks} (H : Host R) (g : R.GG) :
    g ∈ H.thickPlaces ↔ ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = g := by
  unfold Host.thickPlaces
  simp only [Finset.mem_image]

theorem thick_iff (D : D7) (T2 : Finset D.R.A) (u0 : D.R.A)
    (hT2 : ∀ h, h ∈ T2 ↔ ∃ s ∈ D.host.T2, h = (D.R.toFrame).dig s) (hu0 : D.host.u0.val = hval D.R.toFrame u0)
    (ρ : E0 × D.R.A) (hρ : InPhi ρ) :
    IsThickAt T2 u0 ρ ↔ gOfM D.R.toFrame ρ ∈ D.host.thickPlaces := by
  have h2 : D.host.u0 = u0 := Formalism.HC.Frame.A.val_injective _ hu0
  rw [mem_thick, h2]
  unfold IsThickAt
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs, rfl⟩ := (hT2 t).1 ht
    refine ⟨s, hs, ?_⟩
    unfold Formalism.HC.Frame.tau2 gOfM thickPl
    refine Prod.ext (Prod.ext ?_ rfl) rfl
    show (-1 : ℤˣ) = if (1 : ZMod 2) = 0 then 1 else -1
    rw [if_neg (by decide)]
  · rintro ⟨s, hs, hγ⟩
    refine ⟨D.R.dig s, (hT2 _).2 ⟨s, hs, rfl⟩, ?_⟩
    unfold Formalism.HC.Frame.tau2 gOfM at hγ
    have hA : (-1 : ℤˣ) = if ρ.1.2 = 0 then 1 else -1 := congrArg (fun g : D.R.GG => g.1.1) hγ
    have hB : D.R.iota (D.R.dig s + u0) = D.R.iota ρ.2 := congrArg (fun g : D.R.GG => g.2) hγ
    have h12 : ρ.1.2 = 1 := by
      by_contra hne
      have h0 : ρ.1.2 = 0 := by
        have : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide
        exact this _ hne
      rw [if_pos h0] at hA
      exact absurd hA (by decide)
    have h11 : ρ.1.1 = 0 := hρ
    unfold thickPl
    exact Prod.ext (Prod.ext h11.symm h12.symm) (D.R.toFrame.iota_bijective.1 hB)

theorem nodes_at {D : D7} (L : SizeData₂ D) (hN : NumN_at L) : Nodes_at L := by
  intro e m T2 u0 w he hm hT2 hu0 hw hw1
  subst he; subst hm
  obtain ⟨hw2, hb', hthin, htop⟩ := hN
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have key : ∀ ρ : E0 × D.R.A, ∃ τ : D.what₂.Tau,
      ((D.eTau τ : D.R.Psi) : D.R.GG) = gOfM D.R.toFrame ρ := fun ρ =>
    ⟨D.eTau.symm ⟨gOfM D.R.toFrame ρ, gOfM_mem _ ρ⟩, by rw [Equiv.apply_symm_apply]⟩
  have hwρ : ∀ (j : Fin D.R.m) (ρ : E0 × D.R.A), InPhi ρ → ∀ τ : D.what₂.Tau,
      ((D.eTau τ : D.R.Psi) : D.R.GG) = gOfM D.R.toFrame ρ → w j ρ = wj D (j.val + 1) τ :=
    fun j ρ hρ τ h => hw j ρ τ (by rw [h, gcode_gOfM _ _ hρ])
  have hj : ∀ j : Fin D.R.m, 1 ≤ j.val + 1 ∧ j.val + 1 ≤ D.R.m := fun j => ⟨by omega, j.2⟩

  have cases3 : ∀ (j : Fin D.R.m) (ρ : E0 × D.R.A), InPhi ρ →
      (IsThickAt T2 u0 ρ ∧ L.sc.b ≤ w j ρ ∧ w j ρ ≤ L.sc.b + L.etaSz + 1) ∨
      (¬ IsThickAt T2 u0 ρ ∧ 1 ≤ w j ρ ∧ w j ρ ≤ 2 * L.sc.b') := by
    intro j ρ hρ
    obtain ⟨τ, hτ⟩ := key ρ
    rw [hwρ j ρ hρ τ hτ]
    by_cases hth : gOfM D.R.toFrame ρ ∈ D.host.thickPlaces
    · left
      exact ⟨(thick_iff D T2 u0 hT2 hu0 ρ hρ).2 hth,
        L.win_thick _ (hj j).1 (hj j).2 τ (by rw [hτ]; exact hth)⟩
    · right
      refine ⟨fun h => hth ((thick_iff D T2 u0 hT2 hu0 ρ hρ).1 h), ?_⟩
      by_cases htp : gOfM D.R.toFrame ρ ∈ D.host.topPlaces
      · unfold Host.topPlaces at htp
        obtain ⟨t, ht, htt⟩ := Finset.mem_image.mp htp
        have h := L.win_top _ (hj j).1 (hj j).2 τ ⟨t, ht⟩ (by rw [hτ]; exact htt.symm)
        have h1 := L.bT_ge ⟨t, ht⟩
        have h2 := htop ⟨t, ht⟩
        have h3 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg (by linarith) hx.le
        constructor <;> linarith [h.1, h.2]
      · have h := L.win_thin _ (hj j).1 (hj j).2 τ
          (by rw [hτ]; exact ⟨gOfM_mem _ ρ, htp, hth⟩)
        constructor <;> linarith [h.1, h.2]
  have hb := one_le_b L.sc
  refine ⟨fun j ρ hρ => ?_, fun j ρ hth => ?_, fun j ρ hρ hth => ?_⟩
  · rcases cases3 j ρ hρ with h | h
    · linarith [h.2.1]
    · exact h.2.1
  · have hρ : InPhi ρ := by
      unfold IsThickAt at hth
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hth
      rfl
    rcases cases3 j ρ hρ with h | h
    · exact h.2
    · exact absurd hth h.1
  · rcases cases3 j ρ hρ with h | h
    · exact absurd h.1 hth
    · exact h.2.2

theorem sc_pos (s : Scale) : 0 < s.x ∧ 0 < s.b ∧ 0 < s.a ∧ 0 < s.X' ∧ 0 < s.b' := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hb : 0 < s.b := Real.exp_pos _
  have ha : 0 < s.a := mul_pos hx hb
  have hX : 0 < s.X' := Real.exp_pos _
  exact ⟨hx, hb, ha, hX, div_pos ha hX⟩

theorem one_le_n (R : Ranks) : (1 : ℝ) ≤ R.n := by
  have : 1 ≤ R.n := R.toFrame.ord_pos
  exact_mod_cast this

theorem numN_at {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hS : SizesAt L) (h3 : 3 ≤ L.sc.x) : NumN_at L := by
  obtain ⟨sN, sM, sK, sKR, sT, sCond, sQD, sTT, sLa, sRho, sBot, sDe2, sLw, sEta, sNodes, sLstar, sDel, sW, sBm,
    sXpp, sG, sPde, sWords⟩ := hS
  obtain ⟨hx, hb, ha, hX, hb'⟩ := sc_pos L.sc
  have hn := one_le_n D.R
  have hb1 := one_le_b L.sc
  have hw1 : 1 ≤ L.sc.w'' D.R.n := le_trans (Real.one_le_sqrt.mpr hb1) sW
  have hxn : 1 ≤ L.sc.x * D.R.n := by nlinarith
  have hwb : L.sc.w'' D.R.n ≤ L.sc.b' := by
    unfold Scale.w''
    exact div_le_self hb'.le hxn
  have ht : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by
      obtain ⟨r, hr⟩ := D.R.t_odd
      omega
    exact_mod_cast this
  have hη0 := L.etaSz_pos
  have hη : L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x := by
    have := P.teta
    nlinarith
  have hwx : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.b' / 3 := by
    rw [div_le_div_iff₀ hx (by norm_num)]
    nlinarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 3 := by
    rw [div_le_div_iff₀ hx (by norm_num)]
    nlinarith
  refine ⟨hw1, le_trans hw1 hwb, by linarith, fun t => ?_⟩
  have hk : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hLa : 0 < L.LaG := lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) sLa.1
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have h2nd : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le hlog) hLa.le) hk.le
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 / 9 := by
    rw [Real.rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hrho := P.rho_le
  unfold LevelStarExponents.rhoP at hrho
  have hA : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 36 := by
    have e1 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    rw [e1] at hrho
    linarith
  have hbT := P.bT_le t
  have e2 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  rw [e2] at hbT
  have h36 : (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' ≤ 1 / 36 * L.sc.b' :=
    mul_le_mul_of_nonneg_right hA hb'.le
  linarith

theorem nodesF {eps : ℝ} (Fm : FamP eps) : NodesF Fm := by
  refine ⟨max (Fm.x1 + 1) 3, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_left _ _) hx
    linarith
  have h3 : 3 ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx1]; exact le_trans (le_max_right _ _) hx
  exact nodes_at _ (numN_at (Fm.params x hx1 i) (Fm.sizes x hx1 i) h3)

theorem lat_at (D : D7) (hR : D.RRFull) (hN : D.NuFull) (hr : ∀ u, 0 < (D.div.Nu u).rank)
    (hrr : 0 < D.div.RR.rank) : Lat_at D := by
  refine ⟨fun u => ⟨hr u, ?_⟩, ?_⟩
  · have hc : 0 < Fintype.card (D.div.Nu u).ι := by
      have h1 := hr u
      unfold HLat.rank Formalism.HN.rkK at h1
      rw [(hN u).2, finrank_top, Module.finrank_eq_card_basis (D.div.Nu u).b] at h1
      exact h1
    exact Formalism.LFunctionChainParameters.MatrixLatticeEstimates.slope_le_max_slope (D.div.Nu u).b (D.div.Nu u).X (D.div_good.2 u) (D.div.Nu u).L
      (hN u).1 (hN u).2 hc
  · exact bridge_dual_mu_holds D.what₂.LL D.div.RR ⟨D.div_good.1, hR.1, hR.2⟩ hrr

def RRRankF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 < (Fm.D x i).div.RR.rank

theorem latF {eps : ℝ} (Fm : FamP eps) {Cabs CH : ℝ} (h : LinkDIV Fm Cabs CH) (hNF : NuFullF Fm) (hR : J.MuRank Fm)
    (hRR : RRRankF Fm) : LatF Fm := by
  obtain ⟨C, a0, h⟩ := h
  obtain ⟨a1, hR⟩ := hR
  obtain ⟨a2, hRR⟩ := hRR
  obtain ⟨a3, hNF⟩ := hNF
  refine ⟨max a0 (max a1 (max a2 a3)), fun x hx i => ?_⟩
  have b0 : x ≥ a0 := (le_max_left _ _).trans hx
  have c1 := (le_max_right _ _).trans hx
  have b1 : x ≥ a1 := (le_max_left _ _).trans c1
  have c2 := (le_max_right _ _).trans c1
  have b2 : x ≥ a2 := (le_max_left _ _).trans c2
  have b3 : x ≥ a3 := (le_max_right _ _).trans c2
  exact lat_at _ (h x b0 i).2.2.2.2.1 (hNF x b3 i) (hR x b1 i) (hRR x b2 i)

theorem ev_pow_le_exp (c δ A : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 1 ≤ x → x ^ A ≤ Real.exp (c * x ^ δ) := by
  set M : ℝ := 2 * |A| / (δ * c) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M ^ (2 / δ), fun x hx h1 => ?_⟩
  have hx0 : 0 < x := by linarith
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.mpr
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg h1
  have hlog : Real.log x ≤ x ^ (δ / 2) / (δ / 2) := Real.log_le_rpow_div hx0.le (by positivity)
  have hMx : M ≤ x ^ (δ / 2) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hx (by positivity : 0 ≤ δ / 2)
    rw [← Real.rpow_mul hM0, show 2 / δ * (δ / 2) = 1 by field_simp, Real.rpow_one] at h
    exact h
  have hy : 0 < x ^ (δ / 2) := Real.rpow_pos_of_pos hx0 _
  have hsq : x ^ δ = x ^ (δ / 2) * x ^ (δ / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have h1' : Real.log x * A ≤ |A| * (x ^ (δ / 2) / (δ / 2)) := by
    calc Real.log x * A ≤ Real.log x * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hlog0
      _ = |A| * Real.log x := mul_comm _ _
      _ ≤ |A| * (x ^ (δ / 2) / (δ / 2)) := mul_le_mul_of_nonneg_left hlog (abs_nonneg A)
  have h2' : |A| * (x ^ (δ / 2) / (δ / 2)) = c * (M * x ^ (δ / 2)) := by
    rw [hM]; field_simp
  have h3' : c * (M * x ^ (δ / 2)) ≤ c * x ^ δ := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMx hy.le) hc.le
  linarith

theorem ev_two_le_rpow (δ : ℝ) (hδ : 0 < δ) : ∃ x0 : ℝ, ∀ x ≥ x0, 2 ≤ x ^ δ := by
  refine ⟨(2 : ℝ) ^ (1 / δ), fun x hx => ?_⟩
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hx hδ.le
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), show 1 / δ * δ = 1 by field_simp, Real.rpow_one] at h
  exact h

theorem rpow_mono' (s : Scale) {a b : ℝ} (h : a ≤ b) : s.x ^ a ≤ s.x ^ b :=
  Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le h

theorem sqrt_xd (s : Scale) : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  have hx : 0 < s.x := lt_trans one_pos s.one_lt_alt
  unfold Scale.delta1
  have h : s.x * s.x ^ (-(s.eps / 8)) = s.x ^ (1 - s.eps / 8) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [h, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1; ring

section WinParts

variable {D : D7} {L : SizeData₂ D}

theorem m_le (sM : SizeM L) : (D.R.m : ℝ) ≤ L.sc.x ^ (szTh L + ((1 : ℝ) / 2 - L.sc.eps / 16)) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have h := sM.2
  rw [sqrt_xd, ← Real.rpow_add hx] at h
  exact h

theorem m_ge (sM : SizeM L) : L.sc.x ^ (-szTh L + ((1 : ℝ) / 2 - L.sc.eps / 16)) ≤ (D.R.m : ℝ) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have h := sM.1
  rw [sqrt_xd, ← Real.rpow_add hx] at h
  exact h

theorem winA (sM : SizeM L) : (D.R.m : ℝ) ≤ L.sc.x ^ ((1 : ℝ) / 2 + L.sc.eps / 2) :=
  (m_le sM).trans (rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_pos]))

theorem winL (sM : SizeM L) : L.sc.x ^ ((1 : ℝ) / 2 - L.sc.eps) ≤ (D.R.m : ℝ) :=
  (rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_pos])).trans (m_ge sM)

theorem winB (sM : SizeM L) (sK : SizeK L) : L.sc.x * D.R.m ≤ D.R.k := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  calc L.sc.x * D.R.m ≤ L.sc.x * L.sc.x ^ (szTh L + ((1 : ℝ) / 2 - L.sc.eps / 16)) :=
        mul_le_mul_of_nonneg_left (m_le sM) hx.le
    _ = L.sc.x ^ (1 + (szTh L + ((1 : ℝ) / 2 - L.sc.eps / 16))) := by
        rw [Real.rpow_add hx 1, Real.rpow_one]
    _ ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) :=
        rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_pos])
    _ ≤ D.R.k := sK.1

theorem winC (sK : SizeK L) : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) :=
  sK.2.trans (rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_lt]))

theorem x_pow_four_le_k (sK : SizeK L) : L.sc.x ^ (4 : ℝ) ≤ (D.R.k : ℝ) :=
  (rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_pos])).trans sK.1

theorem n_le_x_cubed (sN : SizeN L) : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) :=
  sN.2.trans (rpow_mono' _ (by unfold szTh; linarith [L.sc.eps_lt]))

theorem winM (P : ParameterChoice' D L) : (D.R.k : ℝ) ≤ (D.R.n : ℝ) ^ 2 * L.sc.x ^ ((1 : ℝ) / 2 - L.sc.eps) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have h := P.k_up
  unfold LevelStarExponents.R0 at h
  rw [sub_eq_add_neg, Real.rpow_add hx]
  calc (D.R.k : ℝ) ≤ _ := h
    _ = _ := by ring

theorem kx_ge_one (L : SizeData₂ D) : 1 ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by
  have hk : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hx1 : 1 ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
  nlinarith

theorem winH (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.a := by
  have ha := (sc_pos L.sc).2.2.1
  have h := (L.aT_win t).2
  have h2 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a := div_le_self ha.le (kx_ge_one L)
  linarith

theorem winO (L : SizeData₂ D) (t : D.host.TT) : |(L.aT t : ℝ) / L.sc.b - L.sc.x| ≤ 1 := by
  obtain ⟨hx, hb, ha, -, -⟩ := sc_pos L.sc
  have h := L.aT_win t
  have hab : L.sc.a / L.sc.b = L.sc.x := by unfold Scale.a; field_simp
  have hk : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hxA : L.sc.x ≤ L.sc.x ^ (Scale.A / 2) := by
    have := rpow_mono' L.sc (a := 1) (b := Scale.A / 2) (by unfold Scale.A; norm_num)
    rwa [Real.rpow_one] at this
  have hden : L.sc.x ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := by nlinarith
  have hdpos : 0 < (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) := lt_of_lt_of_le hx hden
  have h1 : L.sc.x ≤ (L.aT t : ℝ) / L.sc.b := by
    rw [← hab]; exact div_le_div_of_nonneg_right h.1 hb.le
  have h2 : (L.aT t : ℝ) / L.sc.b ≤ L.sc.x + 1 := by
    have h3 : (L.aT t : ℝ) / L.sc.b ≤ (L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))) / L.sc.b :=
      div_le_div_of_nonneg_right h.2 hb.le
    have h4 : (L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))) / L.sc.b =
        L.sc.x + L.sc.x / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := by
      rw [add_div, hab, div_div, mul_comm _ L.sc.b, ← div_div, hab]
    have h5 : L.sc.x / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ 1 := (div_le_one hdpos).2 hden
    linarith
  rw [abs_le]; constructor <;> linarith

theorem winI (P : ParameterChoice' D L) :
    Real.log (Fintype.card D.what₂.Word : ℝ) ≤ ((D.R.k : ℝ) - 3) * Real.log 2 := by
  have hc : 0 < Fintype.card D.what₂.Word := Fintype.card_pos
  have h := P.words_le
  have hk : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have h1 : (Fintype.card D.what₂.Word : ℝ) ≤ (2 : ℝ) ^ (D.R.k - 3) := by exact_mod_cast h
  have h2 := Real.log_le_log (by exact_mod_cast hc) h1
  rw [Real.log_pow, Nat.cast_sub hk] at h2
  exact_mod_cast h2

theorem winP (sQD : SizeQD L) : 0 < D.host.v := by
  have h := sQD.2.2.2.2.2.2.1
  unfold Host.v
  linarith

end WinParts

section WinLarge

variable {D : D7} {L : SizeData₂ D}

theorem rpow_nat (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n

theorem k_le_X' (sK : SizeK L) (hE1 : L.sc.x ^ (5 : ℝ) ≤ Real.exp (1 * L.sc.x ^ (L.sc.eps / 3))) :
    (D.R.k : ℝ) ≤ L.sc.X' := by
  unfold Scale.X'
  rw [one_mul] at hE1
  exact (winC sK).trans hE1

theorem X'_le_a (s : Scale) : s.X' ≤ s.a := by
  have hb : 0 < s.b := Real.exp_pos _
  have h1 : s.X' ≤ s.b := by
    unfold Scale.X' Scale.b Scale.L
    exact Real.exp_le_exp.mpr (rpow_mono' s (by linarith [s.eps_pos]))
  unfold Scale.a
  nlinarith [s.one_lt_alt]

theorem winF' (sK : SizeK L) (hE1 : L.sc.x ^ (5 : ℝ) ≤ Real.exp (1 * L.sc.x ^ (L.sc.eps / 3))) :
    D.R.k * L.sc.b' ≤ L.sc.a := by
  obtain ⟨hx, hb, ha, hX, hb'⟩ := sc_pos L.sc
  have hk := k_le_X' sK hE1
  unfold Scale.b'
  calc (D.R.k : ℝ) * (L.sc.a / L.sc.X') = L.sc.a * ((D.R.k : ℝ) / L.sc.X') := by ring
    _ ≤ L.sc.a * 1 := mul_le_mul_of_nonneg_left ((div_le_one hX).2 hk) ha.le
    _ = L.sc.a := mul_one _

theorem winG (hw1 : 1 ≤ L.sc.w'' D.R.n) : L.sc.X'' D.R.n ≤ L.sc.a := by
  unfold Scale.X''
  exact div_le_self (sc_pos L.sc).2.2.1.le hw1

theorem four_le (x : ℝ) (h3 : 3 ≤ x) : 4 * (x + 1) ≤ x ^ 3 := by
  have h2 : 9 ≤ x ^ 2 := by nlinarith
  have h4 : 9 * x ≤ x ^ 3 := by nlinarith
  linarith

theorem f_le (sN : SizeN L) : (D.R.f : ℝ) ≤ 2 * L.sc.x ^ 3 := by
  have h := n_le_x_cubed sN
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, rpow_nat] at h
  have : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by unfold Ranks.f; push_cast; ring
  rw [this]; linarith

theorem winJ (sN : SizeN L) (c6 : ℝ) (h3 : 3 ≤ L.sc.x)
    (hE3 : L.sc.x ^ (7 : ℝ) ≤ Real.exp (c6 * L.sc.x ^ (L.sc.eps / 8))) :
    2 * (D.R.f : ℝ) * (L.sc.x + 1) * Real.exp (-(c6 * L.sc.x ^ (L.sc.eps / 8))) ≤ 1 / L.sc.x := by
  have hx : 0 < L.sc.x := by linarith
  have hf := f_le sN
  have h4 := four_le _ h3
  rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, rpow_nat] at hE3
  have h1 : 2 * (D.R.f : ℝ) * (L.sc.x + 1) * L.sc.x ≤ L.sc.x ^ 7 := by
    calc 2 * (D.R.f : ℝ) * (L.sc.x + 1) * L.sc.x ≤ 2 * (2 * L.sc.x ^ 3) * (L.sc.x + 1) * L.sc.x := by gcongr
      _ = L.sc.x ^ 4 * (4 * (L.sc.x + 1)) := by ring
      _ ≤ L.sc.x ^ 4 * L.sc.x ^ 3 := by gcongr
      _ = L.sc.x ^ 7 := by ring
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hx, one_mul]
  exact h1.trans hE3

theorem winK (P : ParameterChoice' D L) (sN : SizeN L) (sK : SizeK L) (h3 : 3 ≤ L.sc.x)
    (hE4 : L.sc.x ^ (9 : ℝ) ≤ Real.exp (1 * L.sc.x ^ L.sc.eps)) :
    6 * (D.R.f : ℝ) * (L.sc.x + 1) * (L.etaSz + 1) ≤ L.sc.b / L.sc.x := by
  have hx : 0 < L.sc.x := by linarith
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hf := f_le sN
  have h4 := four_le _ h3
  have hη := L.etaSz_pos
  have hb : L.sc.x ^ 9 ≤ L.sc.b := by
    rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, rpow_nat, one_mul] at hE4
    exact hE4
  have hf0 : (0 : ℝ) < D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have ht : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by
      obtain ⟨r, hr⟩ := D.R.t_odd
      omega
    exact_mod_cast this
  have hk4 : L.sc.x ^ 4 ≤ (D.R.k : ℝ) := by
    have h := x_pow_four_le_k sK
    rwa [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, rpow_nat] at h
  have hk0 : (0 : ℝ) < D.R.k := lt_of_lt_of_le (by positivity) hk4
  have hk12 : L.sc.x ^ 12 ≤ (D.R.k : ℝ) ^ 3 := by
    calc L.sc.x ^ 12 = (L.sc.x ^ 4) ^ 3 := by ring
      _ ≤ (D.R.k : ℝ) ^ 3 := by gcongr
  have ht3 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ ht
  have hden : 0 < (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by positivity
  have hA0 := (le_div_iff₀ hden).1 P.eta_le
  have hfη0 : 0 ≤ (D.R.f : ℝ) * L.etaSz := by positivity
  have A1 : (D.R.f : ℝ) * L.etaSz * L.sc.x ^ 12 ≤ L.sc.b := by
    calc (D.R.f : ℝ) * L.etaSz * L.sc.x ^ 12 ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) := by
          apply mul_le_mul_of_nonneg_left _ hfη0
          calc L.sc.x ^ 12 ≤ (D.R.k : ℝ) ^ 3 := hk12
            _ = 1 * (D.R.k : ℝ) ^ 3 := (one_mul _).symm
            _ ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 := by gcongr
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ L.sc.b := hA0
  have hx2 : 9 ≤ L.sc.x ^ 2 := by nlinarith
  have A2 : 12 * L.sc.x * (L.sc.x + 1) ≤ L.sc.x ^ 12 := by
    calc 12 * L.sc.x * (L.sc.x + 1) = 3 * L.sc.x * (4 * (L.sc.x + 1)) := by ring
      _ ≤ 3 * L.sc.x * L.sc.x ^ 3 := by gcongr
      _ = 3 * L.sc.x ^ 4 := by ring
      _ ≤ L.sc.x ^ 2 * L.sc.x ^ 4 := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = L.sc.x ^ 6 := by ring
      _ ≤ L.sc.x ^ 12 := pow_le_pow_right₀ hx1 (by norm_num)
  have B1 : 12 * L.sc.x * (L.sc.x + 1) * ((D.R.f : ℝ) * L.etaSz) ≤ L.sc.b := by
    calc 12 * L.sc.x * (L.sc.x + 1) * ((D.R.f : ℝ) * L.etaSz) ≤ L.sc.x ^ 12 * ((D.R.f : ℝ) * L.etaSz) :=
          mul_le_mul_of_nonneg_right A2 hfη0
      _ = (D.R.f : ℝ) * L.etaSz * L.sc.x ^ 12 := by ring
      _ ≤ L.sc.b := A1
  have B2 : 12 * L.sc.x * (L.sc.x + 1) * (D.R.f : ℝ) ≤ L.sc.b := by
    calc 12 * L.sc.x * (L.sc.x + 1) * (D.R.f : ℝ) ≤ 12 * L.sc.x * (L.sc.x + 1) * (2 * L.sc.x ^ 3) := by gcongr
      _ = 6 * L.sc.x ^ 4 * (4 * (L.sc.x + 1)) := by ring
      _ ≤ 6 * L.sc.x ^ 4 * L.sc.x ^ 3 := by gcongr
      _ = 6 * L.sc.x ^ 7 := by ring
      _ ≤ L.sc.x ^ 2 * L.sc.x ^ 7 := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = L.sc.x ^ 9 := by ring
      _ ≤ L.sc.b := hb
  rw [le_div_iff₀ hx]
  have e : 6 * (D.R.f : ℝ) * (L.sc.x + 1) * (L.etaSz + 1) * L.sc.x =
      (12 * L.sc.x * (L.sc.x + 1) * ((D.R.f : ℝ) * L.etaSz) + 12 * L.sc.x * (L.sc.x + 1) * (D.R.f : ℝ)) / 2 := by
    ring
  rw [e]; linarith

theorem winE (sN : SizeN L) (sQD : SizeQD L) (h3 : 3 ≤ L.sc.x)
    (hE5 : L.sc.x ^ (5 : ℝ) ≤ Real.exp (1 / 2 * L.sc.x ^ L.sc.eps))
    (hE6 : 2 ≤ L.sc.x ^ (L.sc.eps - (L.sc.eps / 5 + szTh L))) :
    0 ≤ L.La ∧ L.La ≤ 2 * L.sc.x ^ L.sc.eps := by
  obtain ⟨hx, hb, ha, -, -⟩ := sc_pos L.sc
  obtain ⟨-, -, hq, -, hd, -, hrd1, hrd2⟩ := sQD
  have hrd0 : 0 < D.host.rdE := by linarith
  have ha1 : 1 ≤ L.sc.a := by
    have := one_le_b L.sc
    unfold Scale.a; nlinarith
  constructor
  · unfold SizeData₂.La
    apply Real.log_nonneg
    nlinarith
  have hq0 : (0 : ℝ) < D.host.q := by exact_mod_cast D.host.hyp.1.pos
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hn0 : (0 : ℝ) < D.R.n := lt_of_lt_of_le one_pos (one_le_n D.R)
  have hloga : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hsq : 0 < Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_pos.mpr (mul_pos hq0 hd0)
  have hlx : 0 ≤ Real.log L.sc.x := Real.log_nonneg L.sc.one_lt_alt.le
  have hxe : 0 < L.sc.x ^ (L.sc.eps / 100) := Real.rpow_pos_of_pos hx _
  have hlogrd : Real.log D.host.rdE ≤ Real.log 2 + Real.log D.R.n + L.sc.eps / 100 * Real.log L.sc.x +
      (Real.log D.host.q + Real.log D.host.d) / 2 := by
    have hrd3 : D.host.rdE ≤ 2 * (D.R.n : ℝ) * L.sc.x ^ (L.sc.eps / 100) * Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
      hrd2.trans (mul_le_mul_of_nonneg_right (by linarith [L.QS_tie]) hsq.le)
    have h := Real.log_le_log hrd0 hrd3
    rw [Real.log_mul (by positivity) hsq.ne', Real.log_mul (by positivity) hxe.ne',
      Real.log_mul (by norm_num) hn0.ne', Real.log_rpow hx,
      Real.log_sqrt (mul_pos hq0 hd0).le, Real.log_mul hq0.ne' hd0.ne'] at h
    exact h
  have hlogn : Real.log D.R.n + L.sc.eps / 100 * Real.log L.sc.x ≤ 3 * Real.log L.sc.x := by
    have h := Real.log_le_log hn0 sN.2
    rw [Real.log_rpow hx] at h
    have h' : (2 + 8 * L.sc.eps + szTh L + L.sc.eps / 100) * Real.log L.sc.x ≤ 3 * Real.log L.sc.x :=
      mul_le_mul_of_nonneg_right (by unfold szTh; linarith [L.sc.eps_lt]) hlx
    linarith
  have h5 : 5 * Real.log L.sc.x ≤ 1 / 2 * L.sc.x ^ L.sc.eps := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hx _) hE5
    rwa [Real.log_rpow hx, Real.log_exp] at h
  have hlog2 : Real.log 2 ≤ Real.log L.sc.x := Real.log_le_log (by norm_num) (by linarith)
  have h6 : 2 * L.sc.x ^ (L.sc.eps / 5 + szTh L) ≤ L.sc.x ^ L.sc.eps := by
    have e : L.sc.x ^ L.sc.eps =
        L.sc.x ^ (L.sc.eps - (L.sc.eps / 5 + szTh L)) * L.sc.x ^ (L.sc.eps / 5 + szTh L) := by
      rw [← Real.rpow_add hx]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hE6 (Real.rpow_nonneg hx.le _)
  unfold SizeData₂.La
  rw [Real.log_mul ha.ne' hrd0.ne', hloga]
  linarith

def XL (s : Scale) (c6 : ℝ) : Prop :=
  3 ≤ s.x ∧ s.x ^ (5 : ℝ) ≤ Real.exp (1 * s.x ^ (s.eps / 3)) ∧
  s.x ^ (7 : ℝ) ≤ Real.exp (c6 * s.x ^ (s.eps / 8)) ∧ s.x ^ (9 : ℝ) ≤ Real.exp (1 * s.x ^ s.eps) ∧
  s.x ^ (5 : ℝ) ≤ Real.exp (1 / 2 * s.x ^ s.eps) ∧ 2 ≤ s.x ^ (s.eps - (s.eps / 5 + s.eps / 100))

end WinLarge

theorem fam_eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions.Lnk

open Formalism.BasicNotions

theorem ev_loglog (ka : ℝ) (hk : 0 < ka) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 2 * Real.log (Real.log x) ≤ ka * Real.log x := by
  refine ⟨Real.exp ((4 / ka) ^ 2), fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hy : (4 / ka) ^ 2 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at h
  have h4 : 0 < 4 / ka := by positivity
  have hy0 : 0 < Real.log x := lt_of_lt_of_le (by positivity) hy
  have hs : 4 / ka ≤ Real.sqrt (Real.log x) := Real.le_sqrt_of_sq_le hy
  have hs0 : 0 < Real.sqrt (Real.log x) := lt_of_lt_of_le h4 hs
  have hss : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x := Real.mul_self_sqrt hy0.le
  have hlog : Real.log (Real.log x) ≤ 2 * Real.sqrt (Real.log x) := by
    have h := Real.log_le_rpow_div hy0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have h5 : 4 ≤ ka * Real.sqrt (Real.log x) := by
    have := mul_le_mul_of_nonneg_left hs hk.le
    rwa [mul_div_cancel₀ _ hk.ne'] at this
  have h6 : 4 * Real.sqrt (Real.log x) ≤ ka * Real.log x := by
    have h7 := mul_le_mul_of_nonneg_right h5 hs0.le
    rw [mul_assoc, hss] at h7
    exact h7
  linarith

section

variable {D : D7} {L : SizeData₂ D}

theorem winN' (hT : D.host.secondSet_card_lower_bound) (sN : SizeN L) (sLw : SizeLw L) (CT ka : ℝ) (hCT : D.host.CT2 ≤ CT)
    (hCT0 : 0 < CT) (hk1 : ka ≤ L.sc.eps / 2) (hk2 : 12 * ka * CT ^ 2 ≤ L.sc.eps ^ 2)
    (h3 : 3 ≤ L.sc.x) (hE : 2 * Real.log (Real.log L.sc.x) ≤ ka * Real.log L.sc.x) :
    L.sc.x ^ (-L.sc.eps) ≤ (D.host.T2.card : ℝ) / D.R.n := by
  have hx : 0 < L.sc.x := by linarith
  have he : 0 < L.sc.eps := L.sc.eps_pos
  have hy1 : 1 ≤ Real.log L.sc.x := by
    have h1 : Real.exp 1 ≤ L.sc.x := by have := Real.exp_one_lt_d9; linarith
    have h := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h
  have hy0 : 0 < Real.log L.sc.x := by linarith
  have hn1 : (1 : ℝ) ≤ D.R.n := one_le_n D.R
  have hn0 : (0 : ℝ) < D.R.n := by linarith
  have hLw2 : (2 : ℝ) ≤ D.host.Lw := by exact_mod_cast D.host.two_le_Lw
  have hLw0 : (0 : ℝ) < D.host.Lw := by linarith
  have hm1 : (1 : ℝ) ≤ (D.R.n0 : ℝ) := by exact_mod_cast D.R.toFrame.n0_pos
  have hm0 : (0 : ℝ) < (D.R.n0 : ℝ) := by linarith
  have hmn : (D.R.n0 : ℝ) ≤ (D.R.n : ℝ) := by exact_mod_cast D.R.toFrame.cyclic_order_le_exponent
  have hlogn0 : 0 ≤ Real.log (D.R.n0 : ℝ) := Real.log_nonneg hm1
  have hlogn : Real.log (D.R.n0 : ℝ) ≤ 9 / 4 * Real.log L.sc.x := by
    have h := Real.log_le_log hm0 (hmn.trans (sN.2.trans
      (rpow_mono' L.sc (b := 9 / 4) (by unfold szTh; linarith [L.sc.eps_lt]))))
    rwa [Real.log_rpow hx] at h
  have hlw0 : 0 ≤ Real.log (D.host.Lw : ℝ) := Real.log_nonneg (by linarith)
  have hlw : Real.log (D.host.Lw : ℝ) ≤ ka * Real.log L.sc.x := by
    have h := Real.log_le_log hLw0 sLw
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hnE : (D.R.n : ℝ) = (D.R.o : ℝ) * (D.R.n0 : ℝ) := by exact_mod_cast D.R.toFrame.exponent_eq_index_mul_cyclic_order
  unfold Host.secondSet_card_lower_bound at hT
  set S : ℝ := Real.sqrt (Real.log (D.R.n0 : ℝ) * Real.log (D.host.Lw : ℝ)) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSle : S ≤ 9 / 20 * (L.sc.eps * Real.log L.sc.x) / CT := by
    rw [hS]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h1 : Real.log (D.R.n0 : ℝ) * Real.log (D.host.Lw : ℝ) ≤
        (9 / 4 * Real.log L.sc.x) * (ka * Real.log L.sc.x) :=
      mul_le_mul hlogn hlw hlw0 (by positivity)
    have h2 : (9 / 20 * (L.sc.eps * Real.log L.sc.x) / CT) ^ 2 =
        81 / 400 * (L.sc.eps ^ 2 * Real.log L.sc.x ^ 2) / CT ^ 2 := by
      rw [div_pow, mul_pow, mul_pow]; norm_num
    rw [h2, le_div_iff₀ (by positivity)]
    have h3' : (9 / 4 * Real.log L.sc.x) * (ka * Real.log L.sc.x) * CT ^ 2 =
        3 / 16 * ((12 * ka * CT ^ 2) * Real.log L.sc.x ^ 2) := by ring
    have h4 : (12 * ka * CT ^ 2) * Real.log L.sc.x ^ 2 ≤ L.sc.eps ^ 2 * Real.log L.sc.x ^ 2 :=
      mul_le_mul_of_nonneg_right hk2 (by positivity)
    have h5 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ CT ^ 2)
    have h6 : 0 ≤ L.sc.eps ^ 2 * Real.log L.sc.x ^ 2 := by positivity
    linarith
  have hCS : D.host.CT2 * S ≤ 9 / 20 * (L.sc.eps * Real.log L.sc.x) := by
    have h1 : D.host.CT2 * S ≤ CT * S := mul_le_mul_of_nonneg_right hCT hS0
    have h2 : CT * S ≤ CT * (9 / 20 * (L.sc.eps * Real.log L.sc.x) / CT) := mul_le_mul_of_nonneg_left hSle hCT0.le
    have h3' : CT * (9 / 20 * (L.sc.eps * Real.log L.sc.x) / CT) = 9 / 20 * (L.sc.eps * Real.log L.sc.x) := by
      field_simp
    linarith
  have hk1' : ka * Real.log L.sc.x ≤ L.sc.eps / 2 * Real.log L.sc.x := mul_le_mul_of_nonneg_right hk1 hy0.le
  have hey : 0 < L.sc.eps * Real.log L.sc.x := mul_pos he hy0
  have hexp : L.sc.x ^ (-L.sc.eps) * L.sc.x ^ (L.sc.eps / 100) ≤ Real.exp (-(D.host.CT2 * S)) / D.host.Lw := by
    rw [← Real.rpow_add hx, Real.rpow_def_of_pos hx, le_div_iff₀ hLw0]
    calc Real.exp (Real.log L.sc.x * (-L.sc.eps + L.sc.eps / 100)) * (D.host.Lw : ℝ)
        = Real.exp (Real.log L.sc.x * (-L.sc.eps + L.sc.eps / 100)) * Real.exp (Real.log (D.host.Lw : ℝ)) := by
          rw [Real.exp_log hLw0]
      _ = Real.exp (Real.log L.sc.x * (-L.sc.eps + L.sc.eps / 100) + Real.log (D.host.Lw : ℝ)) :=
          (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(D.host.CT2 * S)) := Real.exp_le_exp.mpr (by linarith)
  have hxe : 0 ≤ L.sc.x ^ (-L.sc.eps) := Real.rpow_nonneg hx.le _
  rw [le_div_iff₀ hn0]
  calc L.sc.x ^ (-L.sc.eps) * (D.R.n : ℝ) = L.sc.x ^ (-L.sc.eps) * (D.R.o : ℝ) * (D.R.n0 : ℝ) := by rw [hnE]; ring
    _ ≤ L.sc.x ^ (-L.sc.eps) * L.sc.x ^ (L.sc.eps / 100) * (D.R.n0 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left L.o_tie hxe) hm0.le
    _ ≤ Real.exp (-(D.host.CT2 * S)) / D.host.Lw * (D.R.n0 : ℝ) := mul_le_mul_of_nonneg_right hexp hm0.le
    _ = (D.R.n0 : ℝ) * Real.exp (-(D.host.CT2 * S)) / D.host.Lw := by ring
    _ ≤ _ := hT

theorem size_window_at_five (P : ParameterChoice' D L) (sN : SizeN L) (sM : SizeM L) (sK : SizeK L)
    (hLa : 0 ≤ L.La ∧ L.La ≤ 2 * L.sc.x ^ L.sc.eps) (hv : 0 < D.host.v) (hw1 : 1 ≤ L.sc.w'' D.R.n)
    (hN : L.sc.x ^ (-L.sc.eps) ≤ (D.host.T2.card : ℝ) / D.R.n) (c6 : ℝ) (hX : XL L.sc c6) : Win_at L 5 c6 := by
  obtain ⟨h3, hE1, hE3, hE4, -, -⟩ := hX
  exact ⟨winA sM, winB sM sK, winC sK, (k_le_X' sK hE1).trans (X'_le_a _), hLa.1, hLa.2, winF' sK hE1,
    winG hw1, winH L, winI P, winJ sN c6 h3 hE3, winK P sN sK h3 hE4, winL sM, winM P, hN, winO L, hv⟩

end

theorem size_windows_of_thick_set {eps : ℝ} (Fm : FamP eps) (hT2 : ThickSetEventually Fm) : WinF Fm := by
  intro c6 hc6
  have h0 : 0 < eps := fam_eps_pos Fm
  obtain ⟨aT, hT2⟩ := hT2
  set CT : ℝ := max Fm.CT2 0 + 1 with hCTdef
  have hCT0 : 0 < CT := by have := le_max_right Fm.CT2 0; linarith
  have hCTle : Fm.CT2 ≤ CT := by have := le_max_left Fm.CT2 0; linarith
  set ka : ℝ := min (eps / 2) (eps ^ 2 / (12 * CT ^ 2)) with hkadef
  have hka0 : 0 < ka := lt_min (by positivity) (by positivity)
  have hka1 : ka ≤ eps / 2 := min_le_left _ _
  have hka2 : 12 * ka * CT ^ 2 ≤ eps ^ 2 := by
    have h := min_le_right (eps / 2) (eps ^ 2 / (12 * CT ^ 2))
    rw [← hkadef, le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨a1, h1⟩ := ev_pow_le_exp 1 (eps / 3) 5 one_pos (by positivity)
  obtain ⟨a3, h3⟩ := ev_pow_le_exp c6 (eps / 8) 7 hc6 (by positivity)
  obtain ⟨a4, h4⟩ := ev_pow_le_exp 1 eps 9 one_pos h0
  obtain ⟨a5, h5⟩ := ev_pow_le_exp (1 / 2) eps 5 (by norm_num) h0
  obtain ⟨a6, h6⟩ := ev_two_le_rpow (eps - (eps / 5 + eps / 100)) (by linarith)
  obtain ⟨a7, h7⟩ := ev_loglog ka hka0
  refine ⟨5, Fm.x1 + 3 + |a1| + |a3| + |a4| + |a5| + |a6| + |a7| + |aT|, by norm_num, fun x hx i => ?_⟩
  have hpos := Fm.one_lt_family_threshold
  have n1 := abs_nonneg a1
  have n3 := abs_nonneg a3
  have n4 := abs_nonneg a4
  have n5 := abs_nonneg a5
  have n6 := abs_nonneg a6
  have n7 := abs_nonneg a7
  have nT := abs_nonneg aT
  have hx1 : Fm.x1 < x := by linarith
  have hx3 : 3 ≤ x := by linarith
  have hone : 1 ≤ x := by linarith
  have b1 : x ≥ a1 := by linarith [le_abs_self a1]
  have b3 : x ≥ a3 := by linarith [le_abs_self a3]
  have b4 : x ≥ a4 := by linarith [le_abs_self a4]
  have b5 : x ≥ a5 := by linarith [le_abs_self a5]
  have b6 : x ≥ a6 := by linarith [le_abs_self a6]
  have b7 : x ≥ a7 := by linarith [le_abs_self a7]
  have bT : x ≥ aT := by linarith [le_abs_self aT]
  have hsx := Fm.L_x x i hx1
  have hse := Fm.L_eps x i
  have hX : XL (Fm.L x i).sc c6 := by
    unfold XL
    rw [hsx, hse]
    exact ⟨hx3, h1 x b1 hone, h3 x b3 hone, h4 x b4 hone, h5 x b5 hone, h6 x b6⟩
  have hS := Fm.sizes x hx1 i
  have hNum := numN_at (Fm.params x hx1 i) hS (by rw [hsx]; exact hx3)
  obtain ⟨sN, sM, sK, -, -, -, sQD, -, -, -, -, -, sLw, -⟩ := hS
  have hLa := winE sN sQD hX.1 hX.2.2.2.2.1 hX.2.2.2.2.2
  refine size_window_at_five (Fm.params x hx1 i) sN sM sK hLa (winP sQD) hNum.1 ?_ c6 hX
  exact winN' (hT2 x bT i) sN sLw CT ka (by rw [Fm.secondConstant_eq x i]; exact hCTle) hCT0 (by rw [hse]; exact hka1)
    (by rw [hse]; exact hka2) hX.1 (by rw [hsx]; exact h7 x b7)

end Formalism.MainNotions.Lnk

end

noncomputable section

namespace Formalism.MainNotions

open Formalism.MainNotions.Lnk

theorem linkGLOBAL {eps : ℝ} (Fm : FamP eps) (Cabs CH C0 eL : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 ≤ CH) (heL : 0 ≤ eL)
    (hCount : CountF Fm) (hSM : SlopesMF Fm)
    (hSN : LinkG Fm → LinkMu Fm → SlopesNF Fm)
    (hNF : NuFullF Fm) (hRank : J.MuRank Fm) (hRR : RRRankF Fm)
    (hFr : ChosenProviso Fm C0 → ChosenCode Fm C0 CH → LinkS Fm C0 → LinkIRR Fm → LinkDIV Fm Cabs CH → FrameF Fm CH)
    (hLoss : ∀ Cb : ℝ, 0 < Cb → ChosenTT Fm → ChosenBad Fm Cb → LinkG Fm → LossF Fm eL)
    (hChar : CharF Fm) (hCov : Fm.CoverAll) :
    LinkGLOBAL Fm Cabs CH C0 Cabs eL :=
  linkGLOBAL_of Fm Cabs CH C0 eL hCabs hCH heL hCount hSM hSN (fun lD => latF Fm lD hNF hRank hRR) (nodesF Fm) hFr hLoss hChar
    (fun cT2 => size_windows_of_thick_set Fm cT2) hCov

end Formalism.MainNotions

end
