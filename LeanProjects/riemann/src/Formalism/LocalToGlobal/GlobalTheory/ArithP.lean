import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation
import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Minkowski
import Development.AutomorphicArithmetic.ConductorsKronecker.Imports
import Development.AutomorphicArithmetic.ConductorsKronecker.kronecker
import Development.AutomorphicArithmetic.ConductorsKronecker.InertiaD
import Development.AutomorphicArithmetic.ConductorsKronecker.IsInertIff
import Development.AutomorphicArithmetic.OrbitLabellings.EvenAddOrderOfHPOfPowLe

noncomputable section

open scoped BigOperators
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace Formalism.L2.GlobalTheoryTheory.Arith

abbrev baseOf (D : D7) (L : SizeData₂ D) : Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

abbrev insOf {D : D7} {L : SizeData₂ D} (X : G.Inst D L) : Ins (baseOf D L) :=
  { bs := X.bs, kapI := X.kapI, ep := X.ep }

section Rfl

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (a b : G.HH D → ℤ) (p j : ℕ) (t0 : G.HH D)

theorem rho_eq : G.rho D K L.sc = (baseOf D L).rho K := rfl

end Rfl

section Host

open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

end Host

section Origins

variable {φ : Formalism.HC.Frame}

end Origins

namespace Loc

variable (B : Base) (I : Ins B) (K : G.Consts) (a b : B.H → ℤ) (h h' : B.H) (p : ℕ)

end Loc

section HRecord

open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost

end HRecord

abbrev datumOf (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) : NumDatum where
  R := D.R
  sc := L.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := Del
  h0 := h0
  hc := fun z => D.hc (tauPl D z)

structure InstanceCompatible {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (Ce : ℝ) (Del h0 : ℕ) : Prop where
  del : D.s.Del = (Del : ℚ)
  eta : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)
  bs : ∀ h t, X.bs h t = bsH h t
  ep : G.EpDef X Ce
  kap : G.KapIDef X K
  fills : ∀ j ∈ SizeData₂.lifts D, ∀ z, G.fill X (G.bL L) j z = wPl D j z

section Joint

variable {D : D7} {L : SizeData₂ D} (Del h0 : ℕ)

theorem eTau_tauPl (z : Bool × G.HH D) : ((D.eTau (tauPl D z) : D.R.Psi) : D.R.GG) = G.plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

variable {Del h0} {X : G.Inst D L} {K : G.Consts} {Ce : ℝ}

theorem Sc_datumOf (hT : InstanceCompatible X K Ce Del h0) : (datumOf D L Del h0).Sc = L.Sc := by
  rw [L.Sc_eq, hT.del]
  unfold NumDatum.Sc
  simp

theorem eta_datumOf (hT : InstanceCompatible X K Ce Del h0) : (datumOf D L Del h0).eta = L.etaSz := by
  rw [hT.eta]; rfl

theorem ins_eq (hT : InstanceCompatible X K Ce Del h0) : ins (baseOf D L) K Ce = insOf X := by
  have h1 : (bsH : G.HH D → G.HH D → G.HH D) = X.bs := funext fun h => funext fun t => (hT.bs h t).symm
  have h2 : (fun p n' TT a b => sInf (Loc.kapISet (baseOf D L) K p n' TT a b)) = X.kapI := by
    funext p n' TT a b
    exact (hT.kap p n' TT a b).symm
  have h3 : (fun p : ℕ => ⌈Ce * ((baseOf D L).R.f : ℝ) * ((baseOf D L).R.k : ℝ) ^ 2 * Real.logb p (baseOf D L).sc.a⌉₊) = X.ep := by
    funext p
    exact (hT.ep p).symm
  unfold ins
  rw [h2, h3]
  show Ins.mk bsH _ _ = _
  rw [h1]

end Joint

section Main

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ} {X : G.Inst D L} {C : Cst}

abbrev mkB (D : D7) (L : SizeData₂ D) (S η : ℝ) : Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := S, eta := η }

theorem transport {α : Sort*} (hT : InstanceCompatible X C.K C.Ce Del h0) (Φ : ∀ S η : ℝ, Ins (mkB D L S η) → α) :
    Φ (datumOf D L Del h0).Sc (datumOf D L Del h0).eta (ins _ C.K C.Ce) = Φ L.Sc L.etaSz (insOf X) := by
  have key : ∀ S η, S = L.Sc → η = L.etaSz →
      Φ S η (ins _ C.K C.Ce) = Φ L.Sc L.etaSz (ins _ C.K C.Ce) := by
    rintro _ _ rfl rfl; rfl
  rw [key _ _ (Sc_datumOf hT) (eta_datumOf hT)]
  exact congrArg _ (ins_eq hT)

variable (hT : InstanceCompatible X C.K C.Ce Del h0) (a b : G.HH D → ℤ) {p : ℕ} (hp : p.Prime)

include hT hp

end Main

section JointEstimate

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ} {X : G.Inst D L} {C : Cst}

theorem fill_eq_wPl₂ {K : G.Consts} (w : D.what₂.places.Pl) (hF : G.ParametersFill X K w) :
    ∀ j ∈ SizeData₂.lifts D, ∀ z, G.fill X (G.bL L) j z = wPl D j z :=
  fun j hj z => hF.1 j hj (tauPl D z) z (eTau_tauPl z)

variable (hT : InstanceCompatible X C.K C.Ce Del h0) (w : D.what₂.places.Pl) (hF : G.ParametersFill X C.K w)

include hT hF

end JointEstimate

section DGamma

variable (N : NumDatum)

theorem DGamM_pos : 0 < DGamM N := minkM_pos _

theorem prime_le_of_dvd_DGamM {p : ℕ} (hp : p.Prime) (h : p ∣ DGamM N) : p ≤ 2 * N.R.f * N.Nm + 1 :=
  prime_le_of_dvd_minkM hp h

theorem log_DGamM_le : Real.log (DGamM N : ℝ) ≤ 12 * N.R.f * N.Nm * Real.log ((N.R.f : ℝ) * N.Nm) := by
  have hy : (2 : ℝ) ≤ (N.R.f : ℝ) * N.Nm := by exact_mod_cast N.R.two_le_fN
  have h1 := log_minkM_le_two (2 * N.R.f * N.Nm)
  have e : ((2 * N.R.f * N.Nm : ℕ) : ℝ) = 2 * ((N.R.f : ℝ) * N.Nm) := by push_cast; ring
  rw [e] at h1
  have e2 : (2 : ℝ) * (2 * ((N.R.f : ℝ) * N.Nm)) = 2 * 2 * ((N.R.f : ℝ) * N.Nm) := by ring
  have h2 : Real.log (2 * (2 * ((N.R.f : ℝ) * N.Nm))) = Real.log 2 + Real.log 2 + Real.log ((N.R.f : ℝ) * N.Nm) := by
    rw [e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 2 ≤ Real.log ((N.R.f : ℝ) * N.Nm) := Real.log_le_log (by norm_num) hy
  rw [h2] at h1
  have h4 : 2 * (2 * ((N.R.f : ℝ) * N.Nm)) * (Real.log 2 + Real.log 2 + Real.log ((N.R.f : ℝ) * N.Nm)) ≤
      2 * (2 * ((N.R.f : ℝ) * N.Nm)) * (3 * Real.log ((N.R.f : ℝ) * N.Nm)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc Real.log (DGamM N : ℝ)
      ≤ 2 * (2 * ((N.R.f : ℝ) * N.Nm)) * (3 * Real.log ((N.R.f : ℝ) * N.Nm)) := h1.trans h4
    _ = 12 * N.R.f * N.Nm * Real.log ((N.R.f : ℝ) * N.Nm) := by ring

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ}

end DGamma

section Admissible

variable {N : NumDatum} {Lv : Lev N}

theorem Lev.dgamOk_of_dvd (h : Lv.DGam ∣ DGamM N) : Lev.DGamOk N Lv := by
  have hpos : 0 < Lv.DGam := Nat.pos_of_dvd_of_pos h (DGamM_pos N)
  refine ⟨hpos, fun p hp hd => prime_le_of_dvd_DGamM N hp (hd.trans h), le_trans ?_ (log_DGamM_le N)⟩
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.le_of_dvd (DGamM_pos N) h)

theorem Lev.DGamLcm.unique {Lv' : Lev N} {ord : Set ℕ} (h : Lev.DGamLcm N Lv ord) (h' : Lev.DGamLcm N Lv' ord) :
    Lv.DGam = Lv'.DGam := Nat.dvd_antisymm (h.2 _ h'.1) (h'.2 _ h.1)

theorem Lev.DGamLcm.ok {ord : Set ℕ} (h : Lev.DGamLcm N Lv ord) (hM : ∀ a ∈ ord, a ∣ DGamM N) : Lev.DGamOk N Lv :=
  Lev.dgamOk_of_dvd (h.2 _ hM)

end Admissible

section Twice

variable (N : NumDatum) (C : Cst)

end Twice

open Classical in

structure LevelCompatible {D : D7} {L : SizeData₂ D} {Del h0 : ℕ} (EX : ErrX D) (Lv : Lev (datumOf D L Del h0)) (sd : D.what₂.LL) :
    Prop where
  ws : Lv.Ws = Finset.univ.image (fun u : D.what₂.Word => (D.s.letter u : Code (datumOf D L Del h0)))
  T : ∀ u, Lv.T (D.s.letter u) = (D.mem u).A.T
  sdOk : SdOk (datumOf D L Del h0) sd
  piT : ∀ u τ, tauLL D τ (EX.piT u : D.host.E) = elt sd (Lv.piT (D.s.letter u))
  piG : ∀ i τ, tauPib EX i τ = eltBar sd (Lv.piG i)
  DGam : (D.mem D.u₀).C.DGam = Lv.DGam

section Drop

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ} {X : G.Inst D L} {C : Cst} {EX : ErrX D}
  {Lv : Lev (datumOf D L Del h0)} {sd : D.what₂.LL}

def ordRec (D : D7) : Set ℕ :=
  {a | ∃ u μ i, i ≤ D.R.m ∧ ∃ c : (D.chTw u μ).cls i, a = Nat.card ((D.chTw u μ).stab i c)}

end Drop

section Places

variable {K : Type} [Field K] [NumberField K]

theorem pOf_mem (w : HeightOneSpectrum (𝓞 K)) : ((pOf w : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

end Places

section Losses

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ}

variable (hDel : D.s.Del = (Del : ℚ))

include hDel

end Losses

section Assembly

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ} {X : G.Inst D L} {C : Cst} {EX : ErrX D}
  {Lv : Lev (datumOf D L Del h0)} {sd : D.what₂.LL}

end Assembly

section Support

variable {K : Type} [Field K] [NumberField K]

theorem pOf_ne_zero (w : HeightOneSpectrum (𝓞 K)) : pOf w ≠ 0 := by
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  exact CharP.char_ne_zero_of_finite (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))

theorem finite_over (S : Finset ℕ) : {w : HeightOneSpectrum (𝓞 K) | pOf w ∈ S}.Finite := by
  have h1 : ∀ p ∈ (S.filter (· ≠ 0) : Finset ℕ),
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 K)}}.Finite := by
    intro p hp
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (Finset.mem_filter.1 hp).2
  refine (Set.Finite.biUnion (Finset.finite_toSet (S.filter (· ≠ 0))) h1).subset ?_
  intro w hw
  rw [Set.mem_iUnion₂]
  exact ⟨pOf w, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hw, pOf_ne_zero w⟩),
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 (pOf_mem w))⟩

theorem mem_supp (N : NumDatum) (Lv : Lev N) (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ supp N Lv K ↔ pOf w ∈ suppP N Lv := by
  unfold supp
  rw [dif_pos (finite_over _), Set.Finite.mem_toFinset]
  rfl

end Support

section Vanish

variable (N : NumDatum) (C : Cst) (Lv : Lev N)

section

variable {K : Type} [Field K] [NumberField K]

end

end Vanish

section Totals

variable {D : D7} {L : SizeData₂ D} {Del h0 : ℕ}

end Totals

section Family

variable {eps : ℝ} (Fm : FamP eps)

def cstOf : Cst := ⟨Fm.GK, Fm.cX.Ce, Fm.cX.err, Fm.Cr⟩

variable {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x)

structure NewTies (Del h0 : ℕ) (Lv : Lev (datumOf (Fm.D x i) (Fm.L x i) Del h0)) (sd : (Fm.D x i).what₂.LL) : Prop where
  del : (Fm.D x i).s.Del = (Del : ℚ)
  eta : (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (h0 : ℝ)
  bs : ∀ h t, (Fm.Gx x i).bs h t = bsH h t
  lev : LevelCompatible (Fm.ex x hx i).errX Lv sd

variable {Del h0 : ℕ} {Lv : Lev (datumOf (Fm.D x i) (Fm.L x i) Del h0)} {sd : (Fm.D x i).what₂.LL}
  (hN : NewTies Fm hx i Del h0 Lv sd)

include hN

end Family

section Model

open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.characterSumData Formalism.D5

variable (N : NumDatum)

theorem isInert_iff (p : ℕ) :
    IsInert (host N) p ↔ p.Prime ∧ (N.cls p = PrimeClass.inertClass ∨ N.cls p = PrimeClass.signal) := by
  refine (UpperTheory.GL.isInert_iff N.H p).trans (and_congr_right fun hp => ?_)
  unfold NumDatum.cls
  rw [primeClass_eq_inert_iff_symbols hp, primeClass_eq_signal_iff' hp]
  constructor
  · rintro ⟨h1, h2⟩
    rcases N.H.toHostRaw.psAt_eq_one_or (hp.coprime_iff_not_dvd.2 h1) with h3 | h3
    · exact Or.inr ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩
  · rintro (h | h) <;> exact ⟨h.1, h.2.1⟩

theorem sum_lifts (m : ℕ) (F : ℕ → ℝ) : ∑ j : Fin m, F (j.1 + 1) = ∑ j ∈ Finset.Icc 1 m, F j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => F (j + 1)) m]
  refine Finset.sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    have := Finset.mem_range.1 hj
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro a _ b _ h
    omega
  · intro b hb
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hb
    exact ⟨b - 1, Finset.mem_range.2 (by omega), by omega⟩
  · intro _ _
    rfl

variable {N}

end Model

section Reading

open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LHost Formalism.D5

variable {D : D7} (L : SizeData₂ D) (Del h0 : ℕ)

end Reading

end Formalism.L2.GlobalTheoryTheory.Arith

end
