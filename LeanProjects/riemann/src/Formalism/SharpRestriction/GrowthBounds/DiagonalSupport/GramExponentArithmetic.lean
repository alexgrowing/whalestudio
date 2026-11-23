import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickCore
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Imports
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.BinomCombFOnFinset
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.VBBMonomialOne
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SizeStep
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Mk

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

abbrev segmentLetterCount : ZMod Fr.J → ℕ := fun j => (Fr.LLset (segZ j)).card

variable (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]

def mkDt (dPl : TL Fr.J (segmentLetterCount Fr) r → ℕ) (th : ∀ j : ZMod Fr.J, Fin (segmentLetterCount Fr j + 1) → ℝ) (thL : ZMod Fr.J → Fin r → ℝ)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) (cP : ℕ) (hcP : 1 ≤ cP)
    (ga : (TL Fr.J (segmentLetterCount Fr) r × Fin r →₀ ℕ) → O) (hu : ∀ al, IsUnit (ga al))
    (hdig : ∀ k : ℕ, 1 ≤ k → ∀ ε : Bool, ∃ lam : (TL Fr.J (segmentLetterCount Fr) r × Fin r →₀ ℕ) →₀ O,
        (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 6 * k) ∧
        ∀ al : TL Fr.J (segmentLetterCount Fr) r × Fin r →₀ ℕ,
          geQ (vK p ((if ε then algebraMap O (KK O) (ga al) else (algebraMap O (KK O) (ga al))⁻¹) -
            binomCombF (K := KK O) lam al)) (k : ℝ)) :
    SignedChainData p O r Fr.J where
  nL := segmentLetterCount Fr
  sgn := fun j l => decide (Even (llPos Fr (segZ j) l.val))
  d := dPl
  gP := fun j _ => (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat
  nch := fun j => segmentLetterCount Fr j + 1
  chain := fun j i => {x | x.isRight} ∪ {x | ∃ l : Fin (segmentLetterCount Fr j), x = Sum.inl l ∧ l.val < i.val}
  chain_mono := by
    intro j a b hab
    have hab' : a.val < b.val := hab
    refine ⟨?_, ?_⟩
    · rintro x (hx | ⟨l, rfl, hl⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨l, rfl, lt_trans hl hab'⟩
    · intro h
      have hb := b.isLt
      have ha : a.val < segmentLetterCount Fr j := by omega
      have := h (Or.inr ⟨⟨a.val, ha⟩, rfl, hab'⟩ : Sum.inl ⟨a.val, ha⟩ ∈ _)
      rcases this with hx | ⟨l, hl, hl2⟩
      · simp at hx
      · have : l = ⟨a.val, ha⟩ := (Sum.inl.inj hl).symm
        subst this
        exact lt_irrefl _ hl2
  chain_w := fun j i m => Or.inl rfl
  th := th
  sl := fun j i => 3 / 8 * slU Fr p deg Y k (segmentLetterCount Fr) j i.val
  thL := thL
  thL_pos := hthL
  ga := ga
  ga_unit := hu
  ga_dig := hdig
  c := cP
  one_le_c := by exact_mod_cast hcP

end Mk

section Mk2

variable {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) [NeZero Fr.J] (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : ℕ} [NeZero K]

def JPOK' {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (LL : Letters (TL J nL r)) (dNo : TL J nL r → ℕ)
    (ka : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J nL r × Fin K) (KK O))) : Prop :=
  IsJProj (fun i : (Σ j : ZMod J, Fin (nL j + r + 1)) => glOps (KK O) K LL (NSet nL i.1 i.2.val))
    {fun i => ka i.1 i.2.val} e ∧
  (∀ F G, fock (e F) G = fock F (e G)) ∧
  (∀ F ∈ Pol (KK O) K dNo, e F ∈ Pol (KK O) K dNo ∧
    (InBB (O := O) p F → InBB (O := O) p (((p : KK O) ^ DnoOf (K := K) p nL dNo) • e F))) ∧
  ∀ F (i : (Σ j : ZMod J, Fin (nL j + r + 1))), e F ∈ isoSub (glOps (KK O) K LL (NSet nL i.1 i.2.val)) (ka i.1 i.2.val)

theorem jpok_iff {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) :
    JPOK p O Dt dNo ka e ↔ JPOK' p O Dt.nL Dt.trueLet dNo ka e := Iff.rfl

def updTh {J : ℕ} (Dt : SignedChainData p O r J) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) : SignedChainData p O r J :=
  { Dt with th := th, thL := thL, thL_pos := hthL }

theorem letters_ext {ι : Type} (A B : Letters ι) (h : A.vec = B.vec) : A = B := by
  cases A
  cases B
  simp only at h
  subst h
  rfl

theorem upd_trueLet {J : ℕ} (Dt : SignedChainData p O r J) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) : (updTh p O Dt th thL hthL).trueLet = Dt.trueLet := by
  apply letters_ext
  funext x
  rcases x with ⟨j, l | m⟩ <;> rfl

theorem jpok_upd {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) (dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ)
    (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))) (h : JPOK p O Dt dNo ka e) :
    JPOK p O (updTh p O Dt th thL hthL) dNo ka e :=
  (jpok_iff p O (updTh p O Dt th thL hthL) dNo ka e).2 (by
    rw [upd_trueLet]
    exact (jpok_iff p O Dt dNo ka e).1 h)

end Mk2

theorem exists_unit_coeff {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}
    (w : O) (hw : Irreducible w) (G : MvPolynomial σ (KK O)) (h0 : InWj w G 0) (h1 : ¬ InWj w G 1) :
    ∃ mo, vK p (G.coeff mo) = 0 := by
  by_contra hcon
  push Not at hcon
  apply h1
  intro mo
  obtain ⟨c, hc⟩ := h0 mo
  rw [pow_zero, one_mul] at hc
  by_cases hu : IsUnit c
  · exfalso
    apply hcon mo
    rw [hc, valuation_algebraMap_eq_alt p c hu.ne_zero, dvr_order_unit_eq_zero hu]
    simp
  · have hm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal c).2 hu
    rw [hw.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c', hc'⟩ := hm
    exact ⟨c', by rw [hc, hc', pow_one]⟩

theorem pickAt_of (p : ℕ) [hpF : Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O)) (hwi : Irreducible w)
    (hk : m + 1 = r + K) (Fr : Frames n' r) [NeZero Fr.J] (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ) (hcP : 1 ≤ cP)
    (d : Fin n' → ℕ) (Dn : ℝ)
    (hB : ∀ (j : ZMod Fr.J) (u : ℕ), u < segmentLetterCount Fr j + r →
      3 / 8 * slU Fr p deg Y (r + K) (segmentLetterCount Fr) j u < Bo p Fr deg (segZ j) (posU Fr (segmentLetterCount Fr j) (segZ j) u) / 2)
    (hDig : DigFacts Fr p O hk (segmentLetterCount Fr) d)
    (hJP : ∀ Dt : SignedChainData p O r Fr.J, JPAt (K := K) p O Dt)
    (hNo : ∀ Dt : SignedChainData p O r Fr.J, NoAt (K := K) p O Fr cP Dt)
    (hGa : GaAt (K := K) p O Fr (segmentLetterCount Fr))
    (hSz : SizeAt (K := K) p Fr (segmentLetterCount Fr) d Dn)
    (G : MvPolynomial (TV n' (m + 1)) (KK O)) (hdeg : HasMultideg G d) (h0 : InWj w G 0) (h1 : ¬ InWj w G 1)
    (hMem : MemAt p O hk Fr deg Y N₁ G' cP G) :
    PickAt p O hk Fr deg Y N₁ G' cP d (kapFl p (m + 1) d) Dn G := by
  have hGint : CoefGe p G 0 := by
    intro mo
    obtain ⟨c, hc⟩ := h0 mo
    rw [hc]
    exact geQ_alg S _

  obtain ⟨mo0, hmo0⟩ := exists_unit_coeff (p := p) w hwi G h0 h1
  have hmo0s : mo0 ∈ G.support := by
    rw [mem_support_iff]
    intro h
    rw [h, valuation_zero_alt] at hmo0
    exact WithTop.top_ne_zero hmo0
  have hmo0d : ∀ s, multideg mo0 s = d s := ((mem_restrictSupport_iff (KK O)).1 hdeg) hmo0s
  obtain ⟨hBlk, hcoef, hdp, hdn, hfact⟩ := (hDig G hdeg).2.2 mo0 hmo0s
  generalize classOf Fr p hk (segmentLetterCount Fr) mo0 = rho at hBlk hcoef hfact
  generalize blkPl Fr p hk (segmentLetterCount Fr) mo0 = dPl at hBlk hcoef hfact hdp
  generalize blkNo Fr p hk (segmentLetterCount Fr) mo0 = dNo at hBlk hcoef hfact hdn
  generalize plMon Fr p hk (segmentLetterCount Fr) mo0 = bp0 at hcoef hfact hdp
  generalize noMon Fr p hk (segmentLetterCount Fr) mo0 = bn0 at hcoef hfact hdn
  obtain ⟨hgnU, hgpU, ga, hgau, hgaeq, hgadig⟩ := hGa rho hBlk.1

  obtain ⟨thF, hthF⟩ : ∃ thF : (ZMod Fr.J → ℕ → Fin K → ℤ) → ∀ j : ZMod Fr.J, Fin (segmentLetterCount Fr j + 1) → ℝ,
      ∀ ka j i, thF ka j i = thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) (segmentLetterCount Fr) K ka j i.val -
        slU Fr p deg Y (r + K) (segmentLetterCount Fr) j i.val / 8 := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨thLF, hthLF0⟩ : ∃ thLF : (ZMod Fr.J → ℕ → Fin K → ℤ) → ZMod Fr.J → Fin r → ℝ,
      ∀ ka j mm, thLF ka j mm = thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) (segmentLetterCount Fr) K ka j
          (segmentLetterCount Fr j + (r - 1 - mm.val)) - 3 / 8 * slU Fr p deg Y (r + K) (segmentLetterCount Fr) j (segmentLetterCount Fr j + (r - 1 - mm.val)) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hthLF : ∀ ka j (mm : Fin r), mm.val + 2 ≤ r → 0 < thLF ka j mm := by
    intro ka j mm hm
    rw [hthLF0]
    exact thL_arith _ _ _ (hB j (segmentLetterCount Fr j + (r - 1 - mm.val)) (by omega)) (le_max_left _ _)

  obtain ⟨ka, e, hJPOK, hvle⟩ := hJP (mkDt Fr p deg Y (r + K) O dPl (thF fun _ _ _ => 0) (thLF fun _ _ _ => 0)
    (hthLF fun _ _ _ => 0) cP hcP ga hgau hgadig) dNo _ ((hDig G hdeg).2.1 rho dPl dNo bp0)
  have hJPOK2 := jpok_upd p O (mkDt Fr p deg Y (r + K) O dPl (thF fun _ _ _ => 0) (thLF fun _ _ _ => 0)
    (hthLF fun _ _ _ => 0) cP hcP ga hgau hgadig) (thF ka) (thLF ka) (hthLF ka) dNo ka e hJPOK
  have hTP : SignedChainDegreeCondition p O Fr deg Y N₁ G' cP
      (updTh p O (mkDt Fr p deg Y (r + K) O dPl (thF fun _ _ _ => 0) (thLF fun _ _ _ => 0)
      (hthLF fun _ _ _ => 0) cP hcP ga hgau hgadig) (thF ka) (thLF ka) (hthLF ka)) dPl ka :=
    ⟨⟨rfl, fun _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun j i => hthF ka j i,
      fun j mm _ => hthLF0 ka j mm⟩, rfl, fun _ _ => rfl⟩
  exact pick_core p O S w hw2 hk Fr deg Y N₁ G' cP d Dn
    (updTh p O (mkDt Fr p deg Y (r + K) O dPl (thF fun _ _ _ => 0) (thLF fun _ _ _ => 0)
      (hthLF fun _ _ _ => 0) cP hcP ga hgau hgadig) (thF ka) (thLF ka) (hthLF ka)) dPl dNo ka rho hTP hBlk hDig
    hgnU hgpU hgaeq e hJPOK2 (hNo _) hSz G hdeg
    hGint hMem mo0 hmo0 hmo0d bp0 bn0 hcoef hdp hdn hfact hvle

theorem pickStep_all (D : Formalism.BasicNotions.D7) : ∃ CDn C₁ : ℝ, 0 < CDn ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, PickStep C CDn CLa := by
  obtain ⟨CDn, C₁, h1, h2, hS⟩ := sizeStep
  refine ⟨CDn, C₁, h1, h2, fun C hC CLa => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r hpF _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K
    _ _ hk F nb B hD G hdeg hG0 hG1 hMem
  have S : UniformizedDVR p O := dvrOfStd hD.1
  have hK : CharZero (KK O) := dvr_fraction_field_char_zero hpF.out S
  have hR : AdmissibleDVR p n' O := Formalism.MainNotions.flipOneThree.admissible_dvr_of_unramified_quadratic_setting hD.1
  have hV := hD.2.2.1.2.1
  have hJ1 : 1 ≤ F.J := hV.1
  have : NeZero F.J := ⟨by omega⟩
  have h13 : 13 ≤ p := hD.2.1.1
  have hr2 : 2 ≤ r := hD.2.1.2.1
  obtain ⟨hSz, hB, hcP, _⟩ := hS C hC CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K hk F nb
    B hD
  have hd : ∀ s, s ∉ F.TT → dT TT lam0 s = 0 := by
    intro s hs
    rw [hD.2.2.1.1] at hs
    unfold dT
    rw [if_neg hs]
  exact pickAt_of p O S w hD.1.1.w_sq hD.1.2.1 hk F (flatDeg lam0) Y _ _ _ hcP (dT TT lam0) _ hB
    (digFacts F p hpF.out O hk (segmentLetterCount F) L₁ _ hV (by omega) rfl (fun _ => rfl) (dT TT lam0) hd)
    (fun Dt dNo y _ => by
      obtain ⟨ka, e, a1, a2, a3, a4, a5⟩ := restJP D K Dt S hR dNo y
      exact ⟨ka, e, ⟨a1, a3, a4, a5⟩, a2⟩)
    (fun Dt => noAt D p O S w hD.1.1.w_sq (digAbs D p hpF.out (by omega) S) F _ Dt)
    (gaAt D p hpF.out (by omega) S F (segmentLetterCount F)) hSz G hdeg hG0 hG1 hMem

theorem restPick (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestPick D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨CDn, C₁, h1, h2, h⟩ := pickStep_all D
  exact ⟨CDn, C₁, h1, h2, fun C hC => h C hC CLa⟩

end Formalism.MainNotions.Proposition5Numerics
