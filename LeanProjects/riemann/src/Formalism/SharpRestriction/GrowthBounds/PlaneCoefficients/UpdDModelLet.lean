import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Upd

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}

def updD (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) : SignedChainData p O r J :=
  SignedChainData.mk Dt.nL Dt.sgn d Dt.gP Dt.nch Dt.chain Dt.chain_mono Dt.chain_w th Dt.sl thL h Dt.ga Dt.ga_unit Dt.ga_dig
    Dt.c Dt.one_le_c

section With

variable (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m)

theorem updD_modelLet : (updD Dt d th thL h).modelLet = Dt.modelLet := by
  unfold SignedChainData.modelLet
  congr 1
  funext x
  cases x <;> rfl

theorem updD_trueLet : (updD Dt d th thL h).trueLet = Dt.trueLet := by
  unfold SignedChainData.trueLet
  congr 1
  funext x
  obtain ⟨j, s⟩ := x
  cases s <;> rfl

theorem updD_levToML (j) : (updD Dt d th thL h).levToML j = Dt.levToML j := by
  funext x
  cases x <;> rfl

theorem updD_chainML (j i) : (updD Dt d th thL h).chainML j i = Dt.chainML j i := by
  unfold SignedChainData.chainML
  rw [updD_levToML]
  rfl

theorem updD_TSet (j i) : (updD Dt d th thL h).TSet j i = Dt.TSet j i := rfl

theorem updD_digOK (rho) : (updD Dt d th thL h).digOK rho = Dt.digOK rho := rfl

theorem updD_liftVar : (updD Dt d th thL h).liftVar = Dt.liftVar := by
  funext x
  obtain ⟨⟨j, s⟩, a⟩ := x
  cases s <;> rfl

theorem updD_liftExp : (updD Dt d th thL h).liftExp = Dt.liftExp := by
  funext mo x
  obtain ⟨⟨j, s⟩, a⟩ := x
  cases s <;> rfl

theorem updD_Fdig (rho F) : (updD Dt d th thL h).Fdig rho F = Dt.Fdig rho F := by
  unfold SignedChainData.Fdig
  rw [updD_digOK, updD_liftVar, updD_liftExp]
  rfl

theorem updD_normE (K : ℕ) [NeZero K] [NeZero J] : normE p K (updD Dt d th thL h) = normE p K Dt := by
  unfold normE
  rw [updD_trueLet]
  rfl

theorem valS_congr3' {Kf : Type} [Field Kf] {ι : Type} {r : ℕ} [NeZero r] {LL LL' : Letters ι} {S S' : Set ι}
    {F F' : MvPolynomial (ι × Fin r) Kf} (h1 : LL = LL') (h2 : S = S') (h3 : F = F') :
    valS LL S F = valS LL' S' F' := by
  subst h1 h2 h3
  rfl

end With

variable [NeZero J] [NeZero r]

def XXg (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) : Prop :=
  F ∈ Pol (KK O) r d ∧
  (∀ (rho : (ZMod J × Fin r) × Fin r → ℕ) (j : ZMod J) (i : Fin (Dt.nch j)),
    geZ (valS Dt.modelLet (Dt.chainML j i) (Dt.Fdig rho F)) (th j i)) ∧
  ∀ (j : ZMod J) (m : Fin r), m.val + 2 ≤ r → geZ (valS Dt.trueLet (Dt.TSet j m) F) (thL j m)

theorem XX_iff (Dt : SignedChainData p O r J) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    Dt.XX F ↔ XXg Dt Dt.d Dt.th Dt.thL F := Iff.rfl

theorem updD_XX (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (hF : (updD Dt d th thL h).XX F) : XXg Dt d th thL F := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · have e : valS Dt.modelLet (Dt.chainML j i) (Dt.Fdig rho F) =
        valS (updD Dt d th thL h).modelLet ((updD Dt d th thL h).chainML j i) ((updD Dt d th thL h).Fdig rho F) :=
      valS_congr3' (updD_modelLet Dt d th thL h).symm (updD_chainML Dt d th thL h j i).symm
        (updD_Fdig Dt d th thL h rho F).symm
    rw [e]
    exact h2 rho j i
  · have e : valS Dt.trueLet (Dt.TSet j m) F =
        valS (updD Dt d th thL h).trueLet ((updD Dt d th thL h).TSet j m) F :=
      valS_congr3' (updD_trueLet Dt d th thL h).symm (updD_TSet Dt d th thL h j m).symm rfl
    rw [e]
    exact h3 j m hm

end Upd

section Lev

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def Base (Dt : SignedChainData p O r J) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val})

def ThLe (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (Dt : SignedChainData p O r J) (ka : ZMod J → ℕ → Fin K → ℤ)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) : Prop :=
  (∀ j (i : Fin (Dt.nch j)), th j i ≤ thStar Fr p deg Y k mS Dt.nL K ka j i.val -
    sc * slU Fr p deg Y k Dt.nL j i.val - loss (segZ j) i.val) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    thL j mm ≤ thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      sL * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val)) - loss (segZ j) (Dt.nL j + (r - 1 - mm.val))

end Lev

def MemLev (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) (th : ∀ j, Fin (Dt.nch j) → ℝ)
    (thL : ZMod J → Fin r → ℝ), (∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm) →
    ThLe Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL loss Dt ka th thL →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        XXg Dt dPl th thL (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

theorem memAtLe_iff (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    MemAtLe sc sL loss p O hk Fr deg Y N₁ G' cP F ↔
      ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), Base Fr p Dt → MemLev sc sL loss p O hk Fr deg Y N₁ G' cP Dt F := by
  constructor
  · intro h J _ Dt hB dPl dNo ka th thL hpos hT rho e he nu
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
    exact updD_XX Dt dPl th thL hpos _ (h J (updD Dt dPl th thL hpos) dPl dNo ka ⟨b1, b2, b3, rfl, b4, b5, b6, hT.1, hT.2⟩ rho e
      (by rw [updD_normE]; exact he) nu)
  · intro h J _ Dt dPl dNo ka hT rho e he nu
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hT
    subst t4
    exact h J Dt ⟨t1, t2, t3, t5, t6, t7⟩ Dt.d dNo ka Dt.th Dt.thL Dt.thL_pos ⟨t8, t9⟩ rho e he nu

section TotallyRealRoots

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def cost1 (s : Fin n') (jz : ℤ) (u : ℕ) : ℝ := if touchT Fr jz u s then 1 else 0

theorem opCost_eq (s : Fin n') (jz : ℤ) (u : ℕ) : opCost Fr s jz u = cost1 Fr s jz u + cost1 Fr s jz u := by
  unfold opCost cost1
  split_ifs <;> norm_num

end TotallyRealRoots

end Formalism.MainNotions.PairMembershipBlocks
