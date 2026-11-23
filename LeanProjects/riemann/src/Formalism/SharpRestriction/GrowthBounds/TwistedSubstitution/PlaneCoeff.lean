import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestXiPOfNS

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting

section Joint

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def jIso {ι : Type*} (E : ι → GLOps n K V) (lam : ι → Fin n → ℤ) : Submodule K V :=
  ⨅ i, isoSub (E i) (lam i)

def IsJProj {ι : Type*} (E : ι → GLOps n K V) (T : Set (ι → Fin n → ℤ)) (e : Module.End K V) : Prop :=
  (∀ lam ∈ T, ∀ x ∈ jIso E lam, e x = x) ∧ ∀ mu, mu ∉ T → ∀ x ∈ jIso E mu, e x = 0

end Joint

section Letters

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def segZ {J : ℕ} (j : ZMod J) : ℤ := (j.val : ℤ)

def llPos (j : ℤ) (l : ℕ) : ℤ := ((Fr.LLset j).sort (· ≤ ·)).getD l 0

def posU (nLj : ℕ) (j : ℤ) (u : ℕ) : ℤ := if u < nLj then llPos Fr j u else Fr.fr j (u - nLj)

def posTL {J : ℕ} {nL : ZMod J → ℕ} : TL J nL r → ℤ
  | ⟨j, Sum.inl l⟩ => llPos Fr (segZ j) l.val
  | ⟨j, Sum.inr m⟩ => Fr.fr (segZ j) (r - 1 - m.val)

def lowP (p : ℕ) {J : ℕ} {nL : ZMod J → ℕ} (x : TL J nL r) : ℕ :=
  p ^ Fr.dist (segZ x.1) (posTL Fr x)

def NSet {J : ℕ} (nL : ZMod J → ℕ) (j : ZMod J) (u : ℕ) : Set (TL J nL r) :=
  {x | ∃ l : Fin (nL j), x = ⟨j, Sum.inl l⟩ ∧ l.val < u} ∪
    {x | ∃ m : Fin r, x = ⟨j, Sum.inr m⟩ ∧ nL j + (r - 1 - m.val) < u}

end Letters

section Level

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def plVar (x : TL J nL r) (a : Fin r) : TV n' (m + 1) := (posOf n' (posTL Fr x), Fin.cast hk.symm (Fin.castAdd K a))

def noVar (x : TL J nL r) (b : Fin K) : TV n' (m + 1) := (posOf n' (posTL Fr x), Fin.cast hk.symm (Fin.natAdd r b))

def plMon (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => mo (plVar Fr hk nL v.1 v.2) / lowP Fr p v.1

def noMon (mo : TV n' (m + 1) →₀ ℕ) : TL J nL r × Fin K →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => mo (noVar Fr hk nL v.1 v.2) / lowP Fr p v.1

def InLow (rho : TL J nL r × Fin (r + K) → ℕ) (mo : TV n' (m + 1) →₀ ℕ) : Prop :=
  (∀ x (a : Fin r), mo (plVar Fr hk nL x a) % lowP Fr p x = rho (x, Fin.castAdd K a)) ∧
  ∀ x (b : Fin K), mo (noVar Fr hk nL x b) % lowP Fr p x = rho (x, Fin.natAdd r b)

def InBlock (dPl dNo : TL J nL r → ℕ) (mo : TV n' (m + 1) →₀ ℕ) : Prop :=
  (∀ x, ∑ a : Fin r, mo (plVar Fr hk nL x a) / lowP Fr p x = dPl x) ∧
  ∀ x, ∑ b : Fin K, mo (noVar Fr hk nL x b) / lowP Fr p x = dNo x

def levImg (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    MvPolynomial (TL J nL r × Fin r) (MvPolynomial (TL J nL r × Fin K) (KK O)) :=
  ∑ mo ∈ F.support.filter (fun mo => InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo),
    monomial (plMon Fr p hk nL mo) (monomial (noMon Fr p hk nL mo) (F.coeff mo))

end Level

def oneT {σ τ : Type} {Kf : Type} [Field Kf] (e : Module.End Kf (MvPolynomial τ Kf))
    (F : MvPolynomial σ (MvPolynomial τ Kf)) : MvPolynomial σ (MvPolynomial τ Kf) :=
  ∑ mo ∈ F.support, monomial mo (e (F.coeff mo))

def planeCoeff {σ τ : Type} {Kf : Type} [Field Kf] (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) :
    MvPolynomial σ Kf :=
  ∑ mo ∈ F.support, monomial mo ((F.coeff mo).coeff nu)

section Comparison₂

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {J : ℕ} (nL : ZMod J → ℕ) (K : ℕ) [NeZero K]

def thStar (ka : ZMod J → ℕ → Fin K → ℤ) (j : ZMod J) (u : ℕ) : ℝ :=
  let x := posU Fr (nL j) (segZ j) u
  let B := Bo p Fr deg (segZ j) x
  let s : ℝ := (sl p Fr deg Y k (segZ j) x : ℝ)
  let t1 : ℝ := if Even x then (ka j (u + 1) 0 : ℝ) + mS + s else B / 2
  let t2 : ℝ := if 1 ≤ u ∧ ¬ Even (posU Fr (nL j) (segZ j) (u - 1)) then (ka j (u - 1) 0 : ℝ) + mS + s else B / 2
  max (B / 2) (max t1 t2)

def slU (j : ZMod J) (u : ℕ) : ℝ := (sl p Fr deg Y k (segZ j) (posU Fr (nL j) (segZ j) u) : ℝ)

end Comparison₂

section Tie2

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def Tied (Dt : SignedChainData p O r J) (dPl : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  Dt.d = dPl ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val}) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.th j i = thStar Fr p deg Y k mS Dt.nL K ka j i.val - slU Fr p deg Y k Dt.nL j i.val / 8) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    Dt.thL j mm = thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      3 / 8 * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val))

def normE [NeZero J] (Dt : SignedChainData p O r J) :
    (Σ j : ZMod J, Fin (Dt.nL j + r + 1)) → GLOps K (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O)) :=
  fun i => glOps (KK O) K Dt.trueLet (NSet Dt.nL i.1 i.2.val)

end Tie2

def MemAt (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
    (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    Tied Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

end Formalism.MainNotions.TestSideWords
