import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.UpdDModelLet
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def derN {τ Kf : Type} [Field Kf] (w : τ) : Module.End Kf (MvPolynomial τ Kf) := (pderiv w).toLinearMap

def mulN {τ Kf : Type} [Field Kf] (w : τ) : Module.End Kf (MvPolynomial τ Kf) := LinearMap.mulLeft Kf (X w)

def TrDerPl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K)
    (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (x0 : TL J nL r),
    (∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0) →
    ∀ (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
      (F : MvPolynomial (TV n' (m + 1)) (KK O)),
    ∃ (c1 c2 c3 : KK O) (rho1 rho2 : TL J nL r × Fin (r + K) → ℕ),
      levImg Fr p hk nL rho dPl dNo (pderiv (plVar Fr hk nL x0 a) F) =
        c1 • levImg Fr p hk nL rho1 dPl dNo F +
        c2 • (X (x0, a) * pderiv (x0, a) (levImg Fr p hk nL rho1 dPl dNo F)) +
        c3 • pderiv (x0, a) (levImg Fr p hk nL rho2 (Function.update dPl x0 (dPl x0 + 1)) dNo F)

def TrDerNo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K)
    (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (x0 : TL J nL r),
    (∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0) →
    ∀ (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
      (F : MvPolynomial (TV n' (m + 1)) (KK O)),
    ∃ (c1 c2 c3 : KK O) (rho1 rho2 : TL J nL r × Fin (r + K) → ℕ),
      levImg Fr p hk nL rho dPl dNo (pderiv (noVar Fr hk nL x0 b) F) =
        c1 • levImg Fr p hk nL rho1 dPl dNo F +
        c2 • oneT (mulN (x0, b) * derN (x0, b)) (levImg Fr p hk nL rho1 dPl dNo F) +
        c3 • oneT (derN (x0, b)) (levImg Fr p hk nL rho2 dPl (Function.update dNo x0 (dNo x0 + 1)) F)

def TrMulPl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K)
    (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (x0 : TL J nL r),
    (∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0) →
    ∀ (a : Fin r) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
      (F : MvPolynomial (TV n' (m + 1)) (KK O)),
    ∃ (c1 c2 : KK O) (rho1 rho2 : TL J nL r × Fin (r + K) → ℕ), (dPl x0 = 0 → c2 = 0) ∧
      levImg Fr p hk nL rho dPl dNo (X (plVar Fr hk nL x0 a) * F) =
        c1 • levImg Fr p hk nL rho1 dPl dNo F +
        c2 • (X (x0, a) * levImg Fr p hk nL rho2 (Function.update dPl x0 (dPl x0 - 1)) dNo F)

def TrMulNo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K)
    (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (x0 : TL J nL r),
    (∀ x', posOf n' (posTL Fr x') = posOf n' (posTL Fr x0) → x' = x0) →
    ∀ (b : Fin K) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
      (F : MvPolynomial (TV n' (m + 1)) (KK O)),
    ∃ (c1 c2 : KK O) (rho1 rho2 : TL J nL r × Fin (r + K) → ℕ),
      levImg Fr p hk nL rho dPl dNo (X (noVar Fr hk nL x0 b) * F) =
        c1 • levImg Fr p hk nL rho1 dPl dNo F +
        c2 • oneT (mulN (x0, b)) (levImg Fr p hk nL rho2 dPl (Function.update dNo x0 (dNo x0 - 1)) F)

def touchC {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (x0 : TL J Dt.nL r) (j : ZMod J) (i : Fin (Dt.nch j)) : Prop :=
  (∃ l, x0 = ⟨j, Sum.inl l⟩ ∧ Sum.inl l ∈ Dt.chain j i) ∨ ∃ m : Fin r, x0 = ⟨j - 1, Sum.inr m⟩

def ThDrop {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (x0 : TL J Dt.nL r) (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ) : Prop :=
  (∀ j i, th j i ≤ th' j i) ∧ (∀ j i, touchC Dt x0 j i → th j i + 1 ≤ th' j i) ∧
  (∀ j m, thL j m ≤ thL' j m) ∧ ∀ j m, x0 ∈ Dt.TSet j m → thL j m + 1 ≤ thL' j m

def PlDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
    [NeZero r] (Dt : SignedChainData p O r J) (x0 : TL J Dt.nL r) (a : Fin r) (d : TL J Dt.nL r → ℕ)
    (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ), ThDrop Dt x0 th th' thL thL' →
    ∀ H, XXg Dt (Function.update d x0 (d x0 + 1)) th' thL' H → XXg Dt d th thL (pderiv (x0, a) H)

def PlEul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
    [NeZero r] (Dt : SignedChainData p O r J) (x0 : TL J Dt.nL r) (a : Fin r) (d : TL J Dt.nL r → ℕ)
    (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ), ThDrop Dt x0 th th' thL thL' →
    ∀ H, XXg Dt d th' thL' H → XXg Dt d th thL (X (x0, a) * pderiv (x0, a) H)

def PlMul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]
    [NeZero r] (Dt : SignedChainData p O r J) (x0 : TL J Dt.nL r) (a : Fin r) (d : TL J Dt.nL r → ℕ)
    (th th' : ∀ j, Fin (Dt.nch j) → ℝ) (thL thL' : ZMod J → Fin r → ℝ), ThDrop Dt x0 th th' thL thL' → 1 ≤ d x0 →
    ∀ H, XXg Dt (Function.update d x0 (d x0 - 1)) th' thL' H → XXg Dt d th thL (X (x0, a) * H)

def inN {r J : ℕ} (nL : ZMod J → ℕ) (x0 : TL J nL r) (j : ZMod J) (u : ℕ) : ℤ := if x0 ∈ NSet nL j u then 1 else 0

def NoOpStep : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero (KK O)] {r J n' : ℕ} [NeZero J] [NeZero r] (K : ℕ) [NeZero K] (_S : UniformizedDVR p O) (_hR : AdmissibleDVR p n' O)
    (Dt : SignedChainData p O r J) (x0 : TL J Dt.nL r) (b : Fin K)
    (T : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
    (T = derN (x0, b) ∨ T = mulN (x0, b) ∨ T = mulN (Kf := KK O) (x0, b) * derN (Kf := KK O) (x0, b)) →
    ∀ (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
      (G : MvPolynomial (TL J Dt.nL r × Fin r) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O)))
      (ka' : ZMod J → ℕ → Fin K → ℤ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka' i.1 i.2.val} e →
      (∀ ka : ZMod J → ℕ → Fin K → ℤ, (∀ j u, ka' j u 0 ≤ ka j u 0 + inN Dt.nL x0 j u) →
        ∀ e1, IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e1 →
          ∀ nu, XXg Dt d th thL (planeCoeff nu (oneT e1 G))) →
      ∀ nu, XXg Dt d th thL (planeCoeff nu (oneT (e * T) G))

def GeoTop : Prop :=
  ∀ {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ {J : ℕ} [NeZero J]
    (nL : ZMod J → ℕ), J = Fr.J → (∀ j, nL j = (Fr.LLset (segZ j)).card) →
    ∀ s ∈ Fr.TT, ∃ x0 : TL J nL r, posOf n' (posTL Fr x0) = s ∧ ∀ x', posOf n' (posTL Fr x') = s → x' = x0

def GeoTouch : Prop :=
  ∀ {n' r : ℕ} [NeZero n'] [NeZero r] (Fr : Frames n' r) (L₁ N₁ : ℕ), Fr.Valid L₁ N₁ → ∀ {J : ℕ} [NeZero J]
    (nL : ZMod J → ℕ), J = Fr.J → (∀ j, nL j = (Fr.LLset (segZ j)).card) →
    ∀ (x0 : TL J nL r) (j : ZMod J) (u : ℕ), u < nL j + r →
      (x0 ∈ NSet nL j (u + 1) ∨ ∃ m : Fin r, x0 = ⟨j - 1, Sum.inr m⟩) →
      touchT Fr (segZ j) u (posOf n' (posTL Fr x0))

end Formalism.MainNotions.PairMembershipBlocks
