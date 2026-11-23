import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8

variable {D : D7} {L : SizeData₂ D}

def Conclusion1 (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (C bo : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (p : ℝ) ≤ L.sc.X'' D.R.n →
    (∀ j ∈ SizeData₂.lifts D, 0 ≤ gainP X K (aL L) (bL L) p j ∧
      gainP X K (aL L) (bL L) p j ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ)) ∧
    (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K (aL L) (bL L) p,
        (askG X (aL L) (bL L) p j s - lo K L C bo p)) - (D.R.m : ℝ) * fl D L.sc C p ≤
      (∑ j ∈ SizeData₂.lifts D, gainP X K (aL L) (bL L) p j) - tauP X K (aL L) (bL L) p

def Conclusion2 (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop := MeanKappaBound X K

open Classical in

def cands (D : D7) (L : SizeData₂ D) (K : Consts) : Finset ℕ :=
  (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => Cand D L K p)

open Classical in

def WReq (X : Inst D L) (K : Consts) (a b : HH D → ℤ) : Prop :=
  ∑ p ∈ cands D L K, Real.log p / p *
      (2 * (if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then (1 : ℝ) else 0) + 4 * Sig X K a b p) ≤
    L.sc.x ^ (-9 : ℝ)

def PointsLemma (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop :=
  ∀ a ∈ box D (winA D L.sc), ∀ b ∈ box D (winB D K L.sc), WReq X K a b →
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ IsResidueClassZero D p) →
      ∑ p ∈ S, Real.log p * max 0 ((∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) -
        ((∑ j ∈ SizeData₂.lifts D, gainP X K a b p j) - tauP X K a b p - ioP X K a b p)) ≤
      5 * (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a / L.sc.x) ∧
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      ∑ p ∈ S, Real.log p * ioP X K a b p ≤
        (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * L.sc.x ^ (-9 : ℝ))

def WeightVectorExists (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop :=
  ∃ a ∈ box D (winA D L.sc), ∃ b ∈ box D (winB D K L.sc), WReq X K a b

def Conclusion0 (D : D7) (L : SizeData₂ D) (X : Inst D L) : Prop :=
  ∀ a b : HH D → ℤ, (∀ s ∈ D.host.TT, (a s : ℝ) ≤ 2 * L.sc.a) → (∀ s ∈ D.host.TT, (0 : ℝ) ≤ (b s : ℝ)) →
  ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → ∀ j ∈ SizeData₂.lifts D, ∀ s ∈ D.host.TT,
    askP X a b p j s ≤ askG X a b p j s ∧
    askG X a b p j s ≤ askP X a b p j s + Nm D * Real.logb p (2 * L.sc.a)

def WeightedPrimeSumBound (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (C : ℝ) : Prop :=
  (∀ a ∈ box D (winA D L.sc), ∀ b ∈ box D (winB D K L.sc), ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime ∧ (IsResidueClassZero D p ∨ IsSg D p) ∧ L.sc.X'' D.R.n < (p : ℝ)) →
    ∑ p ∈ S, Real.log p * (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ D.host.TT, askG X a b p j s) ≤
      (D.R.m : ℝ) * (D.host.TT.card : ℝ) * L.sc.a * L.sc.x ^ (-16 : ℝ)) ∧
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) →
    ∑ p ∈ S, Real.log p * (C * (cG L + L.etaSz) * Real.logb p (2 * L.sc.a)) ≤ L.sc.b * L.sc.x ^ (-100 : ℝ) ∧
    ∑ p ∈ S, Real.log p * fl D L.sc C p ≤ L.sc.b * L.sc.x ^ (-100 : ℝ)

def admW (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop :=
  aL L ∈ box D (winA D L.sc) ∧ bL L ∈ box D (winB D K L.sc) ∧ WReq X K (aL L) (bL L)

open Classical in

def adm1 (D : D7) (L : SizeData₂ D) (X : Inst D L) (Ce : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → IsResidueClassZero D p → L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ) →
    L2 D L.sc < goodU L.sc.delta1 → 3 * Gp L.sc ≤ addOrderOf (hP D p) →
    ∀ t0 ∈ reps X p, Good X p t0 →
      ((addOrderOf (hP D p) : ℝ) * L.sc.delta1 / (Ce * Real.log L.sc.x) ≤ (Nv X p t0 : ℝ) ∧
        (Nv X p t0 : ℝ) ≤ 40 * (addOrderOf (hP D p) : ℝ) * L.sc.delta1) ∧
      (∀ s ∈ topsOn X p t0, IsV X p s → ∃ d : ℕ, 1 ≤ d ∧ d ≤ Gp L.sc ∧
        s + d • hP D p ∈ D.host.TT ∧ IsV X p (s + d • hP D p) ∧
        ((Finset.Ioo 0 d).filter (fun e => s + e • hP D p ∈ D.host.TT)).card ≤ N1 L.sc) ∧
      (∀ i ∈ topsOn X p t0,
        ((Finset.Icc 1 (L1 D L.sc p)).filter (fun d =>
          i - d • hP D p ∈ D.host.TT ∧ IsV X p (i - d • hP D p))).card < rG L.sc)

open Classical in

def primesResidueBelow (D : D7) (y : ℝ) : Finset ℕ :=
  (Finset.range ⌈y⌉₊).filter (fun p => p.Prime ∧ (p : ℝ) < y ∧ IsResidueClassZero D p)

open Classical in

def BTT (D : D7) (L : SizeData₂ D) (X : Inst D L) : ℝ :=
  ∑ p ∈ (primesResidueBelow D L.sc.X').filter (fun p => L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (hP D p) : ℝ)),
    Real.log p / p * ((D.host.TT.filter (fun t => ¬ Good X p (X.bs (stepP D p) t))).card : ℝ)

def adm2 (D : D7) (L : SizeData₂ D) (X : Inst D L) : Prop :=
  ((D.R.n : ℝ) * L.sc.delta1 / 2 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ 2 * (D.R.n : ℝ) * L.sc.delta1) ∧
  BTT D L X ≤ (D.host.TT.card : ℝ) * L.sc.x ^ (-2 + L.sc.eps)

open Classical in

def adm3 (D : D7) (L : SizeData₂ D) : Prop :=
  ∑ p ∈ (primesResidueBelow D (L.sc.X'' D.R.n)).filter
      (fun p => (addOrderOf (hP D p) : ℝ) < L.sc.x ^ (L.sc.eps / 4)), Real.log p / p ≤
    L.sc.x ^ (-hG L.sc + L.sc.eps)

open Classical in

def ArchimedeanSignatureMatching (D : D7) (L : SizeData₂ D) (K : Consts) : Prop :=
  rho D K L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧
  ∑ p ∈ (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => p.Prime ∧ InBand0 D K L.sc p), Real.log p / p ≤
    L.sc.x ^ (-1 : ℝ) ∧
  rho D K L.sc ≤ rhoB D K L.sc ∧ rhoB D K L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧
  ∑ p ∈ (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => p.Prime ∧ InBand D K L.sc p), Real.log p / p ≤
    L.sc.x ^ (-1 : ℝ)

def adm5 (D : D7) (L : SizeData₂ D) (K : Consts) (δ : ℝ) : Prop :=
  L.sc.x ^ (L.sc.eps - δ) ≤ La K L.sc ∧ La K L.sc ≤ L.sc.x ^ (L.sc.eps + δ) ∧
  ∀ p : ℕ, p.Prime →
    ((p : ℝ) < L.sc.p0 D.R.k → Real.log (Qp L.sc p) ≤ L.sc.x ^ (L.sc.eps / 8 + δ)) ∧
    ((p : ℝ) < L.sc.X' → Real.log (Qp L.sc p) ≤ L.sc.x ^ (11 * L.sc.eps / 24 + δ))

def adm6 (D : D7) (L : SizeData₂ D) (K : Consts) : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    ∀ TT : Finset (Fin n'),
      IsGoodOrbit n' TT (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x →
      2 * L1 D L.sc p ≤ L2 D L.sc → L2 D L.sc < goodU L.sc.delta1 → 3 * Gp L.sc ≤ n' →
      (TT.card : ℝ) ≤ NplusF L.sc n' →
    (p : ℝ) < L.sc.p0 D.R.k →
    ∀ a b : Fin n' → ℤ, (∀ s ∈ TT, a s ∈ winA D L.sc ∧ b s ∈ winB D K L.sc) →
    (∀ s ∈ TT, (L.sc.a - cG L) + (⌊cG L⌋₊ : ℝ) ≤ (a s : ℝ) ∧
      (a s : ℝ) ≤ 2 * (L.sc.a - cG L) - (⌊cG L⌋₊ : ℝ) ∧ (b s : ℝ) + 2 * (⌊cG L⌋₊ : ℝ) ≤ c0num L) →
    ∀ lam0 : Fin n' → Fin (D.R.k - 1 + 1) → ℤ, IsBaseWeight TT a b ⌊cG L⌋₊ lam0 → IsDominant lam0 →
    13 ≤ p → 2 ≤ rG L.sc → N1 L.sc ^ 2 ≤ rG L.sc * TT.card →
    (rG L.sc : ℝ) ≤ L.sc.x ^ Scale.A →
    (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) ≤ (p : ℝ) ^ ((L1 D L.sc p : ℤ) - 1) →
    256 * (D.R.k : ℝ) ^ 2 * (TT.card : ℝ) * (L.sc.x ^ Scale.A) ^ 2 ≤
      (D.R.k : ℝ) ^ 2 * L.sc.x ^ (3 * Scale.A) →
    N1 L.sc + 2 * rG L.sc + rG L.sc ≤ D.R.k →
    K.kII' * (N1 L.sc : ℝ) ^ 2 * Real.log L.sc.a ≤ D.R.k →
    K.szII * (D.R.k : ℝ) ^ 3 * (rG L.sc : ℝ) ^ 2 * (TT.card : ℝ) * Qp L.sc p ^ 5 *
        ((8 * ((DIIf K L p n' : ℝ) + 1)) +
          ((rG L.sc : ℝ) * (TT.card : ℝ) * c0num L + 2 * (rG L.sc : ℝ) * (n' : ℝ) * cG L)) *
        L.sc.x ^ Scale.A ≤ L.sc.a - cG L →
    LPprime (W := W) p n' ι σ w (rG L.sc) lam0 ⌈tIIf K L p n' TT.card⌉₊ (DIIf K L p n')
      (kapIIf K L TT.card) (8 * (DIIf K L p n' + 1))

def HypI (D : D7) (L : SizeData₂ D) (K : Consts) (p n' N : ℕ) : Prop :=
  let s := L.sc
  let Y := s.x ^ (Scale.A / 2)
  let Yb := s.x ^ s.eps / 20
  let Ib := Nstar D s * s.x ^ s.eps * La K s * s.b' / D.R.k
  (D.R.k : ℝ) ^ 2 * Y ^ 2 ≤ p ∧ (p : ℝ) < s.a / s.b' ∧ rho D K s < 1 / 6 ∧
  2 * N1 s + 2 ≤ D.R.k - 1 ∧
  8 * Real.log ((N : ℝ) * Y) ≤ La K s ∧
  Yb * (N : ℝ) * La K s * s.b' / D.R.k ≤ Ib ∧ 2 * Ib ≤ s.b' ∧
  K.kI ≤ Yb ∧
  (D.R.k : ℝ) * Y ^ 2 * Yb * (N : ℝ) * La K s * Real.log s.a ≤ s.X' ∧
  K.kI * (N : ℝ) * La K s ^ 2 ≤ D.R.k ∧ 2 * Yb * (N : ℝ) * La K s < D.R.k ∧
  cG L ≤ La K s * s.b' / D.R.k ∧
  (N : ℝ) ≤ NplusF s n' ∧
  K.kI * (D.R.k : ℝ) ^ 3 * (N : ℝ) * Qp s p ^ 4 *
    ((8 * ((DIf K L p n' : ℝ) + 1)) + (N : ℝ) * cG L + (n' : ℝ) * cG L) * Y ≤ s.b'

def adm7 (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    ∀ TT : Finset (Fin n'),
      IsGoodOrbit n' TT (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x →
      L2 D L.sc < goodU L.sc.delta1 → 3 * Gp L.sc ≤ n' →
    L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ¬ InBand0 D K L.sc p →
    HypI D L K p n' TT.card →
    ∀ a b : Fin n' → ℤ, (∀ s ∈ TT, a s ∈ winA D L.sc ∧ b s ∈ winB D K L.sc) →
    ∀ lam0 : Fin n' → Fin (D.R.k - 1 + 1) → ℤ, IsBaseWeight TT a b ⌊cG L⌋₊ lam0 → IsDominant lam0 →
    LPprime (W := W) p n' ι σ w 1 lam0 ⌈tIf K L p n' TT a b⌉₊ (DIf K L p n') (X.kapI p n' TT a b)
      (8 * (DIf K L p n' + 1))

def adm8 (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Cm : ℝ) : Prop :=
  ∀ (p n' : ℕ), p.Prime → ∀ TT : Finset (Fin n'),
    IsGoodOrbit n' TT (L2 D L.sc) (KG L.sc) (rG L.sc) L.sc.delta1 (hG L.sc) L.sc.x →
      L2 D L.sc < goodU L.sc.delta1 → 3 * Gp L.sc ≤ n' →
    L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ¬ InBand0 D K L.sc p → HypI D L K p n' TT.card →
    (∀ a b, 0 ≤ X.kapI p n' TT a b) ∧
    meanLoc D K L.sc n' TT (X.kapI p n' TT) ≤
      Cm * (TT.card : ℝ) * (N1 L.sc : ℝ) / L.sc.x ^ (Scale.A / 2)

def adm9 (D : D7) (L : SizeData₂ D) (X : Inst D L) (Ce : ℝ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ L.sc.a →
    (X.ep p : ℝ) ≤ (Ce + 1) * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a) ∧
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Nonempty (GatTies D) →
    (D.gat u w hg).Mna.map ((((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^
        X.ep (D.what₂.places.resChar w)) • LinearMap.id) ≤ (D.gat u w hg).M ∧
      (D.gat u w hg).M ≤ (D.gat u w hg).Mna

def UnitBoundLowTerm (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts)
    (low : D.what₂.Word → D.what₂.places.Pl → ℝ) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (VVs VV' : Finset (HH D)),
    let p := D.what₂.places.resChar w
    VVs ⊆ reps X p → VV' ⊆ VVs → ∀ F ∈ (D.gat u w hg).M,
      Y.vKge u w hg (yProd Y u w hg VV' F) ((∑ j ∈ SizeData₂.lifts D,
          ((∑ t0 ∈ VV', max (gU X K (aL L) (bL L) p j t0 - Pr X K (bL L) p j t0)
              (max (g0 X K (aL L) (bL L) p j t0) 0)) +
            (∑ t0 ∈ VVs \ VV', max (g0 X K (aL L) (bL L) p j t0) 0) +
            ∑ t0 ∈ reps X p \ VVs, max (g0 X K (aL L) (bL L) p j t0) 0)) +
          low u w)

def lowU (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) : ℝ :=
  -((D.R.m : ℝ) * (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ))

def unitBoundAtTwistedPlaces (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  UnitBoundLowTerm D L X Y K (lowU D)

def UnitBoundDifferenceTerm (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  UnitBoundLowTerm D L X Y K (lowFE L)

def admG1 (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let Mram := G.M ⊓ Y.Vram u w hg
    NP X Y K u w hg ≤ Mram.map (((p : G.O) ^ ⌈tauP X K (aL L) (bL L) p⌉.toNat) • LinearMap.id) ∧
    (∃ l : ℕ, Module.length G.O (↥Mram ⧸ (NP X Y K u w hg).comap Mram.subtype) = l ∧
      (l : ℝ) ≤ vUnit G * (G.d : ℝ) * (tauP X K (aL L) (bL L) p + ioP X K (aL L) (bL L) p)) ∧
    ∀ F ∈ NP X Y K u w hg,
      Y.vKge u w hg F ((∑ j ∈ SizeData₂.lifts D, gainP X K (aL L) (bL L) p j) + lowFE L u w)

def TypePrimeSizeConds (D : D7) (L : SizeData₂ D) (K : Consts) : Prop :=
  Formalism.MainNotions.SizesAt L ∧ 4 * L.Sc ≤ La K L.sc * L.sc.b' / (D.R.k : ℝ) ∧ Nm D + 1 ≤ L.sc.w'' D.R.n

structure AConsts where
  C31 : ℝ
  Ce : ℝ
  Cm : ℝ
  δ : ℝ

def admitted (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (A : AConsts) : Prop :=
  adm1 D L X A.C31 ∧ adm2 D L X ∧ adm3 D L ∧ ArchimedeanSignatureMatching D L K ∧ adm5 D L K A.δ ∧ adm6 D L K ∧
  adm7 D L X K ∧ adm8 D L X K A.Cm ∧ adm9 D L X A.Ce ∧ unitBoundAtTwistedPlaces D L X Y K ∧ admG1 D L X Y K ∧
  TypePrimeSizeConds D L K

def Conclusion₂ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (C bo : ℝ) : Prop :=
  Conclusion1 D L X K C bo ∧ Conclusion2 D L X K ∧ PointsLemma D L X K ∧ WeightVectorExists D L X K ∧ Conclusion0 D L X ∧ WeightedPrimeSumBound D L X K C

def Stmt (D : D7) (L : SizeData₂ D) (K : Consts) (A : AConsts) (C bo : ℝ) : Prop :=
  K.Nonneg → ∀ (X : Inst D L) (Y : LatInst D), admitted D L X Y K A → Conclusion₂ D L X K C bo

def ClosedFormOfAdmitted (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ A : AConsts, ∃ C bo : ℝ, 0 ≤ C ∧ 0 ≤ bo ∧
    ∀ (X : Inst D L) (Y : LatInst D), admitted D L X Y K A → Conclusion₂ D L X K C bo

def AdmF {eps : ℝ} (Fm : FamP eps) (K : Consts) (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i))
    (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)) : Prop :=
  ∃ (C31 Ce Cm : ℝ), 0 < C31 ∧ 0 ≤ Ce ∧ 0 ≤ Cm ∧
    ∀ δ > 0, ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
      admitted (Fm.D x i) (Fm.L x i) (X x i) (Y x i) K ⟨C31, Ce, Cm, δ⟩

def ConclusionOnFamily {eps : ℝ} (Fm : FamP eps) (K : Consts) (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) : Prop :=
  ∃ (C : ℝ) (δ : ℝ → ℝ), Filter.Tendsto δ Filter.atTop (nhds 0) ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    Conclusion₂ (Fm.D x i) (Fm.L x i) (X x i) K C ((Fm.L x i).sc.b ^ δ x)

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ (K : Consts), K.Nonneg → ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i))
    (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)), AdmF Fm K X Y → ConclusionOnFamily Fm K X

def FamilyClosedForm {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
        (∀ δ > 0, ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
          admitted (Fm.D x i) (Fm.L x i) (X x i) (Y x i) K ⟨C31, Ce, Cm, δ⟩) →
        ∃ δ : ℝ → ℝ, Filter.Tendsto δ Filter.atTop (nhds 0) ∧ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
          Conclusion₂ (Fm.D x i) (Fm.L x i) (X x i) K C ((Fm.L x i).sc.b ^ δ x)

end Formalism.MainNotions.AuxBlock8

end
