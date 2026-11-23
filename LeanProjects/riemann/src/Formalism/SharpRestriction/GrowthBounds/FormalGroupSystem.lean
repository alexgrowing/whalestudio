import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.Imports
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Numbers

variable {n' k1 : ℕ}

def lamI (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') (i : ℕ) : ℤ :=
  if h : 1 ≤ i ∧ i ≤ k1 + 1 then lam0 s ⟨i - 1, by omega⟩ else 0

def NN (k1 t j : ℕ) : ℕ := k1 + 1 + j * (t + 1)

def nu (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') (i : ℕ) : ℤ :=
  if 1 ≤ i ∧ i ≤ k1 + 1 then lamI lam0 s i + w j s
  else if k1 + 1 < i ∧ i ≤ NN k1 t j then -w ((i - (k1 + 2)) / (t + 1) + 1) s + w j s
  else 0

def al (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') : ℤ :=
  if s ∈ TT then lamI lam0 s 1 - lamI lam0 s 2 else 0

def cap (t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (s : Fin n') : ℤ :=
  if s ∈ TT then nu t lam0 w j s 2 else nu t lam0 w j s 1

def lsz (t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (s : Fin n') : ℤ :=
  (∑ i ∈ Icc 1 (NN k1 t j), nu t lam0 w j s i) - al TT lam0 s

def lgp (p : ℕ) (x : ℤ) : ℕ := if x ≤ 0 then 0 else Nat.log p x.toNat + 1

def de (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ℝ :=
  ∑ s : Fin n', ((NN k1 t j : ℝ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s)) +
    ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℝ)) ^ 2

def gam (p : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) ^ 2 - 1)

def IsOddPos (s : Fin n') : Prop := s.val % 2 = 1

instance (s : Fin n') : Decidable (IsOddPos s) := inferInstanceAs (Decidable (s.val % 2 = 1))

def gB (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ℝ :=
  gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ) -
    ∑ s ∈ TT.filter IsOddPos, ∑' e : ℕ,
      min ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1)) (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ) -
    de p t TT lam0 w j

def dSet (TT : Finset (Fin n')) (s : Fin n') : Finset ℕ :=
  (TT.filter fun s' => s'.val % 2 ≠ s.val % 2).image fun s' => (s'.val + n' - s.val) % n'

def gA (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ℝ :=
  ∑ s ∈ TT, ∑' e : ℕ,
    (if 2 * e + 1 ∈ dSet TT s then 0 else
      max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) - (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ)) 0) -
    de p t TT lam0 w j

def Nprime (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j i : ℕ) : ℤ :=
  ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s), ∑ a ∈ Icc 1 i, lamI lam0 s a +
    (i : ℤ) * ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), w j s

def PrZ (t r : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ℤ :=
  ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      ((r : ℤ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), lamI lam0 s a) +
    ((n' / 2 : ℕ) : ℤ) * r * j * (t + 1)

def Pr (t r : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ℝ :=
  ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      ((r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ)) +
    (n' : ℝ) * r * j * (t + 1) / 2

def Sv (p t m r : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) : ℝ :=
  ∑ j ∈ Icc 1 m, max (gB p t TT lam0 w j - Pr t r lam0 w j - gA p t TT lam0 w j) 0

structure Std (p n' k1 t m c r : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  two_le : 2 ≤ n'
  even : Even n'
  r_pos : 1 ≤ r
  two_r : 2 * r ≤ k1 + 1
  m_pos : 1 ≤ m
  base : IsBaseWeight TT a b c lam0
  dom : IsDominant lam0
  w_low : ∀ s, (c : ℤ) ≤ w 1 s ∧ -lam0 s (Fin.last k1) ≤ w 1 s
  w_mono : ∀ s l, 1 ≤ l → l < m → w l s ≤ w (l + 1) s

end Numbers

section Theta

variable (p : ℕ) [Fact p.Prime]

abbrev kb : Type := AlgebraicClosure (ZMod p)

abbrev WW : Type := WittVector p (kb p)

abbrev K0 : Type := FractionRing (WW p)

def sigW : WW p →+* WW p := WittVector.frobenius

def sigK : K0 p ≃+* K0 p :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (kb p))

def IntS {ι : Type} (f : MvPowerSeries ι (K0 p)) : Prop :=
  ∃ g : MvPowerSeries ι (WW p), f = MvPowerSeries.map (algebraMap (WW p) (K0 p)) g

def IntR {ι K1 : Type} [Field K1] (R1 : Subring K1) (f : MvPowerSeries ι K1) : Prop :=
  ∀ n, MvPowerSeries.coeff n f ∈ R1

def logF : PowerSeries (K0 p) :=
  PowerSeries.mk fun n => ∑ j ∈ range (n + 1), if n = p ^ (2 * j) then (((p : K0 p)) ^ j)⁻¹ else 0

def inParam {ι : Type} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries ι (K0 p) :=
  MvPowerSeries.subst (fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι (K0 p)) (logF p)) f

def inParamK {ι : Type} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (f : MvPowerSeries ι K1) : MvPowerSeries ι K1 :=
  MvPowerSeries.subst (fun i => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
    (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) f

def expS {ι : Type} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries ι (K0 p) :=
  fun n => ∑ k ∈ range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k)

def Simeq {ι : Type} (f g : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧
    ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
      expS p (inParam p (f - g)) = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

def sub2 {τ : Type} (f : MvPowerSeries (Fin 2) (K0 p)) (x y : MvPowerSeries τ (K0 p)) : MvPowerSeries τ (K0 p) :=
  MvPowerSeries.subst ![x, y] f

structure BeProp (be : MvPowerSeries (Fin 2) (K0 p)) : Prop where
  ab : ∀ n : Fin 2 →₀ ℕ, MvPowerSeries.coeff n be ≠ 0 → 1 ≤ n 0 ∧ 1 ≤ n 1
  add1 : Simeq p (sub2 p be (MvPowerSeries.X 0 + MvPowerSeries.X 1) (MvPowerSeries.X 2) -
      sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2) - sub2 p be (MvPowerSeries.X 1) (MvPowerSeries.X 2))
    (0 : MvPowerSeries (Fin 3) (K0 p))
  add2 : Simeq p (sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 1 + MvPowerSeries.X 2) -
      sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 1) - sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.X 2))
    (0 : MvPowerSeries (Fin 3) (K0 p))
  conj : ∀ α : WW p, (sigW p)^[2] α = α →
    Simeq p (sub2 p be (MvPowerSeries.C (algebraMap (WW p) (K0 p) α) * MvPowerSeries.X 0) (MvPowerSeries.X 1) :
        MvPowerSeries (Fin 2) (K0 p))
      (sub2 p be (MvPowerSeries.X 0) (MvPowerSeries.C (algebraMap (WW p) (K0 p) (sigW p α)) * MvPowerSeries.X 1))

abbrev Eidx (n' r0 r1 : ℕ) : Type := Fin (n' / 2) × Fin r0 × Fin r1

def ExtensionLocalCondition {n' r0 r1 : ℕ} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1) : Prop :=
  ∃ (Ph : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p))
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1),
    Th = MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph)) * U ∧ IntR R1 (inParamK p K1 U) ∧
    Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) Ph :
      MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)) Ph ∧
    BeProp p be ∧
    Simeq p Ph (∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)))

structure OmBasis (n' : ℕ) where
  om : Fin (n' / 2) → WW p
  omS : Fin (n' / 2) → WW p
  fix : ∀ r, (sigW p)^[n'] (om r) = om r
  fixS : ∀ r, (sigW p)^[n'] (omS r) = omS r
  dual : ∀ r r', ∑ i : Fin (n' / 2), (sigW p)^[2 * i.val] (om r * omS r') = if r = r' then 1 else 0

abbrev Zidx (n' r0 r1 : ℕ) : Type := Fin n' × Fin r0 × Fin r1

def coordZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') :
    Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries (Zidx n' r0 r1) K'
  | Sum.inl (r, a, b) => ∑ s ∈ univ.filter (fun s : Fin n' => ¬ IsOddPos s),
      MvPowerSeries.C (vp * algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] (B.omS r)))) *
        MvPowerSeries.X (s, a, b)
  | Sum.inr (r, a, b) => ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      MvPowerSeries.C (vp * algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] (B.om r)))) *
        MvPowerSeries.X (s, a, b)

def ThZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K') : MvPowerSeries (Zidx n' r0 r1) K' :=
  MvPowerSeries.subst (coordZ B K' vp) Th

def Rp (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') : Subring K' :=
  Subring.closure (Set.range (fun x : WW p => algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) x)) ∪ {vp})

def posSub {n' : ℕ} (s : Fin n') (d : ℕ) : Fin n' :=
  ⟨(s.val + n' * d - d) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

def sSer {n' r0 r1 : ℕ} (K' : Type) [Field K'] (e : Fin n') (a : Fin r0)
    (b : Fin r1) : MvPowerSeries (Zidx n' r0 r1) K' :=
  fun n => ∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (posSub e (2 * l), a, b) (p ^ (2 * l)) then (-1) ^ l else 0

def hhS {n' r0 r1 : ℕ} (K' : Type) [Field K'] (u : Fin n' → K') :
    MvPowerSeries (Zidx n' r0 r1) K' :=
  ∑ s : Fin n', MvPowerSeries.C (u s) *
    ∑ a : Fin r0, ∑ b : Fin r1, (sSer p K' s a b) ^ p * sSer p K' (posAdd s 1) a b

def InClass {n' r0 r1 : ℕ} {K' : Type} [Field K'] (R' : Subring K')
    (f hh : MvPowerSeries (Zidx n' r0 r1) K') : Prop :=
  ∃ g : ℕ → MvPowerSeries (Zidx n' r0 r1) K', (∀ i, IntR R' (g i)) ∧ ∀ n : Zidx n' r0 r1 →₀ ℕ,
    MvPowerSeries.coeff n f = ∑ i ∈ range (n.degree + 1),
      (((p : K') ^ i)⁻¹ * MvPowerSeries.coeff n (hh ^ i * g i))

def SConcl {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1]
    (R1 : Subring K1) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1) : Prop :=
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    ∃ u : Fin n' → K', (∀ s, u s ∈ R') ∧ ∀ hh' : MvPowerSeries (Zidx n' r0 r1) K',
      MvPowerSeries.constantCoeff hh' = 0 →
      (∃ G : MvPowerSeries (Zidx n' r0 r1) K', IntR R' G ∧ hh' = hhS p K' u + MvPowerSeries.C (p : K') * G) →
      InClass p R' (ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') Th)) hh'

def DworkLemma : Prop :=
  p ≠ 2 → ∀ (n : ℕ) (Ps : MvPowerSeries (Fin n) (K0 p)), MvPowerSeries.constantCoeff Ps = 0 →
    (IntS p (expS p Ps) ↔ ∃ Q : MvPowerSeries (Fin n) (WW p),
      MvPowerSeries.subst (fun i => (MvPowerSeries.X i) ^ p) (MvPowerSeries.map (sigK p).toRingHom Ps) -
        (p : K0 p) • Ps = (p : K0 p) • MvPowerSeries.map (algebraMap (WW p) (K0 p)) Q)

end Theta

section ThetaAll

variable (p : ℕ) [Fact p.Prime]

def ExtensionGeneratorCondition {ι : Type} [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (ι ⊕ ι) K1) : Prop :=
  ∃ (Ph : MvPowerSeries (ι ⊕ ι) (K0 p)) (U : MvPowerSeries (ι ⊕ ι) K1),
    Th = MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph)) * U ∧ IntR R1 (inParamK p K1 U) ∧
    Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) Ph : MvPowerSeries (ι ⊕ ι) (K0 p)) Ph ∧
    BeProp p be ∧
    Simeq p Ph (∑ e : ι, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)))

end ThetaAll

def resV {ι κ R : Type} [Semiring R] (f : κ → ι) (Th : MvPowerSeries ι R) : MvPowerSeries κ R :=
  fun n => MvPowerSeries.coeff (n.mapDomain f) Th

def linSub {σ R : Type} [Fintype σ] [CommRing R] (B : σ → σ → R) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun x => ∑ y, MvPowerSeries.C (B x y) * MvPowerSeries.X y) f

def atPi {σ R : Type} [CommRing R] (vp : R) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun n => vp ^ n.degree * MvPowerSeries.coeff n f

def applyD {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    MvPolynomial τ Kc :=
  ∑ n ∈ P.support, ((∏ x ∈ n.support, ((n x).factorial : Kc)) * MvPowerSeries.coeff n f) •
    MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n P)

theorem Pj_nV {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) : (Fl.Pj j).nV = G.P.nV := by
  cases j <;> rfl

structure Sys (p : ℕ) [Fact p.Prime] where
  G : GAtP p
  Fl : Fills G
  Lv : Levels Fl
  Ch : Chain Lv
  std : ∀ v, Std p (G.P.n' v) G.P.m Fl.t Fl.mm Fl.c G.P.r (Fl.TT v) (Fl.a v) (Fl.b v) (G.P.lam0 v) (Fl.w v)
  vp : G.O
  unif : Irreducible vp
  eO : ℕ
  eO_spec : Associated (p : G.O) (vp ^ eO)
  dG : ℕ → ℕ
  dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat p (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j
  om : ∀ v, OmBasis p (G.P.n' v)

namespace Sys

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

abbrev Pl : Type := Fin X.G.P.nV

abbrev t : ℕ := X.Fl.t

abbrev mm : ℕ := X.Fl.mm

abbrev TT (v : X.Pl) : Finset (Fin (X.G.P.n' v)) := X.Fl.TT v

abbrev w (v : X.Pl) : ℕ → Fin (X.G.P.n' v) → ℤ := X.Fl.w v

abbrev Pj (j : ℕ) : Places p X.G.O X.G.Kf := X.Fl.Pj j

abbrev Fm (j : ℕ) : Type := X.Lv.Fm j

def Int (j : ℕ) : Submodule X.G.O (X.Fm j) := X.Lv.Int j

def FQ (j : ℕ) : Submodule X.G.Kf (X.Fm j) := Submodule.span X.G.Kf (X.Int j : Set (X.Fm j))

def Kz (j : ℕ) : X.Fm j →ₗ[X.G.Kf] X.Fm (j + 1) := X.Ch.Kz j

def vJ (j : ℕ) (v : X.Pl) : Fin (X.Pj j).nV := Fin.cast (Pj_nV X.Fl j).symm v

def vB (j : ℕ) (v : Fin (X.Pj j).nV) : X.Pl := Fin.cast (Pj_nV X.Fl j) v

def Tm (v : X.Pl) (i j : ℕ) (F : X.Fm j) : X.Fm j := X.Lv.Tm j (X.vJ j v) i F

def vsc (g : ℝ) : X.G.Kf := (algebraMap X.G.O X.G.Kf X.vp) ^ (⌈g * (X.eO : ℝ)⌉)

def vGe (j : ℕ) (F : X.Fm j) (g : ℝ) : Prop := F ∈ scale (X.vsc g) (X.Int j)

def intK : Submodule X.G.O X.G.Kf := LinearMap.range (Algebra.linearMap X.G.O X.G.Kf)

def vGeK (x : X.G.Kf) (g : ℝ) : Prop := x ∈ scale (X.vsc g) X.intK

def vEqK (x : X.G.Kf) (g : ℝ) : Prop := X.vGeK x g ∧ ∀ g', g < g' → ¬ X.vGeK x g'

def chainK (j : ℕ) : X.Fm 0 →ₗ[X.G.Kf] X.Fm j := X.Ch.chainK j

def alv (v : X.Pl) (s : Fin (X.G.P.n' v)) : ℤ := al (X.TT v) (X.G.P.lam0 v) s

def gv (v : X.Pl) (j : ℕ) : ℝ := gB p X.t (X.TT v) (X.G.P.lam0 v) (X.w v) j

def g0v (v : X.Pl) (j : ℕ) : ℝ := gA p X.t (X.TT v) (X.G.P.lam0 v) (X.w v) j

def Conclusion₂ (v : X.Pl) (j : ℕ) : ℝ := Pr X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j

def Svv (v : X.Pl) : ℝ := Sv p X.t X.mm X.G.P.r (X.TT v) (X.G.P.lam0 v) (X.w v)

def Tt (v : X.Pl) (i j : ℕ) (F : X.Fm j) : X.Fm j :=
  if i = 0 then F else ((p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j i)) • X.Tm v i j F

def yv (v : X.Pl) : X.Fm 0 → X.Fm 0 := X.G.yv v

def ecal (v : X.Pl) (i j : ℕ) (F : X.Fm j) : X.Fm j :=
  ((p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * i * ((NN X.G.P.m X.t j : ℤ) - i)))) • X.Tm v i j F

def qh (v : X.Pl) (i : ℕ) : X.G.Kf := (p : X.G.Kf) ^ (((X.G.P.n' v / 2 : ℕ) : ℤ) * ((X.t : ℤ) - 2 * i))

def FF (v : X.Pl) (m : ℕ → X.G.Kf) (j : ℕ) : Fin j × Fin (X.t + 1) → X.G.Kf :=
  fun x => m (x.1.val + 1) * X.qh v x.2.val

def cl (v : X.Pl) (m : ℕ → X.G.Kf) (j l : ℕ) : X.G.Kf :=
  (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) j X.G.P.r - Nprime (X.G.P.lam0 v) (X.w v) j (X.G.P.r - l)) *
    (p : X.G.Kf) ^ (((X.G.P.n' v / 2 : ℕ) : ℤ) * l * ((NN X.G.P.m X.t j : ℤ) - 2 * X.G.P.r + l)) *
    MvPolynomial.eval (X.FF v m j) (MvPolynomial.hsymm (Fin j × Fin (X.t + 1)) X.G.Kf l)

def Ttu (v : X.Pl) (u : ℕ → X.G.Kf) (i j : ℕ) (F : X.Fm j) : X.Fm j :=
  ((∏ l ∈ Icc 1 j, u l) ^ (-(i : ℤ))) • X.Tt v i j F

def Zop (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (F : X.Fm j) : X.Fm j :=
  ∑ l ∈ range (X.G.P.r + 1), ((-1 : X.G.Kf) ^ l * X.cl v m j l) • X.Ttu v u (X.G.P.r - l) j F

def alEven (v : X.Pl) : ℤ := ∑ s ∈ (X.TT v).filter (fun s => ¬ IsOddPos s), X.alv v s

def vm (v : X.Pl) (l : ℕ) : ℤ :=
  ∑ s ∈ univ.filter (fun s : Fin (X.G.P.n' v) => ¬ IsOddPos s), X.w v l s -
    ∑ s ∈ univ.filter (fun s : Fin (X.G.P.n' v) => IsOddPos s), X.w v l s

def Iprod (S : X.Pl → ℝ) (VV : Finset X.Pl) : Submodule X.G.O (X.Fm 0) :=
  Submodule.span X.G.O {F | ∃ BB ⊆ VV, ∃ Lv : List X.Pl, Lv.Nodup ∧ Lv.toFinset = BB ∧
    ∃ F0 ∈ scale ((algebraMap X.G.O X.G.Kf X.vp) ^ (∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉)) (X.Int 0),
      F = Lv.foldr (fun v F' => (X.yv v)^[X.mm] F') F0}

abbrev Lt (j : ℕ) : Type := X.Lv.comp j × (X.Pj j).Tup

def stab (j : ℕ) (La : X.Lt j) : ℕ :=
  Nat.card {γ : (X.Lv.lev j La.1).Γ // (X.Lv.lev j La.1).smul γ La.2 = La.2}

def latAt (v : X.Pl) : (j : ℕ) → (X.Fl.Pj j).Tup →
    Submodule (X.G.P.W v) (Fin ((X.Fl.Pj j).m + 1) → X.G.P.Qq v)
  | 0, L => L v
  | _ + 1, L => L v

def ind (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup) :
    Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ :=
  fun x => by classical exact if ∀ y ∈ X.latAt v j L, x.mulVec y ∈ X.latAt v (j + 1) L' then 1 else 0

abbrev EA (j : ℕ) : Type := Σ v : X.Pl, Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))

abbrev ZA (j : ℕ) : Type := Σ v : X.Pl, Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))

def coordZA (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) : X.EA j ⊕ X.EA j → MvPowerSeries (X.ZA j) K'
  | Sum.inl ⟨v, (r, a, b)⟩ => ∑ s ∈ univ.filter (fun s : Fin (X.G.P.n' v) => ¬ IsOddPos s),
      MvPowerSeries.C (algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).omS r)))) *
        MvPowerSeries.X ⟨v, (s, a, b)⟩
  | Sum.inr ⟨v, (r, a, b)⟩ => ∑ s ∈ univ.filter (fun s : Fin (X.G.P.n' v) => IsOddPos s),
      MvPowerSeries.C (algebraMap (K0 p) K' (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om r)))) *
        MvPowerSeries.X ⟨v, (s, a, b)⟩

def ThZA (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (Th : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    MvPowerSeries (X.ZA j) K' :=
  MvPowerSeries.subst (X.coordZA K' j) Th

def nuv (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (i : ℕ) : ℤ := nu X.t (X.G.P.lam0 v) (X.w v) j s i

def colHt (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (c : ℕ) : ℕ :=
  ((Icc 1 (NN X.G.P.m X.t j)).filter fun i => (c : ℤ) < X.nuv v j s i).card

abbrev FrI (j : ℕ) : Type := Σ v : X.Pl, Fin (X.G.P.n' v) × ℕ × Fin (NN X.G.P.m X.t j)

abbrev ColCh (j : ℕ) : Type := ∀ v : X.Pl, Fin (X.G.P.n' v) → ℕ → ℕ → Fin (NN X.G.P.m X.t (j + 1))

def colFac (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) :
    MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ) :=
  Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
    ∑ a : Fin (NN X.G.P.m X.t j),
      MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
        MvPolynomial.X (⟨v, (s, a, I v s c i'.val)⟩ : X.ZA j))

def colExp (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) : ℕ :=
  if IsOddPos s then ((range (X.colHt v (j + 1) s c)).filter fun i' => (I v s c i').val < i0 v).card
  else min (X.colHt v (j + 1) s c) (i0 v) -
    ((range (X.colHt v (j + 1) s c)).filter fun i' => (I v s c i').val < i0 v).card

def PI (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ) :=
  ∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 v s c) * X.colFac j I v s c

def PIv (j : ℕ) (I : X.ColCh j) (v : X.Pl) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colFac j I v s c

def sSA (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) : MvPowerSeries (X.ZA j) K' :=
  fun n => ∑ l ∈ range (n.degree + 1),
    if n = Finsupp.single (⟨v, (posSub e (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l)) then (-1) ^ l else 0

def hhA (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') : MvPowerSeries (X.ZA j) K' :=
  ∑ s : Fin (X.G.P.n' v), MvPowerSeries.C (u s) *
    ∑ a : Fin (NN X.G.P.m X.t j), ∑ b : Fin (NN X.G.P.m X.t (j + 1)),
      (X.sSA K' j v s a b) ^ p * X.sSA K' j v (posAdd s 1) a b

def InProdA {K' : Type} [Field K'] (R' : Subring K') (j : ℕ) (h : X.Pl → MvPowerSeries (X.ZA j) K')
    (F : MvPowerSeries (X.ZA j) K') : Prop :=
  ∃ g : (X.Pl → ℕ) → MvPowerSeries (X.ZA j) K', (∀ i, IntR R' (g i)) ∧
    ∀ α : X.ZA j →₀ ℕ, MvPowerSeries.coeff α F =
      ∑ i ∈ Fintype.piFinset (fun _ : X.Pl => range (α.degree + 1)),
        MvPowerSeries.coeff α (MvPowerSeries.C (∏ v, ((p : K') ^ i v)⁻¹) * (∏ v, h v ^ i v) * g i)

end Sys

abbrev XspC {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) (Kc : Type) [CommSemiring Kc] : Type :=
  MvPolynomial (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kc

structure Pend {p : ℕ} [Fact p.Prime] (X : Sys p) where
  Kc : Type
  [fieldKc : Field Kc]
  [algebraicConstant : Algebra (K0 p) Kc]
  [algKf : Algebra X.G.Kf Kc]
  Oc : Subring Kc
  Oc_val : ∀ x : Kc, x ∈ Oc ∨ x⁻¹ ∈ Oc
  witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc
  Oc_K : ∀ x : X.G.Kf, algebraMap X.G.Kf Kc x ∈ Oc ↔ x ∈ X.intK

  Oc_rank1 : ∀ x : Kc, x ≠ 0 → (∃ n : ℕ, (p : Kc) ^ n / x ∈ Oc) ∧ (x⁻¹ ∉ Oc → ∃ n : ℕ, x ^ n / (p : Kc) ∈ Oc)
  be : MvPowerSeries (Fin 2) (K0 p)
  Rep : ∀ j, Finset (X.Lt j)
  Rep_lat : ∀ j (La : X.Lt j), La ∈ Rep j → (X.Pj j).IsLatTup La.2
  Rep_ex : ∀ j ≤ X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup), (X.Pj j).IsLatTup L →
    ∃! L0 : (X.Pj j).Tup, (c, L0) ∈ Rep j ∧ ∃ γ : (X.Lv.lev j c).Γ, L = (X.Lv.lev j c).smul γ L0
  stab_fin : ∀ j ≤ X.mm, ∀ (La : X.Lt j), (X.Pj j).IsLatTup La.2 → 0 < X.stab j La
  Frm : ∀ j, X.Lt j → X.Lt (j + 1) → Type
  ThA : ∀ j La La', Frm j La La' → MvPowerSeries (X.EA j ⊕ X.EA j) Kc
  bc : ∀ j La La', Frm j La La' → X.ZA j → X.ZA j → Kc
  ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc
  ThF_frm : ∀ j La La' (φ : Frm j La La'),
    ThF j La La' = linSub (bc j La La' φ) (X.ThZA Kc j (ThA j La La' φ))
  DelF : ∀ j, (X.Pj j).Xsp →ₗ[X.G.Kf] MvPowerSeries (X.ZA j) Kc →ₗ[X.G.Kf] XspC (X.Pj (j + 1)) Kc
  Del_deg : ∀ j (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) Kc),
    (∀ n : X.ZA j →₀ ℕ, (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
        ((∑ a, ∑ b, n ⟨v, (s, a, b)⟩ : ℕ) : ℤ) = ∑ i ∈ Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i) →
      MvPowerSeries.coeff n f = 0) → DelF j G f = 0
  len : X.Pl → ∀ j, (X.Pj j).Tup → ℤ
  len_edge : ∀ j (v' : Fin (X.Pj j).nV) (i : ℕ) (L : (X.Pj j).Tup)
    (L'' : Submodule ((X.Pj j).W v') (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq v')),
    IsEdge p ((X.Pj j).n' v') i ⟨L'', L v'⟩ →
      len (X.vB j v') j (Function.update L v' L'') = len (X.vB j v') j L - i
  len_other : ∀ j (v' : Fin (X.Pj j).nV) (v : X.Pl) (L : (X.Pj j).Tup)
    (L'' : Submodule ((X.Pj j).W v') (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq v')),
    v ≠ X.vB j v' → len v j (Function.update L v' L'') = len v j L
  Aw : X.Pl → ℕ → Type
  aw : ∀ v j, X.Lt j → X.Lt (j + 1) → Aw v j
  weight_update_at_place : ∀ v j (La : X.Lt j) (La' : X.Lt (j + 1))
    (L'' : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v))),
    aw v j (La.1, Function.update La.2 (X.vJ j v) L'') La' = aw v j La La'
  aw_tgt : ∀ v j (La : X.Lt j) (La' : X.Lt (j + 1))
    (L'' : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v))
      (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v))),
    aw v j La (La'.1, Function.update La'.2 (X.vJ (j + 1) v) L'') = aw v j La La'
  Xi : ∀ v j, Aw v j →
    ((Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) →+ MvPowerSeries (X.ZA j) Kc)

attribute [instance] Pend.fieldKc Pend.algebraicConstant Pend.algKf

namespace Pend

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

def ThV (v : X.Pl) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (φ : Y.Frm j La La') :
    MvPowerSeries (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
      Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) Y.Kc :=
  resV (Sum.map (fun e => (⟨v, e⟩ : X.EA j)) (fun e => (⟨v, e⟩ : X.EA j))) (Y.ThA j La La' φ)

def PhAt (j : ℕ) (v : X.Pl) : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p) :=
  ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
    sub2 p Y.be (MvPowerSeries.X (Sum.inl ⟨v, e⟩)) (MvPowerSeries.X (Sum.inr ⟨v, e⟩))

def eS (j : ℕ) (La : X.Lt j) : X.G.Kf := ∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * Y.len v j La.2)

def eT (j : ℕ) (La' : X.Lt (j + 1)) : X.G.Kf :=
  ∏ v : X.Pl, (p : X.G.Kf) ^ (X.vm v (j + 1) * Y.len v (j + 1) La'.2)

def kerF (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (f : MvPowerSeries (X.ZA j) Y.Kc) (G : (X.Pj j).Xsp) :
    XspC (X.Pj (j + 1)) Y.Kc :=
  (Y.eS j La * (Y.eT j La')⁻¹) • Y.DelF j G f

def ker (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G : (X.Pj j).Xsp) : XspC (X.Pj (j + 1)) Y.Kc :=
  Y.kerF j La La' (Y.ThF j La La') G

def geC (x : Y.Kc) (g : ℝ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℝ) ≤ g * b → x ^ b * (p : Y.Kc) ^ (-a) ∈ Y.Oc

def inLatC (j : ℕ) (g : ℝ) (L : (X.Pj j).Tup) (y : XspC (X.Pj j) Y.Kc) : Prop :=
  y ∈ AddSubgroup.closure {y' | ∃ a : Y.Kc, Y.geC a g ∧ ∃ z ∈ (X.Pj j).HtupW L,
    y' = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) z}

def LowAt (j : ℕ) (v : X.Pl) (g : ℝ) : Prop :=
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (MvPolynomial.coeff n (applyD (X.PIv j I v)
        (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U)))) g

theorem geC_mono {x : Y.Kc} {g g' : ℝ} (h : g' ≤ g) (hx : Y.geC x g) : Y.geC x g' := by
  intro a b hb hab
  exact hx a b hb (hab.trans (mul_le_mul_of_nonneg_right h (by exact_mod_cast hb.le)))

theorem LowAt.mono {j : ℕ} {v : X.Pl} {g g' : ℝ} (h : g' ≤ g) (hg : Y.LowAt j v g) : Y.LowAt j v g' := fun U hU I n => Y.geC_mono h (hg U hU I n)

def volE (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup) : ℤ :=
  (NN X.G.P.m X.t j : ℤ) * Y.len v (j + 1) L' - (NN X.G.P.m X.t (j + 1) : ℤ) * Y.len v j L

end Pend

def adm1 (_D : Formalism.BasicNotions.D7) : Prop := ∀ (p : ℕ) [Fact p.Prime], DworkLemma p

def adm2 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ v, ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La'), ExtensionLocalCondition p Y.Kc Y.Oc Y.be (Y.ThV v j La La' φ)

def adm2b (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La'), ExtensionGeneratorCondition p Y.Kc Y.Oc Y.be (Y.ThA j La La' φ)

def adm2c (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop := BeProp p Y.be

def adm3 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA Y.Kc j (Y.ThA j La La' φ)))) 0

def adm3b (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ j < X.mm, ∀ F ∈ X.FQ j, X.Kz j F ∈ X.FQ (j + 1)

def ExpansionEquality (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) : Prop :=
  ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧
    ∀ F ∈ X.FQ j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2)

def ExpansionDecomposition (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) : Prop :=
  ∃ cK : Y.Kc, cK ∈ Y.Oc ∧ cK⁻¹ ∈ Y.Oc ∧
    ∃ (Cl Yb : Type) (_ : Fintype Cl) (_ : Fintype Yb) (wt : Cl → ℕ) (La : Cl → Yb → X.Lt j),
      (∀ x y, (X.Pj j).IsLatTup (La x y).2) ∧
      (∀ x, 0 < wt x ∧ padicValNat p (wt x) ≤ X.dG j) ∧
      (∀ F ∈ X.FQ j, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
        MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
          ∑ x : Cl, (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb, Y.ker j (La x y) (c', L') (F (La x y).1 (La x y).2)) ∧
      ∀ (v : X.Pl) (i : ℕ), ∀ F ∈ X.FQ j, ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
        ∑ x : Cl, ((wt x : Y.Kc))⁻¹ • ∑ y : Yb,
            ∑ᶠ (L1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
              (_ : IsEdge p ((X.Pj j).n' (X.vJ j v)) i ⟨(La x y).2 (X.vJ j v), L1⟩),
              Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) L1) La' (F (La x y).1 (La x y).2) =
          ∑ x : Cl, ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, Y.ker j (La x y) La' (X.Tm v i j F (La x y).1 (La x y).2)

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  (∀ j, j + 1 < X.mm → ExpansionEquality D X Y j) ∧ ∀ j, j + 1 = X.mm → ExpansionDecomposition D X Y j

def adm5 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ v, ∀ j < X.mm, ∃ u u' : X.G.Kf, X.vEqK u 0 ∧ X.vEqK u' 0 ∧
    ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      Y.ThF j La La' = (u ^ (Y.len v j La.2) * u' ^ (Y.len v (j + 1) La'.2) *
        (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * Y.volE v j La.2 La'.2))) •
        Y.Xi v j (Y.aw v j La La') (X.ind v j La.2 La'.2)

def MinkowskiCounting (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j < X.mm, ∀ (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ)
    (G : (X.Pj j).Xsp), G ∈ (X.Pj j).Vtup → (X.Pj j).IsLatTup L → (X.Pj (j + 1)).IsLatTup La'.2 →
      Y.ker j (c, (X.Lv.lev j c).smul γ L) La' ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G) =
        Y.ker j (c, L) La' G

def adm6 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j ≤ X.mm, ∀ (v' : Fin (X.Pj j).nV) (i : ℕ) (φ : X.Lv.comp j → (X.Pj j).Tup → (X.Pj j).Tup → Y.Kc),
    (∀ c (γ : (X.Lv.lev j c).Γ) L L1, φ c ((X.Lv.lev j c).smul γ L) ((X.Lv.lev j c).smul γ L1) = φ c L L1) →
    ∑ La ∈ Y.Rep j, ((X.stab j La : Y.Kc))⁻¹ *
        ∑ᶠ (L1 : Submodule ((X.Pj j).W v') (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq v'))
          (_ : IsEdge p ((X.Pj j).n' v') i ⟨La.2 v', L1⟩), φ La.1 La.2 (Function.update La.2 v' L1) =
      ∑ La1 ∈ Y.Rep j, ((X.stab j La1 : Y.Kc))⁻¹ *
        ∑ᶠ (L0 : Submodule ((X.Pj j).W v') (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq v'))
          (_ : IsEdge p ((X.Pj j).n' v') i ⟨L0, La1.2 v'⟩), φ La1.1 (Function.update La1.2 v' L0) La1.2

def adm7 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (c' : X.Lv.comp (j + 1)) (L' L'' : (X.Pj (j + 1)).Tup) (i0 : X.Pl → ℕ),
    (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup L' → (∀ v, i0 v ≤ X.G.P.r) →
    (∀ v' : Fin (X.Pj (j + 1)).nV, (i0 (X.vB (j + 1) v') = 0 ∧ L'' v' = L' v') ∨
      (1 ≤ i0 (X.vB (j + 1) v') ∧ IsEdge p ((X.Pj (j + 1)).n' v') (i0 (X.vB (j + 1) v')) ⟨L'' v', L' v'⟩)) →
    ∃ φ : Y.Frm j La (c', L''), ∀ (f : MvPowerSeries (X.ZA j) Y.Kc) (g : ℝ),
      (∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ), Y.geC (MvPolynomial.coeff n (applyD (X.PI j I i0) f)) g) →
      ∀ G ∈ (X.Pj j).HtupW La.2, Y.inLatC (j + 1) g L'
        ((∏ v : X.Pl, (p : X.G.Kf) ^ (Nprime (X.G.P.lam0 v) (X.w v) (j + 1) (i0 v))) •
          Y.kerF j La (c', L'') (linSub (Y.bc j La (c', L'') φ) f) G)

def adm8 (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  Formalism.MainNotions.SelectionLemmas.adm3 D X.G ∧ ∀ v, ∀ F ∈ X.G.M, X.G.yv v F ∈ X.G.M

def adm11 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ v, ∀ j < X.mm, Y.LowAt j v 0

def Conclusion0 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ j < X.mm, ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Kz j G) (-(X.dG j : ℝ))

def Conclusion1 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ v, ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La'), SConcl (X.om v) Y.Kc Y.Oc (Y.ThV v j La La' φ)

def ExpansionsMultiply (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra Y.Kc K']
    [IsScalarTower (K0 p) Y.Kc K'] (R' : Subring K') (vp : K'),
    vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ Y.Oc, algebraMap Y.Kc K' x ∈ R') →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ R') ∧
      ∀ h' : X.Pl → MvPowerSeries (X.ZA j) K',
        (∀ v, MvPowerSeries.constantCoeff (h' v) = 0 ∧ ∃ G : MvPowerSeries (X.ZA j) K', IntR R' G ∧
          h' v = X.hhA K' j v (u v) + MvPowerSeries.C (p : K') * G) →
        X.InProdA R' j h'
          (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j (Y.ThA j La La' φ))))

def Conclusion2 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ j < X.mm, ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Kz j G) (∑ v, X.g0v v (j + 1) - X.dG j)

def projection_lemma_base_level (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La') (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (MvPolynomial.coeff n (applyD (X.PI j I fun _ => 0) (X.ThZA Y.Kc j (Y.ThA j La La' φ))))
        (∑ v, X.g0v v (j + 1))

def VolumeRatio₂ (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ v, ∀ j < X.mm, Y.LowAt j v (X.g0v v (j + 1))

def MassRatio₂ (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ v, ∀ j < X.mm, ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Kz j G)
    (X.gv v (j + 1) - X.alEven v + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j)

def PointsLemma (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ v, ∀ j < X.mm,
    (∀ i ∈ Icc 1 X.G.P.r, ∀ F ∈ X.Int (j + 1), X.Tt v i (j + 1) F ∈ X.Int (j + 1)) ∧
    (∀ i ∈ Icc 1 X.G.P.r, ∀ G ∈ X.Int j, X.vGe (j + 1) (X.Tt v i (j + 1) (X.Kz j G))
      (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j))

def Conclusion4 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ v, ∃ u m : ℕ → X.G.Kf, (∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0) ∧ (∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) ∧
    ∀ j < X.mm,
      (∀ F ∈ X.FQ 0, X.Zop v u m (j + 1) (X.chainK (j + 1) F) =
        ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F)) ∧
      (∀ l ≤ X.G.P.r, X.vGeK (X.cl v m (j + 1) l) 0) ∧
      X.vGeK (X.cl v m (j + 1) X.G.P.r) (X.alEven v) ∧
      (∀ G ∈ X.Int j, X.vGe (j + 1) (X.Zop v u m (j + 1) (X.Kz j G))
        (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j))

def mHat {K : Type} [Field K] (u m : ℕ → K) (l : ℕ) : K := m l * (∏ l' ∈ Icc 1 (l - 1), u l')⁻¹

def KernelCommutationUpToUnits (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ v, ∃ u m : ℕ → X.G.Kf, (∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0) ∧ (∀ l ∈ Icc 1 X.mm, X.vEqK (m l) (X.vm v l)) ∧
    ∀ j < X.mm,
      (∀ i : ℕ, ∀ F ∈ X.FQ j, X.ecal v i (j + 1) (X.Kz j F) =
        (u (j + 1) ^ i) • X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => m (j + 1) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)) ∧
      (∀ F ∈ X.FQ 0, X.Zop v u (mHat u m) (j + 1) (X.chainK (j + 1) F) =
        ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F)) ∧
      (∀ l ≤ X.G.P.r, X.vGeK (X.cl v (mHat u m) (j + 1) l) 0) ∧
      X.vGeK (X.cl v (mHat u m) (j + 1) X.G.P.r) (X.alEven v) ∧
      (∀ G ∈ X.Int j, X.vGe (j + 1) (X.Zop v u (mHat u m) (j + 1) (X.Kz j G))
        (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j))

def Conclusion5 (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  (∀ v, X.Svv v ≤ (X.mm : ℝ) * gam p * ∑ s ∈ X.TT v, (X.alv v s : ℝ)) ∧
  ∀ VV : Finset X.Pl, ∀ F ∈ X.Iprod X.Svv VV, X.vGe X.mm (X.chainK X.mm F)
    (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (X.gv v j - X.Conclusion₂ v j) (X.g0v v j) + ∑ v ∈ univ \ VV, X.g0v v j) -
      ∑ j ∈ range X.mm, (X.dG j : ℝ))

def RelativePresentationLiterature (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' k1 t m c r : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ), Std p n' k1 t m c r TT a b lam0 w →
    Sv p t m r TT lam0 w ≤ (m : ℝ) * gam p * ∑ s ∈ TT, (al TT lam0 s : ℝ)

def LowTermBound (_D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  ∀ (Gn G0n PRn : X.Pl → ℕ → ℝ) (S : X.Pl → ℝ) (VV : Finset X.Pl),
    (∀ v ∈ VV, ∀ j ∈ Icc 1 X.mm, Gn v j ≤ X.gv v j) →
    (∀ v, ∀ j < X.mm, Y.LowAt j v (G0n v (j + 1))) →
    (∀ v ∈ VV, ∀ j ∈ Icc 1 X.mm, X.Conclusion₂ v j ≤ PRn v j) →
    (∀ v ∈ VV, ∑ j ∈ Icc 1 X.mm, max (Gn v j - PRn v j - G0n v j) 0 ≤ S v) →
    ∀ F ∈ X.Iprod S VV, X.vGe X.mm (X.chainK X.mm F)
      (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ))

theorem lowAt_max (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (hU : VolumeRatio₂ D X Y)
    (hZ : adm11 D X Y) (v : X.Pl) (j : ℕ) (hj : j < X.mm) (g : ℝ) (hg : g ≤ max (X.g0v v (j + 1)) 0) :
    Y.LowAt j v g := by
  rcases le_total (X.g0v v (j + 1)) 0 with h0 | h0
  · rw [max_eq_right h0] at hg
    exact Pend.LowAt.mono Y hg (hZ v j hj)
  · rw [max_eq_left h0] at hg
    exact Pend.LowAt.mono Y hg (hU v j hj)

def NumCmp (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
      Formalism.MainNotions.G.gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤
        Formalism.MainNotions.FormalGroupSystem.gB (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
          ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ∧
      Formalism.MainNotions.G.g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤
        Formalism.MainNotions.FormalGroupSystem.gA (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
          ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ∧
      Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
                ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
        Formalism.MainNotions.G.Pr X K (bL L) (D.what₂.places.resChar w) j t0

def SmallResidueCharComparison (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ hT : GatTies D, LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
    ∀ t0 ∈ reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
      Formalism.MainNotions.G.gU X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤
        Formalism.MainNotions.FormalGroupSystem.gB (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
          ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ∧
      Formalism.MainNotions.G.g0 X K (aL L) (bL L) (D.what₂.places.resChar w) j t0 ≤
        Formalism.MainNotions.FormalGroupSystem.gA (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
          ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ∧
      Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
                ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
        Formalism.MainNotions.G.Pr X K (bL L) (D.what₂.places.resChar w) j t0

theorem NumCmp.k5 {D : Formalism.BasicNotions.D7} {L : SizeData₂ D} {X : Inst D L} {Y : LatInst D} {K : Consts}
    (h : NumCmp D L X Y K) : SmallResidueCharComparison D L X Y K := fun hT hL u w hg _ => h hT hL u w hg

def NumericalComparisonAt (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (C₀ : ℝ) : Prop :=
  ∀ K : Consts, C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → Formalism.MainNotions.G.rG L.sc < D.R.k → 2 ≤ L.sc.x → Formalism.MainNotions.SizesAt L →
    SmallResidueCharComparison D L X Y K

def NumericalComparison (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) : Prop := ∃ C₀, NumericalComparisonAt D L X Y C₀

def NumericalComparisonUniform : Prop :=
  ∃ C₀ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D), NumericalComparisonAt D L X Y C₀

def NumericalComparisonFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), NumericalComparisonAt (Fm.D x i) (Fm.L x i) (Fm.Gx x i) (Fm.Gy x i) C₀

def admitted (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  adm1 D ∧ adm2 D X Y ∧ adm2b D X Y ∧ adm2c D X Y ∧ adm3 D X Y ∧ adm3b D X ∧ ArchimedeanSignatureMatching D X Y ∧ adm5 D X Y ∧ MinkowskiCounting D X Y ∧ adm6 D X Y ∧
    adm7 D X Y ∧ adm8 D X ∧ adm11 D X Y

def Conclusion₂ (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) : Prop :=
  Conclusion0 D X ∧ Conclusion1 D X Y ∧ ExpansionsMultiply D X Y ∧ Conclusion2 D X ∧ projection_lemma_base_level D X Y ∧ VolumeRatio₂ D X Y ∧ MassRatio₂ D X ∧ PointsLemma D X ∧ Conclusion4 D X ∧
    Conclusion5 D X ∧ LowTermBound D X Y

def Stmt (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), admitted D X Y → Conclusion₂ D X Y) ∧ RelativePresentationLiterature D

def DegreeDichotomyWithModelBounds (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X), admitted D X Y → KernelCommutationUpToUnits D X

def ErrorExponentStatement (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) [Fact (D.what₂.places.resChar w).Prime]
    (h : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (X : Sys (D.what₂.places.resChar w)) (Y : Pend X),
    X.G = D.gat u w h → admitted D X Y → Conclusion₂ D X Y

def ClosedFormOfAdmitted (D : Formalism.BasicNotions.D7) : Prop := Stmt D

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), Stmt (Fm.D x i)

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := KudlaFamilyStatement Fm

def DegreeDichotomyWithModelBoundsFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), DegreeDichotomyWithModelBounds (Fm.D x i)

def adm9 (D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : Prop := Formalism.MainNotions.SelectionLemmas.Conclusion1 D G

def adm10 (_D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : Prop := G.Sandwich

def adm12 (_D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : Prop :=
  (∀ v, ∀ F ∈ G.Mna, G.yv v F ∈ G.Mna) ∧ ∀ v, ∀ F ∈ G.M, G.yv v F ∈ G.M

def adm13 (D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : Prop := Formalism.MainNotions.SelectionLemmas.adm2 D G

def Adm6 (D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : Prop :=
  adm9 D G ∧ adm10 D G ∧ adm12 D G ∧ adm13 D G ∧ Formalism.MainNotions.SelectionLemmas.adm3 D G

def Conclusion6 (_D : Formalism.BasicNotions.D7) {p : ℕ} (G : GAtP p) : Prop :=
  ∀ (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd cStar S m : ℕ) (κ : Fin G.P.nV → ℝ)
    (V' : Submodule G.O G.Fn),
    1 ≤ m → (∀ v ∈ VV, Sv v ≤ S) →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w
      G.P.r (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    Formalism.MainNotions.SelectionLemmas.IsSaturatedIn (G.M ⊓ V') G.M →
    (m : ℝ) * ∑ v ∈ VV, κ v ≤ 1 / 2 →
    let tauP : ℕ := G.e + Formalism.MainNotions.SelectionLemmas.tau VV m Dd t
    let Mp := G.M ⊓ V'
    let NPp := Formalism.MainNotions.SelectionLemmas.prodIdeal G VV m Sv G.M ⊓ (Ideal.span {(p : G.O) ^ tauP}) • G.M ⊓ V'
    NPp ≤ (Ideal.span {(p : G.O) ^ tauP}) • Mp ∧
    ∃ ℓ : ℕ, Module.length G.O (↥Mp ⧸ Submodule.comap Mp.subtype NPp) = ℓ ∧
      (ℓ : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
        ((G.d : ℝ) * ((tauP : ℝ) + 2 * S * ((m : ℝ) * ∑ v ∈ VV, κ v)))

def ShareFromInputs (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    0 < (D.gat u w h).P.nV → Adm6 D (D.gat u w h) → Conclusion6 D (D.gat u w h)

def LocalServiceStatement (D : Formalism.BasicNotions.D7) : Prop := ∀ (p : ℕ) (G : GAtP p), 0 < G.P.nV → Adm6 D G → Conclusion6 D G

def LemmaVVolumeGeneral (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (cStar : ℕ),
    let p := D.what₂.places.resChar w
    let G := D.gat u w hg
    let Mram := G.M ⊓ Y.Vram u w hg
    let VVp := Formalism.MainNotions.G.VV X K (aL L) (bL L) p
    (G.Mna.map (((p : G.O) ^ X.ep p) • LinearMap.id) ≤ G.M ∧ G.M ≤ G.Mna) → 1 ≤ D.R.m → Set.InjOn (Y.vOf u w hg) (VVp : Set (HH D)) →
    (∀ t0 ∈ VVp, LPprime (W := G.P.W (Y.vOf u w hg t0)) (Qq := G.P.Qq (Y.vOf u w hg t0)) (O := G.O) (Kf := G.Kf) p
      (G.P.n' (Y.vOf u w hg t0)) (G.P.ι (Y.vOf u w hg t0)) (G.P.σ (Y.vOf u w hg t0)) G.P.w G.P.r
      (G.P.lam0 (Y.vOf u w hg t0)) ⌈tv X K (aL L) (bL L) p t0⌉₊ (Dp K L p) (kapv X K (aL L) (bL L) p t0) cStar) →
    Formalism.MainNotions.SelectionLemmas.IsSaturatedIn Mram G.M →
    (D.R.m : ℝ) * ∑ t0 ∈ VVp, kapv X K (aL L) (bL L) p t0 ≤ 1 / 2 →
    NP X Y K u w hg ≤ Mram.map (((p : G.O) ^ ⌈tauP X K (aL L) (bL L) p⌉.toNat) • LinearMap.id) ∧
    (∃ l : ℕ, Module.length G.O (↥Mram ⧸ (NP X Y K u w hg).comap Mram.subtype) = l ∧
      (l : ℝ) ≤ vUnit G * (G.d : ℝ) * (tauP X K (aL L) (bL L) p + ioP X K (aL L) (bL L) p))

def RamifiedSublatticeVolumeOfAdmissible (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) : Prop :=
  (∀ (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    adm9 D (D.gat u w h) ∧ adm12 D (D.gat u w h) ∧ adm13 D (D.gat u w h) ∧ Formalism.MainNotions.SelectionLemmas.adm3 D (D.gat u w h)) →
    LemmaVVolumeGeneral D L X Y K

def ShareFromInputsFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), ShareFromInputs (Fm.D x i)

end Formalism.MainNotions.FormalGroupSystem
