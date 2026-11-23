import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RestNonneg
import Development.AutomorphicArithmetic.OrbitLabellings.RowDefs
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators

def parAt (N : NumDatum) (j d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) : RF.Par where
  Pl := RPl N.R
  k := N.R.k
  m := N.R.m
  r := N.R.r
  f := N.R.f
  d := d
  pos := pos
  w := N.w j
  SE := N.Sc + N.eta

def parOf (N : NumDatum) (j l : ℕ) : RF.Par := parAt N j (N.ordP l) (N.pos l)

structure ParOK (P : RF.Par) : Prop where
  card : Fintype.card P.Pl = P.f
  m_pos : 1 ≤ P.m
  mk_le : P.m + 3 ≤ P.k
  r_eq : P.r = P.k - 1 + P.m
  SE_nonneg : 0 ≤ P.SE

def errB (P : RF.Par) (l : ℕ) (T : ℝ) : ℝ :=
  Real.log P.k * P.m * (∑ z, P.w z) / l + P.f * P.k * P.SE / l + P.k * thl P.k l * (∑ z, P.w z) +
    T * P.f * ((P.k : ℝ) - 1) ^ 3 * Real.log P.k ^ 2

def Inert (N : NumDatum) (l : ℕ) : Prop := N.cls l = PrimeClass.inertClass ∨ N.cls l = PrimeClass.signal

def PhiC (N : NumDatum) (l : ℕ) : Prop := N.cls l = PrimeClass.inertClass ∧ N.hP l = 0

def ConjIn (N : NumDatum) (l : ℕ) : Prop := N.cls l = PrimeClass.inertClass ∧ Odd (addOrderOf (N.hP l))

theorem PhiC.conjIn {N : NumDatum} {l : ℕ} (h : PhiC N l) : ConjIn N l :=
  ⟨h.1, by rw [h.2, addOrderOf_zero]; exact odd_one⟩

theorem even_ordP_of_not_conjIn {N : NumDatum} {l : ℕ} (hI : Inert N l) (hC : ¬ ConjIn N l) : Even (N.ordP l) := by
  unfold NumDatum.ordP
  by_cases hc : N.cls l = PrimeClass.signal
  · rw [if_pos hc]; exact even_two_mul _
  · rw [if_neg hc]
    exact Nat.not_odd_iff_even.1 fun h => hC ⟨hI.resolve_right hc, h⟩

theorem ne_two_of_not_small {N : NumDatum} {l : ℕ} (h : l ∉ N.H.small) : l ≠ 2 := by
  rintro rfl
  exact h (Nat.mem_primeFactors.2 ⟨Nat.prime_two, (dvd_pow_self 2 (by omega)).trans N.H.tower_dvd, N.H.QS_pos.ne'⟩)

section Objects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def gapW (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) (z : RPl N.R) : ℕ :=
  a (pl z, N.R.k - 2) - a (pl z, N.R.k - 1)

def restOf (N : NumDatum) (Dw : Datum H) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  (DF Dw a : ℝ) - ((N.R.k : ℝ) - 1) * ∑ z, (gapW N pl a z : ℝ)

structure PlaceTie (N : NumDatum) {lv : Level H} (c : Coeff lv) (pl : RPl N.R → (E →+* ℂ)) : Prop where
  inj : Function.Injective pl
  psi : ∀ τ, InPsi H τ ↔ ∃ z, pl z = τ
  d_eq : H.d = N.d
  galois : IsGalois ℚ E
  comm : ∀ σ σ' : E ≃ₐ[ℚ] E, σ * σ' = σ' * σ
  unr : ∀ p : ℕ, p.Prime → p ∉ N.H.small → p ≠ N.q → p ≠ N.d → ¬ (p : ℤ) ∣ NumberField.discr E
  frob : ∀ la : HeightOneSpectrum (𝓞 c.F), Inert N (resCharOf la) → ∀ (z : RPl N.R) (x : 𝓞 E),
    ∃ y ∈ la.asIdeal, ((y : 𝓞 c.F) : c.F) =
      embK c (ComplexEmbedding.conjugate (pl (N.pos (resCharOf la) z 1))) x - embK c (pl z) x ^ resCharOf la

structure GoodPage (N : NumDatum) (j : ℕ) (Dw : Datum H) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ)
    (nW T : ℕ) (C1 b L : ℝ) : Prop where
  deg : ∃ θ0 : ℝ, RF.DegHyp2 (parAt N j 1 fun z _ => z) (gapW N pl a) T θ0 (restOf N Dw pl a) C1
  first : ∀ τ, 0 < Dw.mult τ → (T : ℝ) * a (τ, 0) ≤ 3 * b
  what₂ : 10 * (N.R.r : ℝ) * (N.R.f + (N.R.f : ℝ) ^ 2 * ((N.R.k : ℝ) - 1) ^ 3 * L ^ 2 / N.R.m) ≤ nW
  L_ge : 3 ≤ L
  log_le : Real.log N.R.k ≤ L
  inert_ge : ∀ p : ℕ, p.Prime → Inert N p → 5 ≤ p
  ratio : ∀ z z', N.w j z' ≤ N.sc.X'' N.R.n * N.w j z

variable {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)]

def AllPts (Φ : ∀ (N : NumDatum) (_j _l : ℕ) (_pl : RPl N.R → (E →+* ℂ)) (_a : (E →+* ℂ) × ℕ → ℕ) (_nW : ℕ) (_ν : ℝ), Prop) :
    Prop :=
  (∀ x : 𝓞 E, star x = H.bar x) →
  ∀ (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ), 1 ≤ j → j ≤ N.R.m →
    PlaceTie N c pl → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a →
    ∀ la : HeightOneSpectrum (𝓞 c.F), resCharOf la ∉ N.H.small → resCharOf la ≠ N.q → resCharOf la ≠ N.d →
      ¬ resCharOf la ∣ lv.M → (Inert N (resCharOf la) → 5 ≤ resCharOf la) →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
    ∀ (C : IntChart T io y) (nW : ℕ) (ν : ℝ),
      (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → Φ N j (resCharOf la) pl a nW ν

def PkgInertSt : Prop :=
  AllPts Xo c fun N j l pl a nW ν => Inert N l → ¬ ConjIn N l → ∀ T θ0 C1 : ℝ,
    RF.DegHyp2 (parOf N j l) (gapW N pl a) T θ0 (restOf N Dw pl a) C1 →
    N.R.f * (RF.i0 N.R.k l * (N.R.k - 1)) + 2 * N.R.r * N.R.f ≤ nW →
    ∃ Pk : RF.PkgInert (parOf N j l) l C1, Pk.T = T ∧ Pk.ν = ν

def PkgPhiCSt : Prop :=
  AllPts Xo c fun N j l pl a nW ν => PhiC N l → ∀ T θ0 C1 : ℝ,
    RF.DegHyp2 (parOf N j l) (gapW N pl a) T θ0 (restOf N Dw pl a) C1 → 8 * N.R.r * N.R.f ≤ nW →
    ∃ Pk : RF.PkgPhiC (parOf N j l) l C1, Pk.T = T ∧ Pk.ν = ν

def PkgSplitSt : Prop :=
  AllPts Xo c fun N j l pl a nW ν => N.cls l = PrimeClass.splitK → ∀ T θ0 C1 : ℝ,
    RF.DegHyp2 (parAt N j 1 fun z _ => z) (gapW N pl a) T θ0 (restOf N Dw pl a) C1 → 4 * N.R.r * N.R.f ≤ nW →
    ∃ (d : ℕ) (_ : NeZero d) (pos : RPl N.R → ℕ → RPl N.R) (Pk : RF.PkgSplit (parAt N j d pos) l C1), Pk.T = T ∧ Pk.ν = ν

def PkgZeroSt : Prop :=
  AllPts Xo c fun N j l _ a nW ν => ¬ ConjIn N l → (∀ z, 0 ≤ N.w j z) → ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) →
    2 * N.R.r * s * N.R.f ≤ nW →
    ∃ (d : ℕ) (_ : NeZero d) (pos : RPl N.R → ℕ → RPl N.R) (Pk : RF.PkgZero (parAt N j d pos) l), Pk.ν = ν

def PkgZeroCSt : Prop :=
  AllPts Xo c fun N j l _ a nW ν => PhiC N l → (∀ z, 0 ≤ N.w j z) → ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) →
    4 * N.R.r * s * N.R.f ≤ nW →
    ∃ Pk : RF.PkgZeroC (parOf N j l) l, Pk.ν = ν

def PkgCsSt : Prop :=
  AllPts Xo c fun N j l pl a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) → ∀ T θ0 C1 : ℝ,
    RF.DegHyp2 (parOf N j l) (gapW N pl a) T θ0 (restOf N Dw pl a) C1 →
    N.R.f * ((RF.i0 N.R.k l + 1) * (N.R.k - 1) + 4 * N.R.r) ≤ nW →
    ∃ Pk : UpperTheory.G2.PkgCs (parOf N j l) l C1, Pk.T = T ∧ Pk.ν = ν

def PkgZeroCsSt : Prop :=
  AllPts Xo c fun N j l _ a nW ν => N.cls l = PrimeClass.inertClass → Odd (N.ordP l) → (∀ z, 0 ≤ N.w j z) →
    ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
    ∃ Pk : UpperTheory.G2.PkgZeroCs (parOf N j l) l, Pk.ν = ν

def PkgSt : Prop := PkgInertSt Xo c ∧ PkgPhiCSt Xo c ∧ PkgSplitSt Xo c ∧ PkgZeroSt Xo c ∧ PkgZeroCSt Xo c ∧
  PkgCsSt Xo c ∧ PkgZeroCsSt Xo c

end Objects

def InertBd : Prop :=
  ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (P : RF.Par) (l : ℕ), ParOK P → l.Prime → 5 ≤ l →
    ∀ Pk : RF.PkgInert P l C1,
      Pk.T * Pk.ν ≤ (∑ z ∈ Pk.Z, Fnum l P.d fun s => ((P.k : ℝ) - 1) * RF.alongOrb P z P.w s) + Cc * errB P l Pk.T

def PhiCBd : Prop :=
  ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (P : RF.Par) (l : ℕ), ParOK P → l.Prime → 5 ≤ l →
    ∀ Pk : RF.PkgPhiC P l C1,
      Pk.T * Pk.ν ≤ ((P.k : ℝ) - 1) * (∑ z, P.w z) / ((l : ℝ) ^ 2 - 1) + Cc * errB P l Pk.T

def SplitBd : Prop :=
  ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧ ∀ (P : RF.Par) (l : ℕ), ParOK P → l.Prime →
    ∀ Pk : RF.PkgSplit P l C1, Pk.T * Pk.ν ≤ Cc * ((P.m * (∑ z, P.w z) + P.f * P.k * P.SE) / l)

def ZeroBd : Prop :=
  (∀ (P : RF.Par) (l : ℕ) (Pk : RF.PkgZero P l), Pk.ν ≤ 0) ∧ ∀ (P : RF.Par) (l : ℕ) (Pk : RF.PkgZeroC P l), Pk.ν ≤ 0

def NuGoodSt : Prop :=
  ∀ C1 : ℝ, 0 ≤ C1 → ∃ Cc : ℝ, 0 < Cc ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H)
      (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → IntChartEx Xo c → PkgSt Xo c →
    ∀ (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) (nW T : ℕ) (b L w : ℝ), 1 ≤ j → j ≤ N.R.m →
      PlaceTie N c pl → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a → GoodPage N j Dw pl a nW T C1 b L →
      (∑ z, N.w j z) ≤ w → b ≤ w →
    ∀ la : HeightOneSpectrum (𝓞 c.F), resCharOf la ∉ N.H.small → resCharOf la ≠ N.q → resCharOf la ≠ N.d →
      resCharOf la ≠ N.g 0 → resCharOf la ≠ N.g 1 → ¬ resCharOf la ∣ lv.M →
      nuW Xo c la lv.M a nW ≠ ⊤ ∧
      (T : ℝ) * ((nuW Xo c la lv.M a nW).toReal / (ramOverZ la : ℝ)) ≤ N.FjP j (resCharOf la) +
        Cc * (Real.log N.R.k * N.R.m * w / resCharOf la + N.R.f * N.R.k * (N.Sc + N.eta) / resCharOf la +
          N.R.k * thl N.R.k (resCharOf la) * w +
          if N.sc.X'' N.R.n < (resCharOf la : ℝ) then N.R.k * w / (resCharOf la : ℝ) ^ 2 else 0) ∧
      (DF Dw a < resCharOf la → nuW Xo c la lv.M a nW = 0)

open Formalism.L2.Indef Formalism.L2.Indef.Tree in

structure NumTie {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df}
    {P : Type} [Group P] [Finite P] {oc : OnConst} (O : OnObj S P oc) (N : NumDatum) (ι : Bs.J → ℕ) (DL : Bs.J → ℕ) : Prop where
  k_eq : O.k = N.R.k
  m_eq : O.m = N.R.m
  f_eq : O.f = N.R.f
  Se_ge : N.Sc + N.eta ≤ O.Se
  depthNumbers_threshold_eq : O.X2 = N.sc.X'' N.R.n
  th_eq : ∀ l, O.th l = thl N.R.k l
  ad_eq : ∀ l, O.ad l = 0
  wt_sum : ∀ j, (∑ z, N.w (ι j) z) ≤ O.wt j
  wt_b : ∀ j, O.b ≤ O.wt j
  DF_ge : ∀ j, (DL j : ℝ) ≤ O.DF

open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond in

def LeafGoodSt : Prop :=
  ∀ C1 : ℝ, 0 ≤ C1 → ∃ C0 : ℝ,
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H)
      (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
      (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)]
      [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst)
      (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)),
      C0 ≤ oc.C →
      (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) →
      (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
      O.T = ((Dd.Q.T : ℕ) : ℝ) → (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) →
      PiSplit (H := H) Dd → LevelQ (l := lv) Dd → (∀ x : 𝓞 E, star x = H.bar x) →
      (∀ j, IntChartEx (Xo (ι j)) c) → (∀ j, PkgSt (Xo (ι j)) c) → PlaceTie N c pl →
      (∀ j, 1 ≤ ι j ∧ ι j ≤ N.R.m ∧ (Dw (ι j)).p = (N.R.sigW (ι j)).1 ∧ (Dw (ι j)).q = (N.R.sigW (ι j)).2 ∧
        DomW (Dw (ι j)) (Dd.aL (ι j)) ∧
        GoodPage N (ι j) (Dw (ι j)) pl (Dd.aL (ι j)) (Dd.nW (ι j)) Dd.Q.T C1 O.b O.L) →
      NumTie O N ι (fun j => DF (Dw (ι j)) (Dd.aL (ι j))) → LeafPage O → ContentEqualsDatumContent Nm N ι → TiePrimes O N →
      LeafDepthGood Nm O

end GlobalTheory.GoodDepth
