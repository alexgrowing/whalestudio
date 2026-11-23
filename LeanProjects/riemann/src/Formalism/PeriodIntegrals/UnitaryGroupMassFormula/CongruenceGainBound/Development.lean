import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StatementFormalValuationAllFields

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

def applyDs {σ τ Kc : Type} [Field Kc] (vp : Kc) (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    MvPolynomial τ Kc :=
  ∑ n ∈ P.support, ((∏ x ∈ n.support, ((n x).factorial : Kc)) * (vp ^ n.degree)⁻¹ * MvPowerSeries.coeff n f) •
    MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n P)

def term (p : ℕ) {Kc : Type} [Field Kc] (Sh : Shape) (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc) (i : Fin Sh.nV → ℕ)
    (g : MvPowerSeries Sh.ZV Kc) : MvPowerSeries Sh.ZV Kc :=
  MvPowerSeries.C (∏ v, ((p : Kc) ^ i v)⁻¹) * (∏ v, Sh.hhV p v (u v) ^ i v) * g

def degP (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) : ℕ := ∑ v, ∑ s, (sz rb (nu v) s).toNat

structure Counts (Sh : Shape) where
  ec : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r1 → ℕ
  ih : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → ℕ → ℕ
  i0 : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin (Sh.n' v) → ℕ
  i2 : Fin Sh.nV → ℕ
  be : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r0 → Fin Sh.r1 → ℕ
  N : ℕ

def Counts.hits {Sh : Shape} (D : Counts Sh) (v : Fin Sh.nV) (s' : Fin (Sh.n' v)) : ℕ :=
  ∑ s, ∑ e ∈ range D.N, if posAdd s e = s' then D.ih v s e else 0

def Counts.mtot {Sh : Shape} (D : Counts Sh) : ℕ :=
  ∑ v, ((∑ s, ∑ s', D.i0 v s s') + D.i2 v + ∑ s, ∑ e ∈ range D.N, D.ih v s e)

structure Counts.Ok (p : ℕ) {Sh : Shape} (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (D : Counts Sh) : Prop where
  ec_sum : ∀ v s, ((∑ b, D.ec v s b : ℕ) : ℤ) = al (TT v) (nu v) s
  ih_supp : ∀ v s e, D.ih v s e ≠ 0 → s ∈ TT v ∧ Odd e ∧ e < D.N
  h1 : ∀ v s e, (D.ih v s e : ℤ) ≤ cap (TT v) (nu v) (posAdd s e)
  h2 : ∀ v s e, ((p ^ e * D.ih v s e : ℕ) : ℤ) ≤ al (TT v) (nu v) s
  zero_index_support : ∀ v s s', D.i0 v s s' ≠ 0 → s ∈ TT v ∧ s' ∈ TT v ∧ OtherPar s s'
  pair : ∀ v s s', s ∈ TT v → s' ∈ TT v → OtherPar s s' →
    ((p ^ dLev s s' * (D.i0 v s s' + D.ih v s (dLev s s')) : ℕ) : ℤ) ≤ al (TT v) (nu v) s
  b2 : ∀ v, ((p * D.i2 v : ℕ) : ℤ) ≤ ∑ s, low rb (TT v) (nu v) s
  be_sum : ∀ v s, ((∑ a, ∑ b, D.be v s a b : ℕ) : ℤ) = low rb (TT v) (nu v) s - D.hits v s
  be_le : ∀ v s a b, (D.be v s a b : ℤ) ≤ low rb (TT v) (nu v) s

def Counts.coef (p : ℕ) {Kc : Type} [Field Kc] (vp : Kc) {Sh : Shape} (rb : ℕ) (nu : Sh.Wt) (D : Counts Sh) : Kc :=
  (vp ^ degP Sh rb nu)⁻¹ * ((p : Kc) ^ D.mtot)⁻¹ *
    ((∏ v, ∏ s, ∏ b, ((D.ec v s b).factorial : Kc)) * (∏ v, ∏ s, ∏ e ∈ range D.N, ((D.ih v s e).factorial : Kc)) *
      (∏ v, ∏ s, ∏ a, ∏ b, ((D.be v s a b).factorial : Kc)))

def Gen (p : ℕ) {Kc : Type} [Field Kc] (Oc : Subring Kc) (vp : Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt)
    (TT : ∀ v, Finset (Fin (Sh.n' v))) : Set (MvPolynomial Sh.FrV Kc) :=
  {y | ∃ D : Counts Sh, D.Ok p rb nu TT ∧ ∃ r : MvPolynomial Sh.FrV Kc, (∀ n, MvPolynomial.coeff n r ∈ Oc) ∧
    y = MvPolynomial.C (D.coef p vp rb nu) * r}

def SLin : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc)
    (Th : MvPowerSeries Sh.ZV Kc) (I : Sh.ColCh) (A : AddSubgroup (MvPolynomial Sh.FrV Kc)),
    HidaSetting p Oc Sh rb nu vp → InMM p Oc Sh vp Th →
    (∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) → ∀ (i : Fin Sh.nV → ℕ) (g : MvPowerSeries Sh.ZV Kc),
      IntSer Oc g → applyDs vp (Sh.PI rb nu I) (term p Sh u i g) ∈ A) →
    FormalGroupSystem.applyD (Sh.PI rb nu I) Th ∈ A

def SStruct : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp →
    ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (i : Fin Sh.nV → ℕ) (g : MvPowerSeries Sh.ZV Kc), IntSer Oc g →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh),
      applyDs vp (Sh.PI rb nu I) (term p Sh u i g) ∈ AddSubgroup.closure (Gen p Oc vp Sh rb nu TT)

def SVal : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))),
    ∀ y ∈ Gen p Oc vp Sh rb nu TT, gaussGe p Oc y (formalValuationLowerBound p Sh rb nu TT)

def S0 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc), p.Prime → ValR p Oc →
    ∀ (m : ℕ) (al : Fin m → ℕ) (M : ℤ), (∀ k, (al k : ℤ) ≤ M) →
      geV p Oc ((∏ k, ((al k).factorial : Kc))) ((∑ k, (al k : ℝ)) / ((p : ℝ) - 1) - (m : ℝ) * (lg p M : ℝ))

def S5 : Prop :=
  ∀ (p n' r0 r1 rb : ℕ), p.Prime → 5 ≤ p → Even n' → 2 ≤ n' → r0 ≤ rb →
  ∀ (TT : Finset (Fin n')) (nu : Fin n' → ℕ → ℤ), IsPart r0 nu →
  ∀ (ih : Fin n' → ℕ → ℕ) (i0 : Fin n' → Fin n' → ℕ) (i2 N : ℕ),
    (∀ s e, ih s e ≠ 0 → s ∈ TT ∧ Odd e) →
    (∀ s e, (ih s e : ℤ) ≤ cap TT nu (posAdd s e)) →
    (∀ s e, ((p ^ e * ih s e : ℕ) : ℤ) ≤ al TT nu s) →
    (∀ s s', i0 s s' ≠ 0 → s ∈ TT ∧ s' ∈ TT ∧ OtherPar s s') →
    (∀ s s', s ∈ TT → s' ∈ TT → OtherPar s s' →
      ((p ^ dLev s s' * (i0 s s' + ih s (dLev s s')) : ℕ) : ℤ) ≤ al TT nu s) →
    (((p * i2 : ℕ) : ℤ) ≤ ∑ s, low rb TT nu s) →
    gsum p TT nu + Fv p rb TT nu - de p r0 r1 rb TT nu ≤
      gam p * ∑ s ∈ TT, (al TT nu s : ℝ) + gam p * ∑ s, (low rb TT nu s : ℝ)
        - ∑ s, ∑ s', (i0 s s' : ℝ) - (i2 : ℝ) - ∑ s, ∑ e ∈ range N, (ih s e : ℝ)
        - ∑ s, ((r1 : ℝ) * (lg p (al TT nu s) : ℝ) + (r0 : ℝ) * (r1 : ℝ) * (lg p (low rb TT nu s) : ℝ))
        - ∑ s ∈ TT, ∑ e ∈ range N, (lg p (ih s e) : ℝ)

theorem gain_bound_of_parts (hL : SLin) (hS : SStruct) (hV : SVal) : StatementFormalValuationAllFields := by
  intro p Kc _ Oc Sh rb nu vp Th hSet hMM TT I
  have hmem := hL p Kc Oc Sh rb nu vp Th I (AddSubgroup.closure (Gen p Oc vp Sh rb nu TT)) hSet hMM
    (fun u hu i g hg => hS p Kc Oc Sh rb nu vp hSet u hu i g hg TT I)
  have key : ∀ y ∈ AddSubgroup.closure (Gen p Oc vp Sh rb nu TT), gaussGe p Oc y (formalValuationLowerBound p Sh rb nu TT) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy => exact hV p Kc Oc Sh rb nu vp hSet TT y hy
    | zero => intro n; simpa using geV_zero p Oc _
    | add x y _ _ hx hy => intro n; simpa using geV_add p Oc hSet.valR (hx n) (hy n)
    | neg x _ hx => intro n; simpa using geV_neg p Oc (hx n)
  exact key _ hmem

end PI.UnitaryGroupMassFormula.PadicGainBound
