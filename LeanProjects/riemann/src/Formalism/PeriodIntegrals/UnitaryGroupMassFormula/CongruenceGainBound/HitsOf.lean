import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

variable {Sh : Shape}

abbrev Pos (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v)

def ETI.s1 (t : ETI Sh) : Fin (Sh.n' t.1) := FormalGroupSystem.posSub t.2.1 (2 * t.2.2.1)

def ETI.s2 (t : ETI Sh) : Fin (Sh.n' t.1) := FormalGroupSystem.posSub (posAdd t.2.1 1) (2 * t.2.2.2.1)

def ETI.j (t : ETI Sh) : ℕ := 2 * t.2.2.1 + 1

def ETI.j' (t : ETI Sh) : ℕ := 2 * t.2.2.2.1

def ETI.ty (t : ETI Sh) : ℕ := t.2.2.2.2.val

def ETI.IsB (t : ETI Sh) : Prop := t.ty = 1 ∧ t.2.2.2.1 = 0

instance (t : ETI Sh) : Decidable t.IsB := inferInstanceAs (Decidable (_ ∧ _))

def ETI.charge (t : ETI Sh) : Pos Sh × Pos Sh :=
  if t.j' < t.j then (⟨t.1, t.s1⟩, ⟨t.1, t.s2⟩) else (⟨t.1, t.s2⟩, ⟨t.1, t.s1⟩)

def ETI.udeg (p : ℕ) (t : ETI Sh) (q : Pos Sh) : ℕ :=
  (if (t.ty = 0 ∨ t.ty = 1) ∧ (⟨t.1, t.s1⟩ : Pos Sh) = q then p ^ t.j else 0) +
    (if (t.ty = 0 ∨ t.ty = 2) ∧ (⟨t.1, t.s2⟩ : Pos Sh) = q then p ^ t.j' else 0)

def ETI.zdeg (p : ℕ) (t : ETI Sh) (v : Fin Sh.nV) : ℕ :=
  if t.1 = v then
    (if t.ty = 1 ∨ t.ty = 3 then p ^ t.j' else 0) + (if t.ty = 2 ∨ t.ty = 3 then p ^ t.j else 0)
  else 0

def ihOf (m : ETI Sh →₀ ℕ) (v : Fin Sh.nV) (s : Fin (Sh.n' v)) (e : ℕ) : ℕ :=
  ∑ t ∈ m.support, if t.IsB ∧ (⟨t.1, t.s1⟩ : Pos Sh) = ⟨v, s⟩ ∧ t.j = e then m t else 0

def i0Of (m : ETI Sh →₀ ℕ) (v : Fin Sh.nV) (s s' : Fin (Sh.n' v)) : ℕ :=
  ∑ t ∈ m.support, if t.ty = 0 ∧ t.charge = ((⟨v, s⟩ : Pos Sh), (⟨v, s'⟩ : Pos Sh)) then m t else 0

def i2Of (m : ETI Sh →₀ ℕ) (v : Fin Sh.nV) : ℕ :=
  ∑ t ∈ m.support, if t.1 = v ∧ t.ty ≠ 0 ∧ ¬ t.IsB then m t else 0

def NOf (m : ETI Sh →₀ ℕ) : ℕ := ∑ t ∈ m.support, (t.j + 1)

def hitsOf (m : ETI Sh →₀ ℕ) (v : Fin Sh.nV) (s' : Fin (Sh.n' v)) : ℕ :=
  ∑ s, ∑ e ∈ range (NOf m), if posAdd s e = s' then ihOf m v s e else 0

def Mprod (p : ℕ) (Sh : Shape) {Kc : Type} [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v)))
    (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc) (m : ETI Sh →₀ ℕ) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  m.prod fun t k => ET p Sh TT u t ^ k

def SBud : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (m : ETI Sh →₀ ℕ)
      (U : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)), IntA Oc U →
      abelian₂ (QP Sh rb nu TT I) (eV Sh nu TT I) (Mprod p Sh TT u m * U) ≠ 0 →
      (∀ v s, ((∑ t ∈ m.support, m t * t.udeg p ⟨v, s⟩ : ℕ) : ℤ) ≤ al (TT v) (nu v) s) ∧
      (∀ v, ((∑ t ∈ m.support, m t * t.zdeg p v : ℕ) : ℤ) ≤ ∑ s, low rb (TT v) (nu v) s)

def SVan : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (m : ETI Sh →₀ ℕ)
      (U : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)), IntA Oc U →
      abelian₂ (QP Sh rb nu TT I) (eV Sh nu TT I) (Mprod p Sh TT u m * U) ≠ 0 →
      ∀ v s e, (ihOf m v s e : ℤ) ≤ cap (TT v) (nu v) (posAdd s e)

def HitGen (Sh : Shape) {Kc : Type} [Field Kc] (Oc : Subring Kc) (rb : ℕ) (nu : Sh.Wt)
    (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (m : ETI Sh →₀ ℕ) : Set (MvPolynomial Sh.FrV Kc) :=
  {y | ∃ (be : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Fin Sh.r0 → Fin Sh.r1 → ℕ) (r : MvPolynomial Sh.FrV Kc),
    (∀ n, MvPolynomial.coeff n r ∈ Oc) ∧
    (∀ v s, ((∑ a, ∑ b, be v s a b : ℕ) : ℤ) = low rb (TT v) (nu v) s - hitsOf m v s) ∧
    y = MvPolynomial.C ((∏ v, ∏ s, ∏ b, ((eV Sh nu TT I ⟨v, (s, b)⟩).factorial : Kc)) *
      (∏ v, ∏ s, ∏ e ∈ range (NOf m), ((ihOf m v s e).factorial : Kc)) *
      (∏ v, ∏ s, ∏ a, ∏ b, ((be v s a b).factorial : Kc))) * r}

def SHit : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (m : ETI Sh →₀ ℕ)
      (U : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)), IntA Oc U →
      abelian₂ (QP Sh rb nu TT I) (eV Sh nu TT I) (Mprod p Sh TT u m * U) ∈
        AddSubgroup.closure (HitGen Sh Oc rb nu TT I m)

end PI.UnitaryGroupMassFormula.PadicGainBound
