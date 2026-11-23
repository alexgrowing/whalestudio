import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Development

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

abbrev UV (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × Fin Sh.r1

abbrev AV (Sh : Shape) : Type := Sh.ZV ⊕ UV Sh

def IntA {σ τ Kc : Type} [Field Kc] (Oc : Subring Kc) (F : MvPowerSeries σ (MvPolynomial τ Kc)) : Prop :=
  ∀ n m, MvPolynomial.coeff m (MvPowerSeries.coeff n F) ∈ Oc

def subV (Sh : Shape) (Kc : Type) [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) :
    Sh.ZV → MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)
  | ⟨v, (s, a, b)⟩ => MvPowerSeries.X (Sum.inl ⟨v, (s, a, b)⟩) +
      if s ∈ TT v then
        MvPowerSeries.C (MvPolynomial.X (⟨v, (s, 0, a)⟩ : Sh.FrV)) * MvPowerSeries.X (Sum.inr ⟨v, (s, b)⟩)
      else 0

def subF (Sh : Shape) {Kc : Type} [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) (f : MvPowerSeries Sh.ZV Kc) :
    MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  MvPowerSeries.subst (subV Sh Kc TT) f

def abelian₂ {Sh : Shape} {Kc : Type} [Field Kc] (Q : MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ)) (e : UV Sh →₀ ℕ)
    (F : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)) : MvPolynomial Sh.FrV Kc :=
  MvPolynomial.C (∏ t ∈ e.support, ((e t).factorial : Kc)) *
    ∑ n ∈ Q.support, MvPolynomial.C (∏ x ∈ n.support, ((n x).factorial : Kc)) *
      MvPowerSeries.coeff (Finsupp.sumElim n e) F * MvPolynomial.map (Int.castRingHom Kc) (MvPolynomial.coeff n Q)

def QP (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) :
    MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ) :=
  ∏ v : Fin Sh.nV, ∏ s : Fin (Sh.n' v),
    ∏ c ∈ (range (nu v s 1).toNat).filter (fun c : ℕ => ¬ (s ∈ TT v ∧ nu v s 2 ≤ (c : ℤ))), Sh.colFac rb nu I v s c

def eV (Sh : Shape) (nu : Sh.Wt) (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) : UV Sh →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun t =>
    if t.2.1 ∈ TT t.1 then
      ((range (nu t.1 t.2.1 1).toNat).filter (fun c : ℕ => nu t.1 t.2.1 2 ≤ (c : ℤ) ∧ I t.1 t.2.1 c 0 = t.2.2)).card
    else 0

abbrev ETI (Sh : Shape) : Type := Σ v : Fin Sh.nV, Fin (Sh.n' v) × ℕ × ℕ × Fin 4

def zt (p : ℕ) (Sh : Shape) (Kc : Type) [Field Kc] (v : Fin Sh.nV) (sg : Fin (Sh.n' v)) (k : ℕ)
    (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  MvPowerSeries.X (Sum.inl ⟨v, (sg, a, b)⟩) ^ (p ^ k)

def ut (p : ℕ) (Sh : Shape) (Kc : Type) [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV)
    (sg : Fin (Sh.n' v)) (k : ℕ) (a : Fin Sh.r0) (b : Fin Sh.r1) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  if sg ∈ TT v then
    MvPowerSeries.C (MvPolynomial.X (⟨v, (sg, 0, a)⟩ : Sh.FrV) ^ (p ^ k)) * MvPowerSeries.X (Sum.inr ⟨v, (sg, b)⟩) ^ (p ^ k)
  else 0

def ET (p : ℕ) (Sh : Shape) {Kc : Type} [Field Kc] (TT : ∀ v, Finset (Fin (Sh.n' v)))
    (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc) : ETI Sh → MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)
  | ⟨v, (s, l, l', t)⟩ =>
    MvPowerSeries.C (MvPolynomial.C ((-1) ^ (l + l') * u v s)) *
      ∑ a : Fin Sh.r0, ∑ b : Fin Sh.r1,
        (if t.val = 0 then
          ut p Sh Kc TT v (FormalGroupSystem.posSub s (2 * l)) (2 * l + 1) a b * ut p Sh Kc TT v (FormalGroupSystem.posSub (posAdd s 1) (2 * l')) (2 * l') a b
        else if t.val = 1 then
          ut p Sh Kc TT v (FormalGroupSystem.posSub s (2 * l)) (2 * l + 1) a b * zt p Sh Kc v (FormalGroupSystem.posSub (posAdd s 1) (2 * l')) (2 * l') a b
        else if t.val = 2 then
          zt p Sh Kc v (FormalGroupSystem.posSub s (2 * l)) (2 * l + 1) a b * ut p Sh Kc TT v (FormalGroupSystem.posSub (posAdd s 1) (2 * l')) (2 * l') a b
        else
          zt p Sh Kc v (FormalGroupSystem.posSub s (2 * l)) (2 * l + 1) a b * zt p Sh Kc v (FormalGroupSystem.posSub (posAdd s 1) (2 * l')) (2 * l') a b)

def ETset (Sh : Shape) (v : Fin Sh.nV) (D : ℕ) : Finset (ETI Sh) :=
  ((univ : Finset (Fin (Sh.n' v))) ×ˢ (range (D + 1) ×ˢ (range (D + 1) ×ˢ (univ : Finset (Fin 4))))).map
    ⟨Sigma.mk v, sigma_mk_injective⟩

def GenT {σ τ ι Kc : Type} [Field Kc] (p : ℕ) (Oc : Subring Kc) (T : ι → MvPowerSeries σ (MvPolynomial τ Kc)) :
    Set (MvPowerSeries σ (MvPolynomial τ Kc)) :=
  {F | ∃ (m : ι →₀ ℕ) (U : MvPowerSeries σ (MvPolynomial τ Kc)), IntA Oc U ∧
    F = MvPowerSeries.C (MvPolynomial.C ((p : Kc) ^ m.degree)⁻¹) * (m.prod fun t k => T t ^ k) * U}

def S1 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (f : MvPowerSeries Sh.ZV Kc),
      applyDs vp (Sh.PI rb nu I) f =
        MvPolynomial.C ((vp ^ degP Sh rb nu)⁻¹) * abelian₂ (QP Sh rb nu TT I) (eV Sh nu TT I) (subF Sh TT f)

def S2 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV) (D : ℕ),
      ∃ Y : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc), IntA Oc Y ∧
        ∀ n : AV Sh →₀ ℕ, n.degree ≤ D →
          MvPowerSeries.coeff n (subF Sh TT (Sh.hhV p v (u v))) =
            ∑ t ∈ ETset Sh v D, MvPowerSeries.coeff n (ET p Sh TT u t) +
              (p : MvPolynomial Sh.FrV Kc) * MvPowerSeries.coeff n Y

def S3 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (σ τ ι : Type) (nV : ℕ), ValR p Oc →
    ∀ (E : Fin nV → Finset ι) (T : ι → MvPowerSeries σ (MvPolynomial τ Kc))
      (h Y : Fin nV → MvPowerSeries σ (MvPolynomial τ Kc)) (G : MvPowerSeries σ (MvPolynomial τ Kc))
      (i : Fin nV → ℕ) (D : ℕ),
      (∀ v, IntA Oc (Y v)) → IntA Oc G →
      (∀ v (n : σ →₀ ℕ), n.degree ≤ D → MvPowerSeries.coeff n (h v) =
        ∑ t ∈ E v, MvPowerSeries.coeff n (T t) + (p : MvPolynomial τ Kc) * MvPowerSeries.coeff n (Y v)) →
      ∃ F ∈ AddSubgroup.closure (GenT p Oc T), ∀ n : σ →₀ ℕ, n.degree ≤ D →
        MvPowerSeries.coeff n
          (MvPowerSeries.C (MvPolynomial.C (∏ v, ((p : Kc) ^ i v)⁻¹)) * (∏ v, h v ^ i v) * G) =
        MvPowerSeries.coeff n F

def S4 : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (rb : ℕ) (nu : Sh.Wt) (vp : Kc),
    HidaSetting p Oc Sh rb nu vp → ∀ (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc), (∀ v s, u v s ∈ Oc) →
    ∀ (TT : ∀ v, Finset (Fin (Sh.n' v))) (I : Sh.ColCh) (F : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)),
      F ∈ GenT p Oc (ET p Sh TT u) →
      MvPolynomial.C ((vp ^ degP Sh rb nu)⁻¹) * abelian₂ (QP Sh rb nu TT I) (eV Sh nu TT I) F ∈
        AddSubgroup.closure (Gen p Oc vp Sh rb nu TT)

def SSub : Prop :=
  ∀ (p : ℕ) (Kc : Type) [Field Kc] (Sh : Shape) (TT : ∀ v, Finset (Fin (Sh.n' v)))
    (u : ∀ v : Fin Sh.nV, Fin (Sh.n' v) → Kc) (i : Fin Sh.nV → ℕ) (g : MvPowerSeries Sh.ZV Kc),
    subF Sh TT (term p Sh u i g) =
      MvPowerSeries.C (MvPolynomial.C (∏ v, ((p : Kc) ^ i v)⁻¹)) *
        (∏ v, subF Sh TT (Sh.hhV p v (u v)) ^ i v) * subF Sh TT g

def SInt : Prop :=
  ∀ (Kc : Type) [Field Kc] (Oc : Subring Kc) (Sh : Shape) (TT : ∀ v, Finset (Fin (Sh.n' v)))
    (g : MvPowerSeries Sh.ZV Kc), IntSer Oc g → IntA Oc (subF Sh TT g)

section abelian₂

variable {Sh : Shape} {Kc : Type} [Field Kc] (Q : MvPolynomial Sh.ZV (MvPolynomial Sh.FrV ℤ)) (e : UV Sh →₀ ℕ)

end abelian₂

end PI.UnitaryGroupMassFormula.PadicGainBound
