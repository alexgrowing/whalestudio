import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.SatGramRep

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rel

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem grel_equiv (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) : Equivalence (GRel X u u' F0 F0' Λ Λ') where
  refl _ := ⟨1, nlam_one _ _, 1, nlam_one _ _, by simp⟩
  symm := by
    rintro p q ⟨n, hn, n', hn', h⟩
    exact ⟨n⁻¹, nlam_inv hn, n'⁻¹, nlam_inv hn', by rw [h]; group⟩
  trans := by
    rintro p q r ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    exact ⟨m * n, nlam_mul hm hn, n' * m', nlam_mul hn' hm', by rw [h', h]; group⟩

theorem grel_of_mk_eq {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u' F0 F0' Λ Λ'}
    (h : Quot.mk (GRel X u u' F0 F0' Λ Λ') p = Quot.mk _ q) : GRel X u u' F0 F0' Λ Λ' p q :=
  @Quotient.exact _ ⟨GRel X u u' F0 F0' Λ Λ', grel_equiv Λ Λ'⟩ p q h

theorem grel_rep (t : GTerm X u u' F0 F0' what₂ rows') (p : GCar X u u' F0 F0' t.lam t.lam')
    (hp : t.cls = Quot.mk _ p) : GRel X u u' F0 F0' t.lam t.lam' t.rep p :=
  grel_of_mk_eq ((Quot.out_eq t.cls).trans hp)

theorem mem_fam_iff (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    {t s : GTerm X u u' F0 F0' what₂ rows'} (h : t.toTerm = s.toTerm)
    (S : Set (GTerm X u u' F0 F0' what₂ rows'))
    (hS : S ∈ ({(tOf F0 F0' TR cs cs' FdN FdN').genSet, (tOf F0 F0' TR cs cs' FdN FdN').ngSet,
      (tOf F0 F0' TR cs cs' FdN FdN').degSet} : Set (Set (GTerm X u u' F0 F0' what₂ rows')))) :
    t ∈ S ↔ s ∈ S := by
  have hG : Gt t = Gt s := by
    unfold Gt GTerm.G
    rw [h]
  have hg : t.generic ↔ s.generic := by
    unfold GTerm.generic
    rw [h]
  have hi : t.isId ↔ s.isId := by
    unfold GTerm.isId
    rw [h]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS
  rcases hS with rfl | rfl | rfl <;>
    simp only [Formalism.FourierDecayAlt.PB.Terms.genSet, Formalism.FourierDecayAlt.PB.Terms.ngSet, Formalism.FourierDecayAlt.PB.Terms.degSet,
      Set.mem_setOf_eq, tOf, hG, hg, hi]

end Rel

section Steps

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

def IotaRep : Prop :=
  ∀ (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ what₂ → Λ' ∈ rows' → ∀ p q : GCar X u u' F0 F0' Λ Λ',
    GRel X u u' F0 F0' Λ Λ' p q →
      levi TR (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) q.1.1) =
        levi TR (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) p.1.1)

def AmpRepN : Prop :=
  ∀ (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ what₂ → Λ' ∈ rows' → ∀ p q : GCar X u u' F0 F0' Λ Λ',
    GRel X u u' F0 F0' Λ Λ' p q →
    ∀ Ωp Ωq : Set X.B.I.Ginf,
      Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' Λ Λ' p.1.2) Ωp →
      Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' Λ Λ' q.1.2) Ωq →
      OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 →
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       chiN X (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) p.1.1) •
          OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωp (X.Wu u) (X.Wu u') p.1.1.1 =
        chiN X (kOf X u u' (cs.h (cs.base Λ) : X.B.I.Gf) (cs'.h (cs'.base Λ') : X.B.I.Gf) q.1.1) •
          OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ωq (X.Wu u) (X.Wu u') q.1.1.1)

variable {F0 F0' TR cs cs'}

theorem iotaOf_of_mk (hI : IotaRep F0 F0' TR cs cs') (t : GTerm X u u' F0 F0' what₂ rows')
    (p : GCar X u u' F0 F0' t.lam t.lam') (hp : t.cls = Quot.mk _ p) :
    iotaOf TR cs cs' t =
      levi TR (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) p.1.1) :=
  (hI t.lam t.lam' t.mem t.mem' t.rep p (grel_rep t p hp)).symm

theorem ampN_of_mk (FdN FdN' : Set X.B.I.Ginf) (hA : AmpRepN F0 F0' cs cs')
    (hF : FundExists X u u' F0 F0' what₂ rows') (hO : OOIntAll X u u' F0 F0' what₂ rows')
    (t : GTerm X u u' F0 F0' what₂ rows') (p : GCar X u u' F0 F0' t.lam t.lam') (hp : t.cls = Quot.mk _ p)
    (Ω : Set X.B.I.Ginf) (hΩ : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X F0 F0' t.lam t.lam' p.1.2) Ω) :
    ampN cs cs' FdN FdN' t =
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
        (chiN X (kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) p.1.1) •
          OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') p.1.1.1)) := by
  have hFt : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t) (FundOf t) := by
    have h := hF t
    unfold FundOf
    rw [dif_pos h]
    exact h.choose_spec
  have key := hA t.lam t.lam' t.mem t.mem' t.rep p (grel_rep t p hp) (FundOf t) Ω hFt hΩ (hO t)
  have hc := congrArg (fun z => ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) • z) key
  exact hc

end Steps

section Closed

open Formalism.L2.SG.Full

def IotaRepC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    IotaRep (what₂ := Y.what₂ u) (rows' := Y.what₂ u') (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u')

def AmpRepNC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    AmpRepN (what₂ := Y.what₂ u) (rows' := Y.what₂ u') (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u')

end Closed

end Formalism.L2.SG.Pf.SatGramRep
