import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MonomialSumEqProdTensor

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mu : ℝ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 mu X β} {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

abbrev PreSys.κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : Type :=
  (Σ j, P.ιC j) ⊕ ((Σ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t) ⊕ P.ιM)

def PreSys.mult (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun x => L.lv x.1 x.2) P.multM)

def PreSys.f (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.fC x.1 x.2) (Sum.elim (fun x => P.fH x.1 x.2) P.fM)

def PreSys.sg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.sgC x.1 x.2) (Sum.elim (fun x => P.sgH x.1 x.2) (fun a => monomial (P.aM a) 1))

def PreSys.od (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun x => P.oC x.1 x.2) (Sum.elim (fun x => P.oH x.1 x.2) P.oM)

def PreSys.dg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → X.TT × Bool → ℕ :=
  Sum.elim (fun x => P.dgC x.1 x.2) (Sum.elim (fun x => P.dgH x.1 x.2) P.dgM)

theorem PreSys.prod_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → RHH O X) :
    ∏ a, F a = (∏ j, ∏ a, F (Sum.inl ⟨j, a⟩)) * ((∏ j, ∏ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) * ∏ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_sigma]

theorem PreSys.sum_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → ℕ) :
    ∑ a, F a = (∑ j, ∑ a, F (Sum.inl ⟨j, a⟩)) + ((∑ j, ∑ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) + ∑ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]

theorem sum_mul_le {κ : Type} [Fintype κ] (u d : κ → ℕ) (Q : ℕ) (h : ∀ a, d a ≤ Q) : ∑ a, u a * d a ≤ (∑ a, u a) * Q := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (h a)

theorem PreSys.sgNd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) : HomW (ndHom X) (P.od a) (P.sg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.homC j i
  · exact P.homH j i
  · show HomW (ndHom X) (P.oM a) (monomial (P.aM a) (1 : KK O))
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    subst hm'
    exact P.homM a

theorem PreSys.sgMd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) :
    P.sg a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.polC j i
  · exact P.polH j i
  · show monomial (P.aM a) (1 : KK O) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dgM a)
    rw [Pol, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm))
    subst hm'
    exact P.polM a

theorem PreSys.dgQ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (l : X.TT × Bool) : P.dg a l ≤ X.p ^ X.G' := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCQ j i l
  · exact P.dgHQ j i l
  · exact P.dgMQ a l

theorem PreSys.dgY (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (j' : Fin (numSeg X.TT)) :
    P.dg a (topEnd X j', false) = 0 := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCY j i j'
  · exact P.dgHY j i j'
  · exact P.dgMY a j'

theorem PreSys.ordκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    P.oR + ∑ a, P.mult a * P.od a = ordFam C0 CE1 CE2 X β := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.od, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.ordEq

theorem PreSys.degκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (l : X.TT × Bool) :
    P.dR l + ∑ a, P.mult a * P.dg a l = hhDegs X.TT X.aT X.bT l := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.dg, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.degEq l

theorem PreSys.fprod (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    ∏ a, P.f a ^ P.mult a = (∏ j, ∏ a, P.fC j a) * ((∏ j, ∏ i, P.fH j i ^ L.lv j i) * ∏ a, P.fM a ^ P.multM a) := by
  rw [P.prod_κ]
  simp only [PreSys.f, PreSys.mult, Sum.elim_inl, Sum.elim_inr, pow_one]

theorem PreSys.symκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    P.sgR * ∏ a, P.sg a ^ P.mult a = symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  have hsym : symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) =
      (∏ j, L.head O j (L.lv j) (G j)) * monomial Std 1 := by
    rw [hStd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => L.ioBlock_word O j (G j))
  have h1 := P.ident (fun _ _ => 1) L.lv P.multM 0
  have h2 : P.R + ((∑ j, ∑ a, (1 : ℕ) • P.pl j a) + ∑ a, P.multM a • P.aM a) + 0 = Std := by
    refine Eq.trans ?_ P.stdEq.symm
    simp
  have h3 : ∀ j, ∏ a, P.Kc j a ^ (1 : ℕ) = G j := fun j => by simp [P.Kprod j]
  rw [h2] at h1
  simp only [h3] at h1
  rw [hsym, ← h1, P.prod_κ]
  simp [PreSys.mult, PreSys.sg]

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
