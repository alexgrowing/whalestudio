import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SymFamilyWordEqHeadMulMonomial

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [local instance] ColSys.fin

section Ctx

variable {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {β : GlobalTheory X} {L : LvDat C0 CE1 CE2 mu X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)}

def l2sC (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) (a : (Cs j).ι) : RHH O X :=
  monomial ((Cs j).pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) ((Cs j).Kc a))

theorem column_word_mem_polynomials_of_degree (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) :
    G j ∈ Pol (KK O) X.m (L.LL j).deg := by
  have h := Formalism.L2.G.Model.Pol_prod (R := KK O) (k := X.m) Finset.univ (Cs j).dK (Cs j).Kc
    (fun a _ => (Cs j).KPol a)
  rw [(Cs j).Kprod] at h
  have hd : ∑ a, (Cs j).dK a = (L.LL j).deg := funext fun i => by rw [Finset.sum_apply, (Cs j).dKsum i]
  rwa [hd] at h

theorem column_product_eq_monomial_mul_ioD (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j : Fin (numSeg X.TT)) :
    ∏ a, l2sC Cs j a = monomial (∑ a, (Cs j).pl a) 1 *
      ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (G j)) := by
  unfold l2sC
  rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod, (Cs j).Kprod, MvPolynomial.monomial_sum_one]

theorem sym_family_eq_sigma_product (Cs : ∀ j, ColSys C0 CE1 CE2 X O w mu β L j (G j)) (j0 : Fin (numSeg X.TT)) (Std : MonH X)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
    (stdEq : Std = rig L (fun j => (Cs j).a0) j0 +
      ((∑ j, ∑ a, (Cs j).pl a) + ∑ a, multMk X β a • aMk C0 CE1 CE2 X a)) :
    l2sR O L (fun j => (Cs j).a0) j0 * ((∏ j, ∏ a, l2sC Cs j a) *
      ((∏ j, ∏ i, EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
      ∏ a, (monomial (aMk C0 CE1 CE2 X a) (1 : KK O) : RHH O X) ^ multMk X β a)) =
      symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  have hMprod : ∏ a, (monomial (aMk C0 CE1 CE2 X a) (1 : KK O) : RHH O X) ^ multMk X β a =
      monomial (∑ a, multMk X β a • aMk C0 CE1 CE2 X a) 1 := (mono_sum _ _ _).symm
  have hmono : (monomial Std (1 : KK O) : RHH O X) = monomial (rig L (fun j => (Cs j).a0) j0) 1 *
      ((∏ j, monomial (∑ a, (Cs j).pl a) 1) * monomial (∑ a, multMk X β a • aMk C0 CE1 CE2 X a) 1) := by
    rw [← monomial_sum_one, monomial_mul, monomial_mul, one_mul, one_mul, ← stdEq]
  rw [sym_family_word_eq_head_mul_monomial L G Std hStd, hmono, hMprod]
  simp only [word_head_formula, column_product_eq_monomial_mul_ioD, Finset.prod_mul_distrib]
  unfold l2sR
  ring

end Ctx

end Formalism.MainNotions.ColumnSystems.Pf
