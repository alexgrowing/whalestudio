import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MonomialWeightedHomogeneous

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

attribute [local instance] ColSys.fin

def l2P (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) : ℕ :=
  (X.seg C0 CE1 CE2 j).P X.p (uTop (X.seg C0 CE1 CE2 j) i)

def l2x (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) : X.TT :=
  topOdd X j (uTop (X.seg C0 CE1 CE2 j) i)

section Ctx

variable {C0 Cde CE1 CE2 mu E : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O] {β : GlobalTheory X}

def l2sR (O : Type) [CommRing O] [IsDomain O] (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ)
    (j0 : Fin (numSeg X.TT)) : RHH O X :=
  (∏ j, hTop O X (topEnd X j) ^ L.jp j) * monomial (rig L a0 j0) 1

theorem lifted_block_generator (j : Fin (numSeg X.TT)) (i : Fin (BDk C0 CE1 CE2 mu X β j).T.t) :
    ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i) =
      EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i) := ioD_Ehat β j i

theorem rigid_factor_product (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT)) :
    (∏ j, ioD O C0 CE1 CE2 mu X β j ((BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m)) ^ L.jp j) *
      monomial (rig L a0 j0) 1 = l2sR O L a0 j0 := by
  unfold l2sR
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [ioD_Eplus]

theorem rigid_product_weighted_homog (L : LvDat C0 CE1 CE2 mu X β) (a0 : Fin (numSeg X.TT) → ℕ) (j0 : Fin (numSeg X.TT))
    (ω : VarH X → ℕ) (e : X.TT → ℕ) (he : ∀ x, IsWeightedHomogeneous ω (hTop O X x) (e x)) :
    IsWeightedHomogeneous ω (l2sR O L a0 j0) ((∑ j, L.jp j * e (topEnd X j)) + Finsupp.weight ω (rig L a0 j0)) := by
  unfold l2sR
  refine IsWeightedHomogeneous.mul ?_ (isWeightedHomogeneous_monomial _ _ _ rfl)
  have h := IsWeightedHomogeneous.prod Finset.univ (fun j => hTop O X (topEnd X j) ^ L.jp j)
    (fun j => L.jp j • e (topEnd X j)) (fun j _ => (he _).pow _)
  simpa [smul_eq_mul] using h

theorem word_head_formula (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    L.head O j (L.lv j) G = (∏ i, EhatT O X (l2x C0 CE1 CE2 mu X β j i) (l2P C0 CE1 CE2 mu X β j i) ^ L.lv j i) *
      hTop O X (topEnd X j) ^ L.jp j * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) G) := by
  unfold LvDat.head
  rw [map_mul, map_mul, map_prod, map_pow, ioD_Eplus]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by rw [map_pow, lifted_block_generator]

theorem sym_family_word_eq_head_mul_monomial (L : LvDat C0 CE1 CE2 mu X β) (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
    (Std : MonH X) (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) =
      (∏ j, L.head O j (L.lv j) (G j)) * monomial Std 1 := by
  unfold symFam
  rw [hStd, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => L.ioBlock_word O j (G j)

theorem sym_family_word_ne_zero (hp : 0 < X.p) (L : LvDat C0 CE1 CE2 mu X β)
    (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (hG0 : ∀ j, G j ≠ 0)
    (Std : MonH X) (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) ≠ 0 := by
  rw [sym_family_word_eq_head_mul_monomial L G Std hStd]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => ?_) ?_
  · rw [word_head_formula]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _
      (top_letter_power_ne_zero _ _ (pow_pos hp _).ne')) (pow_ne_zero _ (top_letter_ne_zero _))) (ioD_ne_zero hp β j ?_)
    intro h
    exact hG0 j (rename_injective _ (chain_embedding_injective _ _ _) (by rw [h, map_zero]))
  · intro h
    exact one_ne_zero (monomial_eq_zero.1 h)

theorem balanced_word_homogeneous (L : LvDat C0 CE1 CE2 mu X β) (G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
    (hGpol : ∀ j, G j ∈ Pol (KK O) X.m (L.LL j).deg) :
    BalHom O C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  intro j ω' ωL hb
  refine gen_wh O X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mu (β j) ω' ωL hb.1 hb.2.1 hb.2.2
    (L.lv j) (L.jp j) (L.ok j) (G j) (hGpol j) _ ?_
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun c => (MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) :
      MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O)) ^ L.γ j c) _
    (fun c _ => (isWeightedHomogeneous_X (KK O) ω' _).pow (L.γ j c))
  refine wh_congr h ?_
  rw [← L.hγ j, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul]
  congr 1
  exact hb.1 _ _

end Ctx

end Formalism.MainNotions.ColumnSystems.Pf
