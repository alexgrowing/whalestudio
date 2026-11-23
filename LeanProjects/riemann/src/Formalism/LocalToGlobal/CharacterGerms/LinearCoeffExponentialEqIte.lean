import Formalism.LocalToGlobal.CharacterGerms.LinearCoeffSubstChainRule

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

variable (Y : FBChart C V O dd)

theorem mapAt_addAt {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hadd : comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    mapAt ε (addAt Y a b) = addAt Y (mapAt ε a) (mapAt ε b) := by
  have h := hadd
  rw [addOf_eq', addOf_eq', comp_eq_map_at, comp_eq_map_at, comp_eq_map_at] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [mapAt_subst hP ε (cc_addAt Y k0 k1), addAt_subst Y hP (cc_mapAt hε k0) (cc_mapAt hε k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (mapAt ε (pt C dd (0 : Fin 2)) i)) = mapAt ε a := by
    funext j
    rw [mapAt_subst hP ε k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (mapAt ε (pt C dd (1 : Fin 2)) i)) = mapAt ε b := by
    funext j
    rw [mapAt_subst hP ε k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

def PhiAt (ε : Pt C 1 dd) (a : Fin dd → MvPowerSeries τ C) (m : Fin dd) : MvPowerSeries τ C :=
  MvPowerSeries.subst (mapAt ε (exAt Y a)) (l Y m)

theorem exAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (i : Fin dd) :
    MvPowerSeries.subst A (exAt Y u i) = exAt Y (fun i => MvPowerSeries.subst A (u i)) i := subst_subst hu hA _

variable {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)

include hε in
theorem PhiAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (m : Fin dd) :
    MvPowerSeries.subst A (PhiAt Y ε u m) = PhiAt Y ε (fun i => MvPowerSeries.subst A (u i)) m := by
  unfold PhiAt
  rw [subst_subst (cc_mapAt hε (cc_exAt Y hu)) hA]
  congr 1
  funext k
  rw [mapAt_subst hA ε (cc_exAt Y hu)]
  congr 1
  funext i
  exact exAt_subst Y hA hu i

include hε in
theorem PhiAt_add (hadd : comp1 ε (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 ε (pt C (n := 2) dd 0)) (comp1 ε (pt C (n := 2) dd 1)))
    {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (m : Fin dd) :
    PhiAt Y ε (fun i => a i + b i) m = PhiAt Y ε a m + PhiAt Y ε b m := by
  unfold PhiAt
  rw [ex_add Y ha hb, mapAt_addAt Y hε hadd (cc_exAt Y ha) (cc_exAt Y hb),
    l_add_at Y (cc_mapAt hε (cc_exAt Y ha)) (cc_mapAt hε (cc_exAt Y hb))]

theorem linear_coeff_logarithm_eq_ite (m k : Fin dd) : lin1 (l Y m) k = if m = k then 1 else 0 := pderiv_l_zero Y m k

theorem linear_coeff_exponential_eq_ite (m j : Fin dd) : lin1 (e Y m) j = if m = j then 1 else 0 := by
  have h := congrArg (fun f => lin1 f j) (lgex Y m)
  beta_reduce at h
  rw [linear_coeff_subst_chain_rule (cc_e Y), linear_coeff_X_eq_ite] at h
  have h' : ∑ k, lin1 (e Y k) j * lin1 (l Y m) k = lin1 (e Y m) j := by
    simp only [linear_coeff_logarithm_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [h'] at h
  convert h

theorem exAt_X : exAt Y (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) = e Y := by
  funext i
  unfold exAt
  rw [MvPowerSeries.subst_self]
  rfl

include hε in
theorem linear_coeff_formal_law_at_X (m j : Fin dd) :
    lin1 (PhiAt Y ε (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C) m) j =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) := by
  unfold PhiAt
  rw [linear_coeff_subst_chain_rule (cc_mapAt hε (cc_exAt Y fun _ => cc_X _))]
  simp only [linear_coeff_logarithm_eq_ite, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [exAt_X]
  unfold mapAt
  rw [linear_coeff_subst_chain_rule (A := fun q : Fin 1 × Fin dd => e Y q.2) (fun q => cc_e Y q.2), Finset.sum_eq_single ((0 : Fin 1), j)]
  · rw [linear_coeff_exponential_eq_ite, if_pos rfl, one_mul, linear_coeff_eq_coeff_single]
  · intro q _ hq
    rw [linear_coeff_exponential_eq_ite, if_neg, zero_mul]
    intro h
    apply hq
    obtain ⟨q1, q2⟩ := q
    have : q1 = 0 := Subsingleton.elim _ _
    subst this
    exact Prod.ext rfl h
  · intro h; exact absurd (Finset.mem_univ _) h

end VP

theorem endoLog_holds {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : EndoLogSt Y := by
  intro ε hε hadd τ _ a ha i
  have cX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun _ => VP.cc_X _
  set φ : Fin dd → MvPowerSeries (Fin dd) C := VP.PhiAt Y ε MvPowerSeries.X with hφ
  have cφ : ∀ m, MvPowerSeries.constantCoeff (φ m) = 0 := fun m =>
    VP.cc_subst (VP.cc_mapAt hε (VP.cc_exAt Y cX)) (VP.cc_l Y m)
  have hsub : ∀ {τ' : Type} (b : Fin dd → MvPowerSeries τ' C), (∀ i, MvPowerSeries.constantCoeff (b i) = 0) →
      ∀ m, MvPowerSeries.subst b (φ m) = VP.PhiAt Y ε b m := by
    intro τ' b hb m
    rw [hφ, VP.PhiAt_subst Y hε hb cX]
    congr 1
    funext i
    exact VP.subst_X hb i
  have hlin : ∀ m, φ m = ∑ j, VP.lin1 (φ m) j • (MvPowerSeries.X j : MvPowerSeries (Fin dd) C) := by
    intro m
    refine VP.lin_of_add (φ m) (cφ m) ?_
    rw [hsub _ (fun k => by rw [map_add, VP.cc_X, VP.cc_X, add_zero]) m, hsub _ (fun _ => VP.cc_X _) m,
      hsub _ (fun _ => VP.cc_X _) m]
    exact VP.PhiAt_add Y hε hadd (fun _ => VP.cc_X _) (fun _ => VP.cc_X _) m
  have hP := VP.cc_mapAt hε (VP.cc_exAt Y ha)
  show VP.mapAt ε (VP.exAt Y a) i = _
  rw [← VP.e_lAt Y hP i]
  show VP.exAt Y (fun m => VP.PhiAt Y ε a m) i = _
  congr 1
  funext m
  rw [← hsub a ha m, hlin m, VP.subst_sum ha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [VP.subst_smul ha, VP.subst_X ha]
  show VP.lin1 (VP.PhiAt Y ε MvPowerSeries.X m) j • a j = _
  rw [VP.linear_coeff_formal_law_at_X Y hε]

theorem valuation_eq_pair_of_projections' {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hK : KillSt Y p) (hP : ∀ o, ProjSt Y (p o))
    (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_projections Y p H Ls n (endoLog_holds Y) hK hP hT

end Formalism.L2.FormalSeriesBounds
