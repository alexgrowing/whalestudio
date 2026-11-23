import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem Aterm_eq (Y : FBChart C V O dd) (π : Orb → Fin 2 → Fin dd → PS C 1 dd)
    (hπ0 : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0) (s s' : Orb × Fin 2) :
    Aterm Y π s s' = mvExp ((Y.k : C) • hAt Y (π s.1 s.2) (actAt Y Y.w0 (π s'.1 s'.2))) := by
  unfold Aterm
  rw [eval_two_points_eq_subst _ _ _ rfl, compose_one_action_eq_actAt]
  exact expS_eq _ (cc_smul _ (cc_hAt Y (hπ0 _ _) (cc_actAt Y _ (hπ0 _ _))))

theorem hRow_eq (Y : FBChart C V O dd) {J : Fin 2 → Type} [∀ g, Fintype (J g)] (q : PairData Y d J) :
    (Y.raw q).hRow = (Y.k : C) • hAt Y ((Y.raw q).expPt 0) ((Y.raw q).expPt 1) := by
  unfold RawChart.hRow hAt
  congr 2
  funext x
  obtain ⟨g, i⟩ := x
  fin_cases g <;> rfl

end VP

theorem pair_holds (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : PairSt Y p := by
  intro _ π hπ o
  have hX := hπ.cc o 0
  have hZ := hπ.cc o 1
  have hwX := VP.cc_actAt Y Y.w0 hX
  have hwZ := VP.cc_actAt Y Y.w0 hZ
  have hbZ := VP.cc_actAt Y (star Y.w0) hZ
  have hid := VP.pair_id Y hX hZ
  set W : PS C 1 dd := MvPowerSeries.subst (VP.P2 (VP.actAt Y Y.w0 (π o 0)) (π o 1)) Y.B.sy *
    MvPowerSeries.subst (VP.P2 (π o 0) (π o 1)) (Y.B.ad Y.w0) *
    MvPowerSeries.subst (VP.P3 (π o 0) (VP.actAt Y Y.w0 (π o 1)) (VP.actAt Y (star Y.w0) (π o 1))) Y.B.ph2 with hW
  have hWi : IntS V W :=
    ((IntS.subst (VP.constantCoeff_pair_substitution hwX hZ) (VP.integral_pair_substitution (VP.int_actAt Y _ hX (hπ.int o 0)) (hπ.int o 1)) Y.intSy).mul
      (IntS.subst (VP.constantCoeff_pair_substitution hX hZ) (VP.integral_pair_substitution (hπ.int o 0) (hπ.int o 1)) (Y.intAd _))).mul
      (IntS.subst (VP.constantCoeff_triple_substitution hX hwZ hbZ) (VP.integral_triple_substitution (hπ.int o 0) (VP.int_actAt Y _ hZ (hπ.int o 1))
        (VP.int_actAt Y _ hZ (hπ.int o 1))) Y.intPh2)
  have hW1 : MvPowerSeries.constantCoeff W = 1 := by rw [← hid, VP.cc_mvExp']
  refine ⟨W ^ Y.k, ⟨hWi.pow _, by rw [map_pow, hW1, one_pow, V.v.map_one]⟩, ?_⟩
  have c1 := VP.cc_hAt Y hX hwZ
  have c2 := VP.cc_hAt Y hZ hwX
  have c3 := VP.cc_hAt Y hX hZ
  have hprod : Aterm Y π (o, 0) (o, 1) * Aterm Y π (o, 1) (o, 0) =
      W ^ Y.k * mvExp ((Y.k : C) • VP.hAt Y (π o 0) (π o 1)) := by
    rw [VP.Aterm_eq Y π hπ.cc, VP.Aterm_eq Y π hπ.cc, ← VP.exp_add (VP.cc_smul _ c1) (VP.cc_smul _ c2), ← hid,
      ← VP.exp_nsmul (by rw [map_sub, map_add, c1, c2, c3]; simp),
      ← VP.exp_add (VP.cc_smul _ (by rw [map_sub, map_add, c1, c2, c3]; simp)) (VP.cc_smul _ c3)]
    congr 1
    rw [← smul_add, ← smul_add]
    congr 1
    ring
  have hE : ∀ g i, MvPowerSeries.constantCoeff ((Y.raw (p o)).expPt g i) = 0 := fun g i => by
    rw [← VP.cc_toAllS o, ← hπ.pull o g i]
    exact (VP.cc_subst_eq (VP.cc_pull1Pt Y p) _).trans (hπ.cc o g i)
  have hpull : pull1 Y p (mvExp ((Y.k : C) • VP.hAt Y (π o 0) (π o 1))) = toAllS o (mvExp (Y.raw (p o)).hRow) := by
    unfold pull1 toAllS
    rw [VP.subst_exp (VP.cc_pull1Pt Y p) (VP.cc_smul _ c3), VP.subst_smul (VP.cc_pull1Pt Y p),
      VP.hAt_subst Y (VP.cc_pull1Pt Y p) hX hZ, VP.hRow_eq,
      VP.subst_exp (fun _ => VP.cc_X _) (VP.cc_smul _ (VP.cc_hAt Y (hE 0) (hE 1))),
      VP.subst_smul (fun _ => VP.cc_X _), VP.hAt_subst Y (fun _ => VP.cc_X _) (hE 0) (hE 1)]
    congr 3
    · funext i; exact hπ.pull o 0 i
    · funext i; exact hπ.pull o 1 i
  rw [← VP.pullback_one_var_mul, hprod, VP.pullback_one_var_mul, hpull]

theorem valuation_eq_pair_of_biadditive_cross (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hP : ProjPullSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH)
    (h1 : BiaddSt Y p) (h2 : CrossSt Y p) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_pairing Y p H Ls n hP hT h1 h2 (pair_holds Y p)

end Formalism.L2.FormalSeriesBounds
