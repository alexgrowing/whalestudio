import Formalism.LocalToGlobal.CharacterGerms.RowTieValBr

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

def mapAt (ε : Pt C 1 dd) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (ε i)

theorem comp_eq_map_at {n : ℕ} (ε : Pt C 1 dd) (a : Pt C n dd) : comp1 ε a = mapAt ε a := by
  unfold comp1 mapAt ev
  funext i
  congr 1
  funext p
  first
    | (rw [Fin.fin_one_eq_zero p.1]; rfl)
    | (simp [Fin.fin_one_eq_zero p.1])

theorem cc_mapAt {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (mapAt ε a i) = 0 := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.2)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hb]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hε i, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 he
    have hmem : s ∈ e.support := Finsupp.mem_support_iff.2 (by simpa using hs)
    have h0 : MvPowerSeries.constantCoeff (e.prod fun s k => a s.2 ^ k) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero hmem
      rw [map_pow, ha s.2, zero_pow (Finsupp.mem_support_iff.1 hmem)]
    rw [h0, smul_zero]

theorem mapAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    (ε : Pt C 1 dd) {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (i : Fin dd) :
    MvPowerSeries.subst A (mapAt ε u i) = mapAt ε (fun i => MvPowerSeries.subst A (u i)) i := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => u q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hu q.2)
  have hA' : MvPowerSeries.HasSubst A := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  rw [MvPowerSeries.subst_comp_subst_apply hb hA']

theorem subst_pow' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (k : ℕ) :
    MvPowerSeries.subst a (f ^ k) = MvPowerSeries.subst a f ^ k := by
  have hb : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  first
    | exact MvPowerSeries.subst_pow hb f k
    | (rw [← MvPowerSeries.coe_substAlgHom hb, map_pow])

variable (Y : FBChart C V O dd)

theorem mapAt_act {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) (x : O)
    (hc : comp1 ε (Y.B.A.act x) = comp1 (Y.B.A.act x) ε) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    mapAt ε (actAt Y x a) = actAt Y x (mapAt ε a) := by
  unfold actAt
  have hA : ∀ i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := fun i => Y.B.A.2 x i
  rw [comp_eq_map_at, comp_eq_map_at] at hc
  funext i
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.2)
  have hAs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => Y.B.A.act x q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hA q.2)
  have hεs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => ε q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hε q.2)
  have hci : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => Y.B.A.act x q.2) (ε i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => ε q.2) (Y.B.A.act x i) := congrFun hc i
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      MvPowerSeries.subst (fun q' : Fin 1 × Fin dd => a q'.2) (Y.B.A.act x q.2)) (ε i) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      MvPowerSeries.subst (fun q' : Fin 1 × Fin dd => a q'.2) (ε q.2)) (Y.B.A.act x i)
  rw [← MvPowerSeries.subst_comp_subst_apply hAs hb (ε i),
    ← MvPowerSeries.subst_comp_subst_apply hεs hb (Y.B.A.act x i), hci]

theorem cmp_at {ε ε' : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hε' : ∀ i, MvPowerSeries.constantCoeff (ε' i) = 0) {a b : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    MvPowerSeries.subst (P2 a b) (FB.expS C (ev (n := 2) ![comp1 ε (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 ε' (pt C dd 1)] Y.h)) =
      mvExp (hAt Y (mapAt ε a) b - hAt Y a (mapAt ε' b)) := by
  rw [eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, comp_eq_map_at, comp_eq_map_at]
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  have hcc : MvPowerSeries.constantCoeff (hAt Y (mapAt ε (pt C dd (0 : Fin 2))) (pt C dd (1 : Fin 2)) -
      hAt Y (pt C dd (0 : Fin 2)) (mapAt ε' (pt C dd (1 : Fin 2)))) = 0 := by
    rw [map_sub, cc_hAt Y (cc_mapAt hε k0) k1, cc_hAt Y k0 (cc_mapAt hε' k1), sub_zero]
  show MvPowerSeries.subst (P2 a b) (FB.expS C (hAt Y (mapAt ε (pt C dd (0 : Fin 2))) (pt C dd (1 : Fin 2)) -
      hAt Y (pt C dd (0 : Fin 2)) (mapAt ε' (pt C dd (1 : Fin 2))))) = _
  rw [expS_eq _ hcc, subst_exp hP hcc, subst_sub' hP, hAt_subst Y hP (cc_mapAt hε k0) k1,
    hAt_subst Y hP k0 (cc_mapAt hε' k1), e0, e1]
  congr 3
  · funext i; rw [mapAt_subst hP ε k0, e0]
  · funext i; rw [mapAt_subst hP ε' k1, e1]

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem dmap_zePart (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (ε : Pt C 1 dd) (s : Orb × Fin 2) (m : Fin dd) :
    ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (ε m) • zePart Y p s j =
      ∑ c : I s.1 s.2, linAct ε ((p s.1).u s.2 c) m •
        (MvPowerSeries.X (⟨s.1, ⟨s.2, c⟩⟩ : WVO I) : MvPowerSeries (WVO I) C) := by
  unfold zePart
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.sum_smul]
  congr 1

theorem cross_of (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hE : EndoLogSt Y) (hK : KillSt Y p)
    (hP : ∀ o, ProjSt Y (p o)) : CrossSt Y p := by
  intro hs π hπ s s' hss
  obtain ⟨o, g⟩ := s
  obtain ⟨e, hei, he0, hadd, -, hcomm, hfix, himg, hcmp⟩ := hP o
  have hX := hπ.cc o g
  have hZ := hπ.cc s'.1 s'.2
  have hwZ := VP.cc_actAt Y Y.w0 hZ
  set Ad : PS C 2 dd := FB.expS C (ev (n := 2) ![comp1 (e g) (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 (e (1 - g)) (pt C dd 1)] Y.h) with hAd
  set W : PS C 1 dd := MvPowerSeries.subst (VP.P2 (π o g) (VP.actAt Y Y.w0 (π s'.1 s'.2))) Ad with hW
  have hWe := VP.cmp_at Y (he0 g) (he0 (1 - g)) hX hwZ
  have hWi : IntS V W := IntS.subst (VP.constantCoeff_pair_substitution hX hwZ)
    (VP.integral_pair_substitution (hπ.int o g) (VP.int_actAt Y _ hZ (hπ.int s'.1 s'.2))) (hcmp g)
  refine ⟨W ^ Y.k, ⟨hWi.pow _, by rw [map_pow, hW, hAd, hWe, VP.cc_mvExp', one_pow, V.v.map_one]⟩, ?_⟩
  have hA := VP.cc_pull1Pt Y p
  have pX : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (π o g i)) =
      VP.exAt Y (zePart Y p (o, g)) := funext fun i => (hπ.pull o g i).trans (toAllS_expPt Y p o g i)
  have pZ : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (π s'.1 s'.2 i)) =
      VP.exAt Y (zePart Y p s') := funext fun i => (hπ.pull s'.1 s'.2 i).trans (toAllS_expPt Y p s'.1 s'.2 i)
  have cA := VP.cc_exAt Y (cc_zePart Y p (o, g))
  have cB := VP.cc_exAt Y (cc_zePart Y p s')

  have m1 : VP.mapAt (e g) (VP.exAt Y (zePart Y p (o, g))) = VP.exAt Y (zePart Y p (o, g)) := by
    funext i
    rw [show VP.mapAt (e g) (VP.exAt Y (zePart Y p (o, g))) i = _ from
      hE (e g) (he0 g) (hadd g) (WVO I) (zePart Y p (o, g)) (cc_zePart Y p (o, g)) i]
    congr 1
    funext m
    rw [dmap_zePart]
    unfold zePart
    exact Finset.sum_congr rfl fun c _ => by rw [hfix g c]
  have m2 : VP.mapAt (e (1 - g)) (VP.exAt Y (zePart Y p s')) = fun _ => 0 := by
    funext i
    rw [show VP.mapAt (e (1 - g)) (VP.exAt Y (zePart Y p s')) i = _ from
      hE (e (1 - g)) (he0 _) (hadd _) (WVO I) (zePart Y p s') (cc_zePart Y p s') i]
    have hz : (fun m => ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e (1 - g) m) • zePart Y p s' j) =
        fun _ => 0 := by
      funext m
      rw [dmap_zePart]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hK hs o (1 - g) (e (1 - g)) (he0 _) (hcomm _) (himg _) ⟨s'.1, ⟨s'.2, c⟩⟩ hss]
      exact zero_smul _ _
    rw [hz, VP.exAt_zero]
  rw [VP.Aterm_eq Y π hπ.cc, VP.exp_nsmul (VP.cc_hAt Y hX hwZ)]
  unfold pull1
  rw [VP.subst_pow' hA, VP.subst_pow' hA]
  congr 1
  rw [hW, hAd, hWe, VP.subst_exp hA (VP.cc_hAt Y hX hwZ),
    VP.subst_exp hA (by rw [map_sub, VP.cc_hAt Y (VP.cc_mapAt (he0 g) hX) hwZ,
      VP.cc_hAt Y hX (VP.cc_mapAt (he0 _) hwZ), sub_zero]),
    VP.subst_sub' hA, VP.hAt_subst Y hA hX hwZ, VP.hAt_subst Y hA (VP.cc_mapAt (he0 g) hX) hwZ,
    VP.hAt_subst Y hA hX (VP.cc_mapAt (he0 _) hwZ)]
  have a1 : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2)
      (VP.actAt Y Y.w0 (π s'.1 s'.2) i)) = VP.actAt Y Y.w0 (VP.exAt Y (zePart Y p s')) := by
    funext i; rw [VP.actAt_subst Y hA hZ, pZ]
  have a2 : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2)
      (VP.mapAt (e g) (π o g) i)) = VP.exAt Y (zePart Y p (o, g)) := by
    funext i; rw [VP.mapAt_subst hA (e g) hX, pX, m1]
  have a3 : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2)
      (VP.mapAt (e (1 - g)) (VP.actAt Y Y.w0 (π s'.1 s'.2)) i)) = fun _ => 0 := by
    funext i
    rw [VP.mapAt_subst hA (e (1 - g)) hwZ, a1, VP.mapAt_act Y (he0 _) Y.w0 (hcomm _ _) cB, m2, VP.actAt_zero]
  rw [a1, a2, a3, pX, VP.hAt_zero_right Y cA, sub_zero]

theorem valuation_eq_pair_of_projections (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (hE : EndoLogSt Y) (hK : KillSt Y p) (hP : ∀ o, ProjSt Y (p o))
    (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : ValEqPSt Y p H Ls n :=
  value_equation_of_projectors Y p H Ls n (projPull_of Y p hE hK hP) hT (cross_of Y p hE hK hP)

end Formalism.L2.FormalSeriesBounds
