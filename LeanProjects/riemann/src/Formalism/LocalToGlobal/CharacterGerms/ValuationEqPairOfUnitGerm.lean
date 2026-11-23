import Formalism.LocalToGlobal.CharacterGerms.PullbackLogCoordsEvalZero
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  ext e
  rw [MvPowerSeries.coeff_subst (hs (fun _ => MvPowerSeries.constantCoeff_zero)), finsum_eq_single _ 0]
  · by_cases he : e = 0 <;> simp [he, MvPowerSeries.coeff_C, MvPowerSeries.coeff_one]
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ n => (0 : MvPowerSeries τ C) ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (zero_pow hs')
    simp [h0]

variable (Y : FBChart C V O dd)

def l (m : Fin dd) : MvPowerSeries (Fin dd) C := un1 (Y.lg m)

def e (k : Fin dd) : MvPowerSeries (Fin dd) C := un1 (Y.ex k)

theorem cc_l (m : Fin dd) : MvPowerSeries.constantCoeff (l Y m) = 0 := by
  have h := Y.lg_lin m 0 (by simp)
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.lg m) = 0
  rw [Finsupp.mapDomain_zero, h]
  simp

theorem cc_e (k : Fin dd) : MvPowerSeries.constantCoeff (e Y k) = 0 := by
  have h := Y.ex_const k
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) 0) (Y.ex k) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]

theorem exlg (n : Fin dd) : MvPowerSeries.subst (l Y) (e Y n) = MvPowerSeries.X n := by
  have ha : ∀ i, MvPowerSeries.constantCoeff (Y.lg i) = 0 := fun i => by
    rw [← constantCoeff_uncurry]; exact cc_l Y i
  show MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex n)) = _
  rw [uncurry_comp ha, Y.ex_lg]
  exact uncurry_X n

theorem lgex (m : Fin dd) : MvPowerSeries.subst (e Y) (l Y m) = MvPowerSeries.X m := by
  show MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 (Y.lg m)) = _
  rw [uncurry_comp Y.ex_const, Y.lg_ex]
  exact uncurry_X m

theorem cc_F (k : Fin dd) : MvPowerSeries.constantCoeff (Y.B.G.F k) = 0 := Y.B.G.const k

theorem ev_id (f : PS C 2 dd) : ev (n := 2) ![pt C dd 0, pt C dd 1] f = f := by
  have h : (fun q : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨i, k⟩; fin_cases i <;> rfl
  unfold ev
  rw [h, MvPowerSeries.subst_self]
  rfl

theorem l_add (m : Fin dd) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (l Y m) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (l Y m) +
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (l Y m) := by
  have hF : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = fun k => Y.B.G.F k :=
    funext fun k => ev_id (Y.B.G.F k)
  have h := Y.lg_add m
  rw [hF, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  show MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 (Y.lg m)) =
    MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 (Y.lg m)) +
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 (Y.lg m))
  rw [subst_singlePointUncurry (fun k => Y.B.G.const k), subst_singlePointUncurry (fun k => MvPowerSeries.constantCoeff_X _),
    subst_singlePointUncurry (fun k => MvPowerSeries.constantCoeff_X _)]
  exact h

theorem F_exZero (k : Fin dd) : MvPowerSeries.subst (exZero Y) (Y.B.G.F k) = e Y k := by

  set u : Fin 1 × Fin dd → MvPowerSeries (Fin dd) C := fun q => un1 (Y.ex q.2) with hu_def
  have hu : MvPowerSeries.HasSubst u := hs (fun q => cc_e Y q.2)
  have hz : MvPowerSeries.HasSubst (exZero Y) := hs (fun q => by
    unfold exZero
    split_ifs
    · exact cc_e Y q.2
    · simp)
  have hsw : MvPowerSeries.HasSubst
      (fun q : Fin 2 × Fin dd => (![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) q.1 q.2) :=
    hs (fun q => by
      rcases q with ⟨i, j⟩
      fin_cases i <;> exact MvPowerSeries.constantCoeff_X _)
  have hun : MvPowerSeries.HasSubst
      (fun q : Fin 2 × Fin dd => (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) q.1 q.2) :=
    hs (fun q => by
      rcases q with ⟨i, j⟩
      fin_cases i
      · simp
      · exact MvPowerSeries.constantCoeff_X _)
  have hu0 : MvPowerSeries.subst u (0 : MvPowerSeries (Fin 1 × Fin dd) C) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hu, map_zero]
  have hz0 : MvPowerSeries.subst (exZero Y) (0 : PS C 2 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hz, map_zero]
  have h1 := Y.B.G.comm k
  have h2 := congrArg (MvPowerSeries.subst u) (Y.B.G.unit k)
  unfold ev at h1 h2
  rw [← h1, MvPowerSeries.subst_comp_subst_apply hsw hz]
  rw [MvPowerSeries.subst_comp_subst_apply hun hu, MvPowerSeries.subst_X hu] at h2
  show _ = u (0, k)
  convert h2 using 2
  funext q
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [pt, MvPowerSeries.subst_X hz, exZero, hu0]
  · show MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((0 : Fin 2), j)) =
      MvPowerSeries.subst u (MvPowerSeries.X ((0 : Fin 1), j))
    rw [MvPowerSeries.subst_X hz, MvPowerSeries.subst_X hu]
    simp [exZero, u]

def J (m k : Fin dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv C k (l Y m))

theorem pderiv_l_zero (m i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv C i (l Y m)) = if m = i then 1 else 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add, Nat.cast_zero, Nat.cast_one, one_mul, mul_one]
  change MvPowerSeries.coeff (Finsupp.mapDomain (fun x : Fin dd => ((0 : Fin 1), x)) (Finsupp.single i 1))
    (Y.lg m) = _
  rw [Finsupp.mapDomain_single, Y.lg_lin m _ (by simp), MvPowerSeries.coeff_X]
  by_cases hmi : m = i
  · subst hmi; simp
  · rw [if_neg hmi, if_neg]
    intro h
    have := Finsupp.single_left_injective (one_ne_zero) h
    exact hmi (congrArg Prod.snd this).symm

theorem eqA (m i : Fin dd) :
    ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.G.F k)) * J Y m k =
      if m = i then 1 else 0 := by

  have hF := fun w => (ordGE_one_iff (Y.B.G.F w)).2 (Y.B.G.const w)
  have hX := fun (b : Fin 2) (w : Fin dd) =>
    (ordGE_one_iff (MvPowerSeries.X (b, w) : PS C 2 dd)).2 (MvPowerSeries.constantCoeff_X _)
  have hz : MvPowerSeries.HasSubst (exZero Y) := hs (fun q => by
    unfold exZero
    split_ifs
    · exact cc_e Y q.2
    · simp)
  have hsF : MvPowerSeries.HasSubst (fun k => Y.B.G.F k) := hs (fun k => Y.B.G.const k)
  have hsX1 : MvPowerSeries.HasSubst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) :=
    hs (fun k => MvPowerSeries.constantCoeff_X _)
  have h := congrArg (MvPowerSeries.pderiv C ((1 : Fin 2), i)) (l_add Y m)
  rw [map_add, pderiv_subst hF, pderiv_subst (hX 0), pderiv_subst (hX 1)] at h
  beta_reduce at h
  have s0 : ∑ w : Fin dd, MvPowerSeries.pderiv C ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), w) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv C w (l Y m)) = 0 :=
    Finset.sum_eq_zero (fun w _ => by rw [MvPowerSeries.pderiv_X_of_ne (by simp), zero_mul])
  have s1 : ∑ w : Fin dd, MvPowerSeries.pderiv C ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), w) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv C w (l Y m)) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv C i (l Y m)) := by
    rw [Finset.sum_eq_single i (fun w _ hw => by
        rw [MvPowerSeries.pderiv_X_of_ne (by simpa using hw), zero_mul]) (by simp),
      MvPowerSeries.pderiv_X_self, one_mul]
  rw [s0, s1, zero_add] at h
  have h2 := congrArg (MvPowerSeries.subst (exZero Y)) h
  rw [← MvPowerSeries.coe_substAlgHom hz, map_sum] at h2
  simp only [map_mul, MvPowerSeries.coe_substAlgHom] at h2
  rw [MvPowerSeries.subst_comp_subst_apply hsX1 hz] at h2
  simp only [MvPowerSeries.subst_comp_subst_apply hsF hz, F_exZero, MvPowerSeries.subst_X hz] at h2
  have hz1 : (fun s : Fin dd => exZero Y ((1 : Fin 2), s)) = fun _ => 0 := funext fun s => by simp [exZero]
  rw [hz1, subst_zeroPt, pderiv_l_zero] at h2
  refine h2.trans ?_
  split_ifs <;> simp

theorem eqK (n k : Fin dd) :
    ∑ m, J Y m k * MvPowerSeries.pderiv C m (e Y n) = if n = k then 1 else 0 := by

  have hl := fun w => (ordGE_one_iff (l Y w)).2 (cc_l Y w)
  have hsE : MvPowerSeries.HasSubst (e Y) := hs (cc_e Y)
  have hsL : MvPowerSeries.HasSubst (l Y) := hs (cc_l Y)
  have key : ∀ g, MvPowerSeries.subst (e Y) (MvPowerSeries.subst (l Y) g) = g := fun g => by
    rw [MvPowerSeries.subst_comp_subst_apply hsL hsE]
    simp_rw [lgex Y]
    rw [MvPowerSeries.subst_self]
    rfl
  have h := congrArg (MvPowerSeries.subst (e Y)) (congrArg (MvPowerSeries.pderiv C k) (exlg Y n))
  rw [pderiv_subst hl k, ← MvPowerSeries.coe_substAlgHom hsE, map_sum] at h
  simp only [map_mul, MvPowerSeries.coe_substAlgHom, key] at h
  refine h.trans ?_
  by_cases hnk : n = k
  · subst hnk
    rw [MvPowerSeries.pderiv_X_self, if_pos rfl, ← MvPowerSeries.coe_substAlgHom hsE, map_one]
  · rw [MvPowerSeries.pderiv_X_of_ne hnk, if_neg hnk, ← MvPowerSeries.coe_substAlgHom hsE, map_zero]

end VP

theorem expODE {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) : ExpODESt Y := by
  intro i j
  have hFK : Y.B.FK C = Y.B.G.F := by
    funext q
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F q) = _
    simp
  rw [hFK]

  let A : Matrix (Fin dd) (Fin dd) (MvPowerSeries (Fin dd) C) := fun a k =>
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), a) (Y.B.G.F k))
  let Jt : Matrix (Fin dd) (Fin dd) (MvPowerSeries (Fin dd) C) := fun k m => VP.J Y m k
  let D : Matrix (Fin dd) (Fin dd) (MvPowerSeries (Fin dd) C) := fun m n =>
    MvPowerSeries.pderiv C m (VP.e Y n)
  have hAJ : A * Jt = 1 := by
    refine Matrix.ext fun a m => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (VP.eqA Y m a).trans ?_
    by_cases h : m = a
    · subst h; simp
    · simp [h, Ne.symm h]
  have hJD : Jt * D = 1 := by
    refine Matrix.ext fun k n => ?_
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (VP.eqK Y n k).trans ?_
    by_cases h : n = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have hDA : D = A := calc
    D = (A * Jt) * D := by rw [hAJ, Matrix.one_mul]
    _ = A * (Jt * D) := Matrix.mul_assoc A Jt D
    _ = A := by rw [hJD, Matrix.mul_one]
  exact congrFun (congrFun hDA i) j

theorem logCoord_holds {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : LogCoordSt Y p :=
  logCoord_of_ode p (expODE Y)

theorem valuation_eq_pair_of_unit_germ {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
    [NeZero d] {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (H : ∀ o, (Y.raw (p o)).Hyps V) (Ls : LetSys C dd) (n : ℕ)
    (h2 : UnitSt Y p) (h3 : GermLiftSt Y p H) : ValEqPSt Y p H Ls n :=
  valuation_eq_pair_of_log_unit_germ Y p H Ls n (logCoord_holds Y p) h2 h3

end Formalism.L2.FormalSeriesBounds
