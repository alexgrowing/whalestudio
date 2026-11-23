import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFBTop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitDef

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLie

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePSplit

section Lin

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def linM (φ : Pt C 1 dd) : Matrix (Fin dd) (Fin dd) C :=
  Matrix.of fun i j => coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linAct_eq (φ : Pt C 1 dd) (v : Fin dd → C) : linAct φ v = Matrix.mulVec (linM φ) v := by
  funext i
  rfl

theorem coeff_single_cc {σ : Type} (s : σ) (f : MvPowerSeries σ C) :
    coeff (Finsupp.single s 1) f = constantCoeff (pderiv C s f) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (g : MvPowerSeries σ C) : constantCoeff (MvPowerSeries.subst a g) = constantCoeff g := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha), finsum_eq_single _ 0]
  · simp
  · intro d hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]

theorem lin_comp1 {φ ψ : Pt C 1 dd} (hψ : ∀ k, constantCoeff (ψ k) = 0) :
    linM (comp1 φ ψ) = linM φ * linM ψ := by
  ext i j
  simp only [linM, Matrix.of_apply, Matrix.mul_apply, coeff_single_cc]
  show constantCoeff (pderiv C ((0 : Fin 1), j)
    (MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2) (φ i))) = _
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2)
    (fun p => (z0_1 ψ hψ) p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cc_subst (a := fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2)
    (fun p => (z0_1 ψ hψ) p.1 p.2)]
  rfl

theorem lin_pt : linM (pt C (n := 1) dd 0) = 1 := by
  ext i j
  simp only [linM, pt, Matrix.of_apply, Matrix.one_apply, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h2
    apply h
    have h3 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h2
    exact (Prod.mk.inj h3).2.symm

theorem cc_pderiv_X {σ : Type} [DecidableEq σ] (s t : σ) : constantCoeff (pderiv C s (X t : MvPowerSeries σ C)) = if t = s then 1 else 0 := by
  rw [MvPowerSeries.pderiv_X]
  by_cases h : t = s
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem formal_group_coeff_first_linear {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (i j : Fin dd) :
    constantCoeff (pderiv C ((0 : Fin 2), j) (Y.B.G.F i)) = if i = j then 1 else 0 := by
  have hA : Z0 (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  have h := congrArg (fun f => constantCoeff (pderiv C ((0 : Fin 1), j) f)) (formalGroupLaw_ev_x_zero Y (pt C (n := 1) dd 0) (z0_pt 0) i)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev at h
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt, Pi.zero_apply, map_zero,
    mul_zero, Finset.sum_const_zero, add_zero, cc_pderiv_X, Prod.mk.injEq, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]

theorem formal_group_coeff_second_linear {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (i j : Fin dd) :
    constantCoeff (pderiv C ((1 : Fin 2), j) (Y.B.G.F i)) = if i = j then 1 else 0 := by
  have hA : Z0 (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j'; fin_cases k
    · simp
    · exact z0_pt 0 j'
  have h := congrArg (fun f => constantCoeff (pderiv C ((0 : Fin 1), j) f)) (Y.B.G.unit i)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev at h
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt, Pi.zero_apply, map_zero,
    mul_zero, Finset.sum_const_zero, zero_add, cc_pderiv_X, Prod.mk.injEq, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]

theorem lin_addOf {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {A B : Pt C 1 dd}
    (hA : ∀ k, constantCoeff (A k) = 0) (hB : ∀ k, constantCoeff (B k) = 0) :
    linM (addOf Y.B.G.F A B) = linM A + linM B := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C 1 dd) := constant_zero_two_points A B hA hB
  ext i j
  simp only [linM, Matrix.of_apply, Matrix.add_apply, coeff_single_cc]
  show constantCoeff (pderiv C ((0 : Fin 1), j)
    (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2) (Y.B.G.F i))) = _
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hZ p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hZ p.1 p.2), formal_group_coeff_first_linear Y, formal_group_coeff_second_linear Y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Lin

section Glue

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def linHom (Y : FBChart C V O dd) : O →+* Matrix (Fin dd) (Fin dd) C where
  toFun x := linM (Y.B.A.act x)
  map_one' := by rw [Y.B.A.one_act]; exact lin_pt
  map_mul' x y := by rw [Y.B.A.mul_act]; exact lin_comp1 (Y.B.A.const y)
  map_zero' := by
    have e := Y.B.A.add_act 0 0
    rw [add_zero] at e
    have h : linM (Y.B.A.act 0) = linM (Y.B.A.act 0) + linM (Y.B.A.act 0) := by
      conv_lhs => rw [e]
      exact lin_addOf Y (Y.B.A.const 0) (Y.B.A.const 0)
    have h2 := congrArg (fun M => M - linM (Y.B.A.act 0)) h
    simp only [sub_self, add_sub_cancel_right] at h2
    exact h2.symm
  map_add' x y := by rw [Y.B.A.add_act]; exact lin_addOf Y (Y.B.A.const x) (Y.B.A.const y)

def KeySt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (g : Fin 2) (ε : O), (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ a, V.MM (p.em g a ε - 1)) →
    (∀ x : O, (∀ a, V.MM (p.em g a x)) → ∃ y, ε * x = (V.l : O) * y) →
    ∀ e : Pt C 1 dd, (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) →
    ∀ x : O, Polynomial.aeval (linM (Y.B.A.act x))
      (∏ c : ZMod d, (Polynomial.X - Polynomial.C (p.em g c x))) * linM e = 0

theorem proj_core (Y : FBChart C V O dd) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (e : Pt C 1 dd)
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) :
    (∀ i, MvPowerSeries.constantCoeff (e i) = 0) ∧ comp1 e e = e ∧
      (∀ a, comp1 e (Y.B.A.act a) = comp1 (Y.B.A.act a) e) := by
  have hT := tends_of_endomorphism_limit Y he
  have e0 : ∀ i, constantCoeff (e i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨e0, ?_, ?_⟩
  · funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (ε ^ V.l ^ n))
      (fun n => act0 _) e0 hT hT i
    have R := tendsS_of_small lSmall_holds Y (x := fun n => ε ^ V.l ^ n * ε ^ V.l ^ n) (sq_cong hε) hT i
    have eq : (fun n => comp1 (Y.B.A.act (ε ^ V.l ^ n)) (Y.B.A.act (ε ^ V.l ^ n)) i) =
        fun n => Y.B.A.act (ε ^ V.l ^ n * ε ^ V.l ^ n) i := funext fun n => by rw [Y.B.A.mul_act]
    rw [eq] at L
    exact L.unique R
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (ε ^ V.l ^ n))
      (fun n => act0 _) e0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R

theorem projLie_of (hK : KeySt) (hS : SplitSt) : ProjLieSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g ε hε hε1 hεx e he v
  obtain ⟨e0, hidem, hcomm⟩ := proj_core Y ε hε e he
  have hinj : Function.Injective (fun c : ZMod d => p.em g c) := by
    intro c c' h
    by_contra hne
    obtain ⟨x, hx⟩ := p.em_sep (g, c) (g, c') (by simp [hne])
    have h2 : p.em g c = p.em g c' := h
    rw [h2, sub_self, AddValuation.map_zero] at hx
    simp at hx
  have hPP : linM e * linM e = linM e := by rw [← lin_comp1 e0, hidem]
  have hPM : ∀ x, linM e * linHom Y x = linHom Y x * linM e := fun x => by
    show linM e * linM (Y.B.A.act x) = linM (Y.B.A.act x) * linM e
    rw [← lin_comp1 (Y.B.A.const x), ← lin_comp1 e0, hcomm x]
  obtain ⟨w, hw, hwe⟩ := hS C O dd (ZMod d) (linHom Y) (linM e) (fun c => p.em g c) hPP hPM hinj
    (fun x => hK C V O dd Y d I p g ε hε hε1 hεx e he x) v
  have hb : ∀ c, ∃ b : I g → C, (∀ c', p.ty g c' ≠ c → b c' = 0) ∧ w c = ∑ c', b c' • p.u g c' := fun c =>
    p.u_full g c (w c) fun x => by rw [linAct_eq]; exact hwe c x
  choose b _ hbw using hb
  refine ⟨fun c' => ∑ c, b c c', ?_⟩
  rw [linAct_eq, hw]
  simp_rw [hbw, Finset.sum_smul]
  exact Finset.sum_comm

end Glue

end RowTiePLie

end Formalism.L2.FormalSeriesBounds
