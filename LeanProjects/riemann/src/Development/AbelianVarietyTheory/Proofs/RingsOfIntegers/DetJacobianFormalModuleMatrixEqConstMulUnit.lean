import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermPointsNoConstantTermFirstZero

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB IsLocalRing

namespace GlobalTheory.PlaceInt.MatJac

open GlobalTheory.GaugeAdjoint

section General

variable {R : Type} [CommRing R] {d n : ℕ} (G : FGLaw R d)

def invJ (z : Pt R n d) (a l : Fin d) : PS R n d := ev ![z, 0] (pderiv R ((1 : Fin 2), l) (G.F a))

def invD (q : Fin n × Fin d) (f : PS R n d) : PS R n d :=
  ∑ c, pderiv R (q.1, c) f * invJ G (pt R d q.1) c q.2

theorem const_invJ {z : Pt R n d} (hz : ∀ i, constantCoeff (z i) = 0) (a l : Fin d) :
    constantCoeff (invJ G z a l) = if a = l then 1 else 0 := by
  have hz0 : ∀ i, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp
  unfold invJ
  rw [GlobalTheory.DerivEndo.cc_ev (GlobalTheory.DerivEndo.noConst_two hz hz0), ← GlobalTheory.FormalMulN.coeff_single_one]
  exact GlobalTheory.FormalMulN.lin_F_right G a l

theorem invD_ev {m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) (q : Fin n × Fin d) :
    invD G q (ev a f) = ∑ j, ∑ l, ev a (pderiv R (j, l) f) * invD G q (a j l) := by
  unfold invD
  calc _ = ∑ c, ∑ j, ∑ l, ev a (pderiv R (j, l) f) * pderiv R (q.1, c) (a j l) *
        invJ G (pt R d q.1) c q.2 := by
        simp_rw [GlobalTheory.DerivEndo.pderiv_ev ha, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring

private theorem pderiv_pt_eq_ite {k : ℕ} (j j' : Fin k) (l c : Fin d) :
    pderiv R (j', c) (pt R d j l) = if (j, l) = (j', c) then 1 else 0 := by
  show pderiv R (j', c) (X (j, l)) = _
  split_ifs with h
  · rw [h, pderiv_X_self]
  · exact pderiv_X_of_ne h

private theorem formalGroup_add_apply_eq_ev {k : ℕ} (x y : Pt R k d) (a : Fin d) :
    G.add x y a = ev ![x, y] (G.F a) := rfl

private theorem ev_ev_pair_eq_ev_pair_ev {k m : ℕ} (b : Fin m → Pt R k d) (hb : ∀ j i, constantCoeff (b j i) = 0)
    (x y : Pt R m d) (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (g : PS R 2 d) :
    ev b (ev ![x, y] g) = ev ![fun i => ev b (x i), fun i => ev b (y i)] g := by
  rw [GlobalTheory.DerivEndo.ev_ev hb (GlobalTheory.DerivEndo.noConst_two hx hy)]
  congr 1
  funext j i
  fin_cases j <;> rfl

theorem right_invJ {z w : Pt R n d} (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) (a i : Fin d) :
    ∑ c, ev ![z, w] (pderiv R ((1 : Fin 2), c) (G.F a)) * invJ G w c i = invJ G (G.add z w) a i := by
  have hz0 : ∀ i, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp
  have c0 := GlobalTheory.DerivEndo.cc_pt (R := R) (n := 3) (d := d) 0
  have c1 := GlobalTheory.DerivEndo.cc_pt (R := R) (n := 3) (d := d) 1
  have c2 := GlobalTheory.DerivEndo.cc_pt (R := R) (n := 3) (d := d) 2
  have c01 := GlobalTheory.FormalMulN.const_add G c0 c1
  have c12 := GlobalTheory.FormalMulN.const_add G c1 c2
  have e3 : ∀ j i, constantCoeff ((![z, w, 0] : Fin 3 → Pt R n d) j i) = 0 :=
    GlobalTheory.FormalMulN.const_three hz hw hz0
  have hL0 : ∀ l, pderiv R ((2 : Fin 3), i) (G.add (pt R d 0) (pt R d 1) l) = 0 := by
    intro l
    rw [formalGroup_add_apply_eq_ev, GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c0 c1)]
    simp [pderiv_pt_eq_ite, Fin.sum_univ_two]
  have hR : ∀ l, pderiv R ((2 : Fin 3), i) (G.add (pt R d 1) (pt R d 2) l) =
      ev ![pt R (n := 3) d 1, pt R d 2] (pderiv R ((1 : Fin 2), i) (G.F l)) := by
    intro l
    rw [formalGroup_add_apply_eq_ev, GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c1 c2)]
    simp [pderiv_pt_eq_ite, Fin.sum_univ_two]
  have hA := congrArg (fun P : Pt R 3 d => pderiv R ((2 : Fin 3), i) (P a))
    (GlobalTheory.FormalMulN.add_assoc_pt G c0 c1 c2)
  rw [formalGroup_add_apply_eq_ev G (G.add _ _) _ a, formalGroup_add_apply_eq_ev G (pt R d 0) _ a,
    GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c01 c2),
    GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c0 c12)] at hA
  simp [Fin.sum_univ_two, hL0, hR, pderiv_pt_eq_ite] at hA
  have f0 : (fun i => ev ![z, w, 0] (pt R (n := 3) d 0 i)) = z := GlobalTheory.FormalMulN.ev_pt_fun e3 0
  have f1 : (fun i => ev ![z, w, 0] (pt R (n := 3) d 1 i)) = w := GlobalTheory.FormalMulN.ev_pt_fun e3 1
  have f2 : (fun i => ev ![z, w, 0] (pt R (n := 3) d 2 i)) = 0 := GlobalTheory.FormalMulN.ev_pt_fun e3 2
  have fa0 : (fun i => ev ![z, w, 0] (G.add (pt R (n := 3) d 0) (pt R d 1) i)) = G.add z w := by
    rw [GlobalTheory.FormalMulN.ev_add_pts G c0 c1 e3, f0, f1]
  have fa1 : (fun i => ev ![z, w, 0] (G.add (pt R (n := 3) d 1) (pt R d 2) i)) = w := by
    rw [GlobalTheory.FormalMulN.ev_add_pts G c1 c2 e3, f1, f2, GlobalTheory.FormalMulN.add_zero_pt G hw]
  have hB := congrArg (ev ![z, w, 0]) hA
  rw [ev_ev_pair_eq_ev_pair_ev _ e3 _ _ c01 c2, fa0, f2, GlobalTheory.DerivEndo.ev_sum e3] at hB
  simp only [GlobalTheory.DerivEndo.ev_mul e3, ev_ev_pair_eq_ev_pair_ev _ e3 _ _ c0 c12, ev_ev_pair_eq_ev_pair_ev _ e3 _ _ c1 c2,
    f0, f1, f2, fa1] at hB
  exact hB.symm

theorem ev_left_eq {z w : Pt R n d} (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) (a c : Fin d) :
    ev ![z, w] (pderiv R ((0 : Fin 2), c) (G.F a)) = ev ![w, z] (pderiv R ((1 : Fin 2), c) (G.F a)) := by
  have h2 : ∀ j i, constantCoeff ((![pt R (n := 2) d 1, pt R (n := 2) d 0] : Fin 2 → Pt R 2 d) j i) = 0 :=
    GlobalTheory.DerivEndo.noConst_two (GlobalTheory.DerivEndo.cc_pt 1) (GlobalTheory.DerivEndo.cc_pt 0)
  have hzw := GlobalTheory.DerivEndo.noConst_two hz hw
  have hc : G.F a = ev ![pt R (n := 2) d 1, pt R (n := 2) d 0] (G.F a) := by
    have h := GlobalTheory.FormalMulN.add_comm_pt G (GlobalTheory.DerivEndo.cc_pt (R := R) (n := 2) (d := d) 0)
      (GlobalTheory.DerivEndo.cc_pt 1)
    rw [GlobalTheory.DerivEndo.add_pt] at h
    exact congrFun h a
  have hd : pderiv R ((0 : Fin 2), c) (G.F a) =
      ev ![pt R (n := 2) d 1, pt R (n := 2) d 0] (pderiv R ((1 : Fin 2), c) (G.F a)) := by
    conv_lhs => rw [hc]
    rw [GlobalTheory.DerivEndo.pderiv_ev h2]
    simp [Fin.sum_univ_two, pderiv_pt_eq_ite]
  rw [hd, ev_ev_pair_eq_ev_pair_ev _ hzw _ _ (GlobalTheory.DerivEndo.cc_pt 1) (GlobalTheory.DerivEndo.cc_pt 0),
    GlobalTheory.FormalMulN.ev_pt_fun hzw 0, GlobalTheory.FormalMulN.ev_pt_fun hzw 1]
  rfl

def Inv (z : Pt R n d) : Prop :=
  (∀ i, constantCoeff (z i) = 0) ∧
    ∀ q : Fin n × Fin d, ∃ u : Fin d → R, ∀ a, invD G q (z a) = ∑ l, invJ G z a l * C (u l)

theorem inv_zero : Inv G (0 : Pt R n d) := by
  refine ⟨fun i => by simp, fun q => ⟨0, fun a => ?_⟩⟩
  simp [invD]

theorem inv_pt (j : Fin n) : Inv G (pt R d j) := by
  refine ⟨GlobalTheory.DerivEndo.cc_pt j, fun q => ⟨fun l => if j = q.1 ∧ l = q.2 then 1 else 0, fun a => ?_⟩⟩
  unfold invD
  simp only [pderiv_pt_eq_ite]
  by_cases h : j = q.1
  · subst h
    simp [Prod.mk.injEq, apply_ite (C (σ := Fin n × Fin d) (R := R)), mul_ite, ite_mul]
  · simp [h]

theorem inv_add {z w : Pt R n d} (hz : Inv G z) (hw : Inv G w) : Inv G (G.add z w) := by
  obtain ⟨hz0, hzu⟩ := hz
  obtain ⟨hw0, hwu⟩ := hw
  refine ⟨GlobalTheory.FormalMulN.const_add G hz0 hw0, fun q => ?_⟩
  obtain ⟨u, hu⟩ := hzu q
  obtain ⟨v, hv⟩ := hwu q
  refine ⟨u + v, fun a => ?_⟩
  have hZ : ∀ m, ∑ l, ev ![z, w] (pderiv R ((0 : Fin 2), l) (G.F a)) * invJ G z l m =
      invJ G (G.add z w) a m := by
    intro m
    simp_rw [ev_left_eq G hz0 hw0]
    rw [right_invJ G hw0 hz0, GlobalTheory.FormalMulN.add_comm_pt G hw0 hz0]
  have hW : ∀ m, ∑ l, ev ![z, w] (pderiv R ((1 : Fin 2), l) (G.F a)) * invJ G w l m =
      invJ G (G.add z w) a m := fun m => right_invJ G hz0 hw0 a m
  rw [formalGroup_add_apply_eq_ev, invD_ev G (GlobalTheory.DerivEndo.noConst_two hz0 hw0), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hu, hv]
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp_rw [← hZ, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · simp_rw [← hW, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

private theorem comp1_apply_eq_ev_single {k : ℕ} (φ : Pt R 1 d) (z : Pt R k d) (a : Fin d) :
    comp1 φ z a = ev ![z] (φ a) := rfl

private theorem ev_single_ev_restrict_first_axis {k : ℕ} (z : Pt R k d) (hz : ∀ i, constantCoeff (z i) = 0) (g : PS R 2 d) :
    ev ![z] (ev (n := 1) ![pt R d 0, 0] g) = ev ![z, 0] g := by
  have h1 := GlobalTheory.DerivEndo.noConst_one hz
  rw [ev_ev_pair_eq_ev_pair_ev ![z] h1 (pt R d 0) 0 (GlobalTheory.DerivEndo.cc_pt 0) (fun i => by simp),
    GlobalTheory.FormalMulN.ev_pt_fun h1 0, GlobalTheory.FormalMulN.ev_zero_fun h1]
  rfl

theorem inv_comp (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hom : comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)))
    {z : Pt R n d} (hz : Inv G z) : Inv G (comp1 φ z) := by
  obtain ⟨hz0, hzu⟩ := hz
  have h1 := GlobalTheory.DerivEndo.noConst_one hz0
  have hc : ∀ i, constantCoeff (comp1 φ z i) = 0 := fun i => by
    rw [comp1_apply_eq_ev_single, GlobalTheory.DerivEndo.cc_ev h1]
    exact hφ i
  refine ⟨hc, fun q => ?_⟩
  obtain ⟨u, hu⟩ := hzu q
  refine ⟨(dLin φ).mulVec u, fun a => ?_⟩
  have hB : ∀ g : PS R 2 d, ev ![z] (ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] g)) =
      ev ![comp1 φ z, 0] g := by
    intro g
    rw [GlobalTheory.DerivEndo.ev_ev h1 (GlobalTheory.DerivEndo.noConst_one hφ)]
    have e : (fun j i => ev ![z] ((![φ] : Fin 1 → Pt R 1 d) j i)) = ![comp1 φ z] := by
      funext j i
      fin_cases j
      rfl
    rw [e, ev_single_ev_restrict_first_axis (comp1 φ z) hc]
  have K : ∀ m, ∑ l, ev ![z] (pderiv R ((0 : Fin 1), l) (φ a)) * invJ G z l m =
      ∑ b, invJ G (comp1 φ z) a b * C (dLin φ b m) := by
    intro m
    have hj := congrArg (ev ![z]) (GlobalTheory.DerivEndo.jac_endo G φ hφ hom a m)
    simp only [GlobalTheory.DerivEndo.ev_sum h1, GlobalTheory.DerivEndo.ev_mul h1, GlobalTheory.DerivEndo.ev_C, hB,
      ev_single_ev_restrict_first_axis z hz0] at hj
    exact hj
  rw [comp1_apply_eq_ev_single, invD_ev G h1]
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, hu]
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, K]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem isUnit_det_of_const {σ ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPowerSeries σ R))
    (h : (constantCoeff (σ := σ) (R := R)).mapMatrix M = 1) : IsUnit M.det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, h, Matrix.det_one]
  exact isUnit_one

def blockJ (z : Fin n → Pt R n d) : Matrix (Fin n × Fin d) (Fin n × Fin d) (PS R n d) :=
  Matrix.of fun p q => if p.1 = q.1 then invJ G (z p.1) p.2 q.2 else 0

theorem const_blockJ {z : Fin n → Pt R n d} (hz : ∀ b i, constantCoeff (z b i) = 0) :
    (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix (blockJ G z) = 1 := by
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
  unfold blockJ
  rw [Matrix.of_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, const_invJ G (hz p.1)]
    simp [Prod.ext_iff, h]
  · rw [if_neg h, map_zero, if_neg (fun e => h (congrArg Prod.fst e))]

theorem det_jac_of_inv (ψ : Fin n → Pt R n d) (hψ : ∀ b, Inv G (ψ b)) :
    ∃ U : (PS R n d)ˣ, Matrix.det (Matrix.of fun i j : Fin n × Fin d => pderiv R j (ψ i.1 i.2)) =
      C (Matrix.det (Matrix.of fun p q : Fin n × Fin d =>
        coeff (Finsupp.single q 1) (ψ p.1 p.2))) * (U : PS R n d) := by
  have hψ' : ∀ b, (∀ i, constantCoeff (ψ b i) = 0) ∧ ∀ q : Fin n × Fin d, ∃ u : Fin d → R,
      ∀ a, invD G q (ψ b a) = ∑ l, invJ G (ψ b) a l * C (u l) := hψ
  choose hψ0 u hu using hψ'
  set Jac := Matrix.of fun i j : Fin n × Fin d => pderiv R j (ψ i.1 i.2) with hJac
  set Lm := Matrix.of fun p q : Fin n × Fin d => coeff (Finsupp.single q 1) (ψ p.1 p.2) with hLm
  set Um : Matrix (Fin n × Fin d) (Fin n × Fin d) R := Matrix.of fun p q => u p.1 q p.2 with hUm
  have hpt0 : ∀ b i, constantCoeff ((fun b => pt R d b : Fin n → Pt R n d) b i) = 0 :=
    fun b i => GlobalTheory.DerivEndo.cc_pt b i
  have key : Jac * blockJ G (fun b => pt R d b) =
      blockJ G ψ * (C (σ := Fin n × Fin d) (R := R)).mapMatrix Um := by
    ext i q
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    have e1 : ∀ j1 : Fin n, ∑ j2, Jac i (j1, j2) * blockJ G (fun b => pt R d b) (j1, j2) q =
        if j1 = q.1 then ∑ c, pderiv R (j1, c) (ψ i.1 i.2) * invJ G (pt R d j1) c q.2 else 0 := by
      intro j1
      unfold blockJ
      split_ifs with h <;> simp [hJac, h]
    have e2 : ∀ p1 : Fin n, ∑ p2, blockJ G ψ i (p1, p2) *
        (C (σ := Fin n × Fin d) (R := R)).mapMatrix Um (p1, p2) q =
        if i.1 = p1 then ∑ l, invJ G (ψ i.1) i.2 l * C (u i.1 q l) else 0 := by
      intro p1
      unfold blockJ
      split_ifs with h
      · subst h
        simp [hUm]
      · simp [h]
    simp only [e1, e2, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← hu]
    rfl
  have hUpt : IsUnit (blockJ G (fun b => pt R d b)).det :=
    isUnit_det_of_const _ (const_blockJ G hpt0)
  have hUψ : IsUnit (blockJ G ψ).det := isUnit_det_of_const _ (const_blockJ G hψ0)
  have hL : (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix Jac = Lm := by
    ext p q
    simp [hJac, hLm, GlobalTheory.FormalMulN.coeff_single_one]
  have hCU : (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix
      ((C (σ := Fin n × Fin d) (R := R)).mapMatrix Um) = Um := by
    ext p q
    simp
  have hUL : Lm = Um := by
    have := congrArg (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix key
    rw [map_mul, map_mul, const_blockJ G hpt0, const_blockJ G hψ0, hL, hCU, mul_one, one_mul] at this
    exact this
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hdet
  refine ⟨hUψ.unit * hUpt.unit⁻¹, ?_⟩
  have e : Jac.det = Jac.det * (blockJ G (fun b => pt R d b)).det *
      ((hUpt.unit⁻¹ : (PS R n d)ˣ) : PS R n d) := by
    rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [e, hdet, hUL, Units.val_mul, IsUnit.unit_spec]
  ring

end General

section Local

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] [CharZero V] {d : ℕ}

theorem evV_eq_ev {m n : ℕ} {a : Fin m → Pt V n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS V m d) : evV a f = ev a f := by
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.PlaceInt.evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d)
    (fun p => a p.1 p.2) (fun p => by rw [ha p.1 p.2]; exact Submodule.zero_mem _)
  exact h3 (fun p => ha p.1 p.2) f

theorem inv_foldr {n : ℕ} (G : FGLaw V d) (L : List (Pt V n d)) (hL : ∀ z ∈ L, Inv G z) :
    Inv G (L.foldr (addV G.F) 0) := by
  induction L with
  | nil => exact inv_zero G
  | cons z L ih =>
    have hz := hL z (by simp)
    have hr := ih (fun x hx => hL x (by simp [hx]))
    have e : L.foldr (addV G.F) 0 = L.foldr (addV G.F) 0 := rfl
    have e2 : addV G.F z (L.foldr (addV G.F) 0) = G.add z (L.foldr (addV G.F) 0) := by
      funext i
      rw [formalGroup_add_apply_eq_ev]
      exact evV_eq_ev (GlobalTheory.DerivEndo.noConst_two hz.1 hr.1) _
    rw [List.foldr_cons, e2]
    exact inv_add G hz hr

theorem inv_matV {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {n : ℕ}
    (p : Matrix (Fin n) (Fin n) O) (b : Fin n) :
    Inv B.G (matV B p (fun j => pt V (n := n) d j) b) := by
  unfold matV
  apply inv_foldr
  intro z hz
  rw [List.mem_ofFn] at hz
  obtain ⟨j, rfl⟩ := hz
  have e : compV (B.A.act (p b j)) (pt V (n := n) d j) = comp1 (B.A.act (p b j)) (pt V d j) := by
    funext i
    rw [comp1_apply_eq_ev_single]
    exact evV_eq_ev (GlobalTheory.DerivEndo.noConst_one (GlobalTheory.DerivEndo.cc_pt j)) _
  rw [e]
  exact inv_comp B.G _ (B.A.const _) (B.A.hom _) (inv_pt B.G j)

end Local

theorem det_jacobian_matV : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), ∃ U : (PS V n d)ˣ,
    Matrix.det (Matrix.of fun i j : Fin n × Fin d =>
      MvPowerSeries.pderiv V j (matV B p (fun j => pt V (n := n) d j) i.1 i.2)) =
      MvPowerSeries.C (jacM B p) * (U : PS V n d) := by
  intro V _ _ _ _ _ d O _ _ B n p
  exact det_jac_of_inv B.G _ (fun b => inv_matV B p b)

end GlobalTheory.PlaceInt.MatJac
