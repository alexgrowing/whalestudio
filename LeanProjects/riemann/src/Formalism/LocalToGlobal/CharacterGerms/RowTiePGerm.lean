import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace PartialDerivEval

section Ev

variable {R : Type} [CommRing R] {d : ℕ}

def Z0 {m n : ℕ} (a : Fin m → Pt R n d) : Prop := ∀ k i, constantCoeff (a k i) = 0

theorem hasSubst_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : Z0 a) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2

theorem ev_eq_alg {m n : ℕ} {a : Fin m → Pt R n d} (ha : Z0 a) (f : PS R m d) :
    ev a f = substAlgHom (R := R) (hasSubst_ev ha) f := by
  rw [coe_substAlgHom]; rfl

variable {m n : ℕ} {a : Fin m → Pt R n d}

theorem ev_add (ha : Z0 a) (f g : PS R m d) : ev a (f + g) = ev a f + ev a g := by
  simp only [ev_eq_alg ha, map_add]

theorem ev_sub (ha : Z0 a) (f g : PS R m d) : ev a (f - g) = ev a f - ev a g := by
  simp only [ev_eq_alg ha, map_sub]

theorem ev_neg (ha : Z0 a) (f : PS R m d) : ev a (-f) = -ev a f := by
  simp only [ev_eq_alg ha, map_neg]

theorem ev_mul (ha : Z0 a) (f g : PS R m d) : ev a (f * g) = ev a f * ev a g := by
  simp only [ev_eq_alg ha, map_mul]

theorem ev_zero (ha : Z0 a) : ev a (0 : PS R m d) = 0 := by
  simp only [ev_eq_alg ha, map_zero]

theorem ev_sum (ha : Z0 a) {ι : Type} (s : Finset ι) (f : ι → PS R m d) :
    ev a (∑ i ∈ s, f i) = ∑ i ∈ s, ev a (f i) := by
  simp only [ev_eq_alg ha, map_sum]

theorem ev_C (r : R) : ev a (C r : PS R m d) = C r := by
  unfold ev; rw [subst_C]

theorem ev_X (ha : Z0 a) (k : Fin m) (i : Fin d) : ev a (X (k, i) : PS R m d) = a k i := by
  unfold ev; rw [subst_X (hasSubst_ev ha)]

theorem ev_ev {l : ℕ} {b : Fin l → Pt R m d} (hb : Z0 b) (ha : Z0 a) (f : PS R l d) :
    ev a (ev b f) = ev (fun k i => ev a (b k i)) f := by
  unfold ev; rw [subst_comp_subst_apply (hasSubst_ev hb) (hasSubst_ev ha)]

theorem const_ev (ha : Z0 a) {f : PS R m d} (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_ev ha) (fun p => ha p.1 p.2) hf

theorem constantCoeff_ev (ha : Z0 a) (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  have h1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [h1]
  rw [ev_add ha, ev_C, map_add, constantCoeff_C, const_ev ha (by simp), add_zero]

theorem pderiv_eval_pair {a : Fin 2 → Pt R n d} (ha : Z0 a) (f : PS R 2 d) (q : Fin n × Fin d) :
    pderiv R q (ev a f) = ∑ j, ev a (pderiv R ((0 : Fin 2), j) f) * pderiv R q (a 0 j) +
      ∑ j, ev a (pderiv R ((1 : Fin 2), j) f) * pderiv R q (a 1 j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f q,
    Fintype.sum_prod_type, Fin.sum_univ_two]

theorem eval_points_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f := by
  unfold ev
  have : (fun p : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k <;> rfl
  rw [this, subst_self]
  rfl

end Ev

section IntSec

variable {C : Type} [Field C] {V : VF C} {τ : Type}

theorem intS_add {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f + g) := fun μ => by
  rw [map_add]; exact (hf μ).add (hg μ)

theorem intS_neg {f : MvPowerSeries τ C} (hf : IntS V f) : IntS V (-f) := fun μ => by
  rw [map_neg]; exact (hf μ).neg

theorem intS_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries τ C} (hf : ∀ i ∈ s, IntS V (f i)) :
    IntS V (∑ i ∈ s, f i) := fun μ => by
  rw [map_sum]; exact VF.Ge.sum fun i hi => hf i hi μ

theorem intS_C_mul {c : C} (hc : V.Ge 0 c) {f : MvPowerSeries τ C} (hf : IntS V f) : IntS V (MvPowerSeries.C c * f) :=
  fun μ => by rw [coeff_C_mul]; exact hc.mul_int (hf μ)

theorem intS_mul {f g : MvPowerSeries τ C} (hf : IntS V f) (hg : IntS V g) : IntS V (f * g) := by
  classical
  intro μ
  rw [coeff_mul]
  exact VF.Ge.sum fun p _ => (hf p.1).mul_int (hg p.2)

theorem intS_one : IntS V (1 : MvPowerSeries τ C) := by
  classical
  intro μ
  rw [coeff_one]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intS_pow {f : MvPowerSeries τ C} (hf : IntS V f) (n : ℕ) : IntS V (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact intS_one
  | succ n ih => rw [pow_succ]; exact intS_mul ih hf

theorem intS_zero : IntS V (0 : MvPowerSeries τ C) := fun μ => by rw [map_zero]; exact VF.Ge.zero 0

theorem intS_X (s : τ) : IntS V (X s : MvPowerSeries τ C) := by
  classical
  intro μ
  rw [coeff_X]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem ge_natCast (k : ℕ) : V.Ge 0 (k : C) := by
  induction k with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ k ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem intS_pderiv {f : MvPowerSeries τ C} (hf : IntS V f) (i : τ) : IntS V (pderiv C i f) := by
  intro μ
  rw [coeff_pderiv]
  exact (hf _).mul_int ((ge_natCast (μ i)).add VF.Ge.one)

theorem intS_subst {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (subst a f) := by
  intro μ
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_induction (fun x => V.Ge 0 x) (VF.Ge.zero 0) (fun x y hx hy => hx.add hy) fun e => ?_
  rw [smul_eq_mul]
  refine (hf e).mul_int ?_
  have hp : IntS V (e.prod fun s m => a s ^ m) := by
    unfold Finsupp.prod
    exact Finset.prod_induction _ (IntS V) (fun _ _ h1 h2 => intS_mul h1 h2) intS_one fun s _ => intS_pow (ha s) _
  exact hp μ

theorem intS_ev {d m n : ℕ} {a : Fin m → Pt C n d} (ha : Z0 a) (hi : ∀ k i, IntS V (a k i)) {f : PS C m d}
    (hf : IntS V f) : IntS V (ev a f) := by
  unfold ev
  exact intS_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) (fun p => hi p.1 p.2) hf

end IntSec

section FBSec

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem toK_self {n : ℕ} (f : PS C n dd) : FB.toK C f = f := by
  unfold FB.toK; rw [show algebraMap C C = RingHom.id C from rfl, map_id]; rfl

theorem FK_self (B : FB C dd O) : B.FK C = B.G.F := by
  funext i; unfold FB.FK FGLaw.mapF; rw [show algebraMap C C = RingHom.id C from rfl, map_id]; rfl

theorem pderiv_expS {n : ℕ} {g : PS C n dd} (hg : constantCoeff g = 0) (q : Fin n × Fin dd) :
    pderiv C q (FB.expS C g) = FB.expS C g * pderiv C q g := by
  unfold FB.expS; rw [Formalism.G.LogCR.pderiv_psubst hg, PowerSeries.derivative_exp]

theorem z0_pt {n : ℕ} (k : Fin n) (i : Fin dd) : constantCoeff (pt C dd k i) = 0 := constantCoeff_X _

theorem constant_zero_first_two_points : Z0 (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) := by
  intro k i; fin_cases k <;> simp [pt]

theorem integral_first_two_points : ∀ k i, IntS V ((![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) k i) := by
  intro k i; fin_cases k
  · exact intS_X _
  · exact intS_X _
  · exact intS_zero

theorem z0_pp {n : ℕ} (k k' : Fin n) : Z0 (![pt C dd k, pt C dd k'] : Fin 2 → Pt C n dd) := by
  intro j i; fin_cases j <;> simp [pt]

theorem z0_p0 {n : ℕ} (P : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0) :
    Z0 (![P, 0] : Fin 2 → Pt C n dd) := by
  intro k i; fin_cases k
  · exact hP i
  · simp

theorem z0_1 {n : ℕ} (P : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0) : Z0 (![P] : Fin 1 → Pt C n dd) := by
  intro k i; fin_cases k; exact hP i

theorem eval_first_two_points_first (j : Fin dd) :
    ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pt C dd 0 j) = pt C dd 0 j := by
  rw [show (pt C (n := 3) dd 0 j) = X ((0 : Fin 3), j) from rfl, ev_X constant_zero_first_two_points]; rfl

theorem eval_first_two_points_middle (j : Fin dd) :
    ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pt C dd 1 j) = pt C dd 1 j := by
  rw [show (pt C (n := 3) dd 1 j) = X ((1 : Fin 3), j) from rfl, ev_X constant_zero_first_two_points]; rfl

theorem eval_first_two_points_last (j : Fin dd) :
    ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pt C dd 2 j) = 0 := by
  rw [show (pt C (n := 3) dd 2 j) = X ((2 : Fin 3), j) from rfl, ev_X constant_zero_first_two_points]; rfl

theorem killE (A : Pt C 3 dd) (A' : Pt C 2 dd) (hA0 : ∀ j, constantCoeff (A j) = 0)
    (hA : ∀ j, ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (A j) = A' j) (f : PS C 2 dd) :
    ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (ev (n := 3) ![A, pt C dd 2] f) =
      ev (n := 2) ![A', 0] f := by
  rw [ev_ev (constant_zero_point_third A hA0) constant_zero_first_two_points]
  congr 1
  funext k j
  fin_cases k
  · exact hA j
  · exact eval_first_two_points_last j
where
  constant_zero_point_third (A : Pt C 3 dd) (hA0 : ∀ j, constantCoeff (A j) = 0) : Z0 (![A, pt C dd 2] : Fin 2 → Pt C 3 dd) := by
    intro k i; fin_cases k
    · exact hA0 i
    · exact z0_pt _ _

theorem pderiv_last_eval_of_independent (A : Pt C 3 dd) (hA0 : ∀ j, constantCoeff (A j) = 0) (i : Fin dd)
    (hA : ∀ j, pderiv C ((2 : Fin 3), i) (A j) = 0) (f : PS C 2 dd) :
    pderiv C ((2 : Fin 3), i) (ev (n := 3) ![A, pt C dd 2] f) = ev (n := 3) ![A, pt C dd 2] (pderiv C ((1 : Fin 2), i) f) := by
  rw [pderiv_eval_pair (killE.constant_zero_point_third A hA0)]
  have e1 : ∑ j, ev (n := 3) ![A, pt C dd 2] (pderiv C ((0 : Fin 2), j) f) *
      pderiv C ((2 : Fin 3), i) ((![A, pt C dd 2] : Fin 2 → Pt C 3 dd) 0 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [show ((![A, pt C dd 2] : Fin 2 → Pt C 3 dd) 0 j) = A j from rfl, hA j, mul_zero]
  rw [e1, zero_add, Finset.sum_eq_single i]
  · rw [show ((![A, pt C dd 2] : Fin 2 → Pt C 3 dd) 1 i) = X ((2 : Fin 3), i) from rfl, pderiv_X_self, mul_one]
  · intro j _ hj
    rw [show ((![A, pt C dd 2] : Fin 2 → Pt C 3 dd) 1 j) = X ((2 : Fin 3), j) from rfl,
      pderiv_X_of_ne (fun h => hj (Prod.mk.inj h).2), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem pderiv_last_eval_first_two (i : Fin dd) (f : PS C 2 dd) : pderiv C ((2 : Fin 3), i) (ev (n := 3) ![pt C dd 0, pt C dd 1] f) = 0 := by
  rw [pderiv_eval_pair (z0_pp 0 1)]
  have e : ∀ k : Fin 2, ∀ j, pderiv C ((2 : Fin 3), i) ((![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 3 dd) k j) = 0 := by
    intro k j; fin_cases k
    · exact pderiv_X_of_ne (by simp)
    · exact pderiv_X_of_ne (by simp)
  simp only [e, mul_zero, Finset.sum_const_zero, add_zero]

theorem ev_sgP (Y : FBChart C V O dd) (v : Fin dd → C) {n : ℕ} (P : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0) :
    ev (n := n) ![P] (Y.sgP v) = -∑ i, MvPowerSeries.C (v i) * ev (n := n) ![P, 0] (pderiv C ((1 : Fin 2), i) Y.h) := by
  have hZ := z0_1 P hP
  have hZ' : Z0 (![pt C dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  unfold FBChart.sgP
  rw [ev_neg hZ, ev_sum hZ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ev_mul hZ, ev_C, ev_ev hZ' hZ]
  congr 2
  funext k j
  fin_cases k
  · exact ev_X hZ 0 j
  · exact ev_zero hZ

theorem h_const (Y : FBChart C V O dd) : constantCoeff Y.h = 0 := by
  have h2 := constantCoeff_ev (z0_p0 (pt C (n := 1) dd 0) (z0_pt 0)) Y.h
  rw [Y.gauge.ax1, map_zero] at h2
  exact h2.symm

theorem const_addOf (Y : FBChart C V O dd) {n : ℕ} (k k' : Fin n) (j : Fin dd) :
    constantCoeff (addOf Y.B.G.F (pt C dd k) (pt C dd k') j) = 0 :=
  const_ev (z0_pp k k') (Y.B.G.const j)

theorem group_law_right_zero (Y : FBChart C V O dd) (j : Fin dd) :
    ev (n := 2) (![pt C dd 1, 0] : Fin 2 → Pt C 2 dd) (Y.B.G.F j) = pt C dd 1 j := by
  have hA : Z0 (![pt C dd 1, 0] : Fin 2 → Pt C 2 dd) := z0_p0 _ (z0_pt 1)
  conv_lhs => rw [← Y.B.G.comm j]
  rw [ev_ev (z0_pp 1 0) hA]
  have e1 : (fun k i => ev (n := 2) (![pt C dd 1, 0] : Fin 2 → Pt C 2 dd)
      ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k i)) = ![0, pt C dd 1] := by
    funext k i; fin_cases k
    · exact ev_X hA 1 i
    · exact ev_X hA 0 i
  rw [e1]
  have hB : Z0 (![pt C dd 1] : Fin 1 → Pt C 2 dd) := z0_1 _ (z0_pt 1)
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k i; fin_cases k
    · simp
    · exact z0_pt 0 i
  have e2 : (![0, pt C dd 1] : Fin 2 → Pt C 2 dd) =
      fun k i => ev (n := 2) (![pt C dd 1] : Fin 1 → Pt C 2 dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k i) := by
    funext k i; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 i).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit j, ev_X hB]
  rfl

end FBSec

end PartialDerivEval

open PartialDerivEval

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem germI_holds (Y : FBChart C V O dd) : GermISt Y := by
  intro v hv
  have hE := constant_zero_first_two_points (C := C) (dd := dd)
  have hF3 : ∀ j, ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd)
      (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) = addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j := by
    intro j
    unfold addOf
    rw [ev_ev (z0_pp 0 1) hE]
    congr 1
    funext k i; fin_cases k
    · exact eval_first_two_points_first i
    · exact eval_first_two_points_middle i
  have hd3 : ∀ i j, pderiv C ((2 : Fin 3), i) (addOf Y.B.G.F (pt C (n := 3) dd 0) (pt C dd 1) j) = 0 :=
    fun i j => pderiv_last_eval_first_two i (Y.B.G.F j)
  have hd0 : ∀ i j, pderiv C ((2 : Fin 3), i) (pt C (n := 3) dd 0 j) = 0 := fun i j => pderiv_X_of_ne (by simp)
  have hd1 : ∀ i j, pderiv C ((2 : Fin 3), i) (pt C (n := 3) dd 1 j) = 0 := fun i j => pderiv_X_of_ne (by simp)
  have hph : Y.B.ph1 = FB.expS C (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) := by
    have := Y.gauge.ph1; rwa [toK_self, FK_self] at this
  have hg : constantCoeff (ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h + ev (n := 3) ![pt C dd 1, pt C dd 2] Y.h -
      ev (n := 3) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), pt C dd 2] Y.h) = 0 := by
    rw [map_sub, map_add, const_ev (killE.constant_zero_point_third _ (z0_pt 0)) (h_const Y),
      const_ev (killE.constant_zero_point_third _ (z0_pt 1)) (h_const Y), const_ev (killE.constant_zero_point_third _ (const_addOf Y 0 1)) (h_const Y)]
    simp
  have hi : ∀ i, ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pderiv C ((2 : Fin 3), i) Y.B.ph1) =
      ev (n := 2) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) Y.h) + ev (n := 2) ![pt C dd 1, 0] (pderiv C ((1 : Fin 2), i) Y.h) -
        ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1), 0] (pderiv C ((1 : Fin 2), i) Y.h) := by
    intro i
    rw [hph, pderiv_expS hg, ← hph, ev_mul hE, Y.B.cocycleLeft_zero_thd, one_mul, map_sub, map_add, ev_sub hE, ev_add hE,
      pderiv_last_eval_of_independent _ (z0_pt 0) i (hd0 i), pderiv_last_eval_of_independent _ (z0_pt 1) i (hd1 i), pderiv_last_eval_of_independent _ (const_addOf Y 0 1) i (hd3 i),
      killE _ _ (z0_pt 0) eval_first_two_points_first, killE _ _ (z0_pt 1) eval_first_two_points_middle, killE _ _ (const_addOf Y 0 1) hF3]
  have key : ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (Y.sgP v) - ev (n := 2) ![pt C dd 0] (Y.sgP v) -
      ev (n := 2) ![pt C dd 1] (Y.sgP v) =
      ∑ i, MvPowerSeries.C (v i) * ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pderiv C ((2 : Fin 3), i) Y.B.ph1) := by
    rw [ev_sgP Y v _ (const_addOf Y 0 1), ev_sgP Y v _ (z0_pt 0), ev_sgP Y v _ (z0_pt 1)]
    simp only [hi, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [key]
  exact intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev hE integral_first_two_points (intS_pderiv Y.intPh1 _))

theorem germII_holds (Y : FBChart C V O dd) : GermIISt Y := by
  intro v hv
  have hE := constant_zero_first_two_points (C := C) (dd := dd)
  have hQ0 : ∀ j, constantCoeff (addOf Y.B.G.F (pt C (n := 3) dd 1) (pt C dd 2) j) = 0 := const_addOf Y 1 2
  have hZQ : Z0 (![pt C dd 0, addOf Y.B.G.F (pt C (n := 3) dd 1) (pt C dd 2)] : Fin 2 → Pt C 3 dd) := by
    intro k i; fin_cases k
    · exact z0_pt 0 i
    · exact hQ0 i
  have hd0 : ∀ i j, pderiv C ((2 : Fin 3), i) (pt C (n := 3) dd 0 j) = 0 := fun i j => pderiv_X_of_ne (by simp)
  have hd1 : ∀ i j, pderiv C ((2 : Fin 3), i) (pt C (n := 3) dd 1 j) = 0 := fun i j => pderiv_X_of_ne (by simp)
  have hph : Y.B.ph2 = FB.expS C (ev (n := 3) ![pt C dd 0, pt C dd 1] Y.h + ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h -
      ev (n := 3) ![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] Y.h) := by
    have := Y.gauge.ph2; rwa [toK_self, FK_self] at this
  have hg : constantCoeff (ev (n := 3) ![pt C dd 0, pt C dd 1] Y.h + ev (n := 3) ![pt C dd 0, pt C dd 2] Y.h -
      ev (n := 3) ![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] Y.h) = 0 := by
    rw [map_sub, map_add, const_ev (z0_pp 0 1) (h_const Y), const_ev (z0_pp 0 2) (h_const Y), const_ev hZQ (h_const Y)]
    simp

  have hdQ : ∀ i, pderiv C ((2 : Fin 3), i) (ev (n := 3) ![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] Y.h) =
      ∑ j, ev (n := 3) ![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] (pderiv C ((1 : Fin 2), j) Y.h) *
        ev (n := 3) ![pt C dd 1, pt C dd 2] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
    intro i
    rw [pderiv_eval_pair hZQ]
    have e1 : ∑ j, ev (n := 3) ![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] (pderiv C ((0 : Fin 2), j) Y.h) *
        pderiv C ((2 : Fin 3), i) ((![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] : Fin 2 → Pt C 3 dd) 0 j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show ((![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] : Fin 2 → Pt C 3 dd) 0 j) = pt C dd 0 j from rfl,
          hd0 i j, mul_zero]
    rw [e1, zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] : Fin 2 → Pt C 3 dd) 1 j) =
      ev (n := 3) ![pt C dd 1, pt C dd 2] (Y.B.G.F j) from rfl, pderiv_last_eval_of_independent _ (z0_pt 1) i (hd1 i)]
  have hEQ : ∀ f : PS C 2 dd, ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd)
      (ev (n := 3) ![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] f) = f := by
    intro f
    rw [ev_ev hZQ hE]
    have e : (fun k i => ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd)
        ((![pt C dd 0, addOf Y.B.G.F (pt C dd 1) (pt C dd 2)] : Fin 2 → Pt C 3 dd) k i)) = ![pt C dd 0, pt C dd 1] := by
      funext k i; fin_cases k
      · exact eval_first_two_points_first i
      · show ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd)
          (ev (n := 3) ![pt C dd 1, pt C dd 2] (Y.B.G.F i)) = pt C dd 1 i
        rw [killE _ _ (z0_pt 1) eval_first_two_points_middle, group_law_right_zero]
    rw [e, eval_points_two]
  have hi : ∀ i, ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pderiv C ((2 : Fin 3), i) Y.B.ph2) =
      ev (n := 2) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) Y.h) -
        ∑ j, pderiv C ((1 : Fin 2), j) Y.h * ev (n := 2) ![pt C dd 1, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) := by
    intro i
    rw [hph, pderiv_expS hg, ← hph, ev_mul hE, Y.B.cocycleRight_zero_thd, one_mul, map_sub, map_add, ev_sub hE, ev_add hE,
      pderiv_last_eval_first_two i Y.h, ev_zero hE, zero_add, pderiv_last_eval_of_independent _ (z0_pt 0) i (hd0 i), killE _ _ (z0_pt 0) eval_first_two_points_first, hdQ i, ev_sum hE]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ev_mul hE, hEQ, killE _ _ (z0_pt 1) eval_first_two_points_middle]
  have key : (∑ j : Fin dd, (∑ i : Fin dd, MvPowerSeries.C (v i) *
        ev (n := 2) ![pt C dd 1, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) * pderiv C ((1 : Fin 2), j) Y.h) +
        ev (n := 2) ![pt C dd 0] (Y.sgP v) =
      -∑ i, MvPowerSeries.C (v i) * ev (n := 2) (![pt C dd 0, pt C dd 1, 0] : Fin 3 → Pt C 2 dd) (pderiv C ((2 : Fin 3), i) Y.B.ph2) := by
    rw [ev_sgP Y v _ (z0_pt 0)]
    simp only [hi, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin dd))) (t := (Finset.univ : Finset (Fin dd)))]
    have e : ∀ i j, MvPowerSeries.C (v i) * ev (n := 2) ![pt C dd 1, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j)) *
        pderiv C ((1 : Fin 2), j) Y.h = MvPowerSeries.C (v i) * (pderiv C ((1 : Fin 2), j) Y.h *
          ev (n := 2) ![pt C dd 1, 0] (pderiv C ((1 : Fin 2), i) (Y.B.G.F j))) := fun i j => by ring
    simp only [e]
    ring
  rw [key]
  exact intS_neg (intS_sum _ fun i _ => intS_C_mul (hv i) (intS_ev hE integral_first_two_points (intS_pderiv Y.intPh2 _)))

end Formalism.L2.FormalSeriesBounds
