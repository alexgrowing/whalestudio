import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAIsAdj

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R
open scoped ComplexConjugate

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

noncomputable section

section loc

variable {r : ℕ} {TT : ℝ}

def IsLoc (X : Module.End ℂ (SmQ r TT)) : Prop :=
  ∀ (u : SmQ r TT) (V : Set (E r)), IsOpen V → (∀ q : Qp r TT, q.1 ∈ V → (u : Qp r TT → ℂ) q = 0) →
    ∀ q : Qp r TT, q.1 ∈ V → ((X u : SmQ r TT) : Qp r TT → ℂ) q = 0

theorem isLoc_add {X Y : Module.End ℂ (SmQ r TT)} (hX : IsLoc X) (hY : IsLoc Y) : IsLoc (X + Y) := by
  intro u V hV hu q hq
  simp [hX u V hV hu q hq, hY u V hV hu q hq]

theorem isLoc_mul {X Y : Module.End ℂ (SmQ r TT)} (hX : IsLoc X) (hY : IsLoc Y) : IsLoc (X * Y) := by
  intro u V hV hu q hq
  exact hX (Y u) V hV (fun q' hq' => hY u V hV hu q' hq') q hq

theorem isLoc_algebraMap (z : ℂ) : IsLoc (algebraMap ℂ (Module.End ℂ (SmQ r TT)) z) := by
  intro u V hV hu q hq
  simp [Module.algebraMap_end_apply, hu q hq]

theorem isLoc_neg {X : Module.End ℂ (SmQ r TT)} (hX : IsLoc X) : IsLoc (-X) := by
  intro u V hV hu q hq
  simp [hX u V hV hu q hq]

theorem isLoc_mulLeft (f : SmQ r TT) : IsLoc (LinearMap.mulLeft ℂ f) := by
  intro u V hV hu q hq
  simp [hu q hq]

theorem isLoc_euler (v : M.Var r) : IsLoc (eulerQ (r := r) (TT := TT) v) := by
  intro u V hV hu q hq
  have h0 : MA.ext (u : Qp r TT → ℂ) =ᶠ[nhds q.1] fun _ => (0 : ℂ) := by
    filter_upwards [(hV.inter (Qset_open r TT)).mem_nhds ⟨hq, q.2⟩] with x hx
    simp only [MA.ext, dif_pos hx.2]
    exact hu ⟨x, hx.2⟩ hx.1
  have hd : fderiv ℝ (MA.ext (u : Qp r TT → ℂ)) q.1 = 0 := by
    rw [h0.fderiv_eq]; exact fderiv_const_apply _
  show coordE v q.1 * wirt v (MA.ext (u : Qp r TT → ℂ)) q.1 = 0
  simp [wirt, hd]

end loc

section LocSub

variable (P : M.Par)

def locSub : Subalgebra ℂ (DQ P).Pr where
  carrier := {a | IsLoc a.1 ∧ IsLoc a.2.unop}
  mul_mem' {a b} ha hb := ⟨isLoc_mul ha.1 hb.1, by
    show IsLoc (a.2 * b.2).unop
    rw [MulOpposite.unop_mul]; exact isLoc_mul hb.2 ha.2⟩
  add_mem' {a b} ha hb := ⟨isLoc_add ha.1 hb.1, by
    show IsLoc (a.2 + b.2).unop
    rw [MulOpposite.unop_add]; exact isLoc_add ha.2 hb.2⟩
  algebraMap_mem' z := ⟨isLoc_algebraMap z, isLoc_algebraMap (conj z)⟩

theorem mem_locSub {a : (DQ P).Pr} : a ∈ locSub P ↔ IsLoc a.1 ∧ IsLoc a.2.unop := Iff.rfl

theorem locSub_star {a : (DQ P).Pr} (ha : a ∈ locSub P) : star a ∈ locSub P := ⟨ha.2, ha.1⟩

theorem gen_loc {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : w ∈ locSub P := by
  simp only [DAlg.gens, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rw [mem_locSub]
  rcases hw with (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals first
    | exact ⟨isLoc_mulLeft _, isLoc_mulLeft _⟩
    | exact ⟨isLoc_euler _, isLoc_neg (isLoc_euler _)⟩
    | exact ⟨isLoc_mul (isLoc_mulLeft _) (isLoc_euler _), isLoc_neg (isLoc_mul (isLoc_mulLeft _) (isLoc_euler _))⟩

abbrev MSl : Subalgebra ℂ (A P (DQ P)) := Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (locSub P) (M.Ty P)

theorem sc_memL {w : (DQ P).Pr} (hw : w ∈ (DQ P).gens P.TT) : sc P (DQ P) w ∈ MSl P :=
  Formalism.FourierDecayAlt.P.MAx2.Jet.scalar_mem _ _ (gen_loc P hw)

theorem star_memL {a : A P (DQ P)} (ha : a ∈ MSl P) : star a ∈ MSl P := fun i j => by
  rw [Matrix.star_apply]; exact locSub_star P (ha j i)

variable {P}

section LvL

variable {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L)
include hL

theorem lvL_p (l : Fin P.r) : L.p l ∈ MSl P := by
  rw [hL.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_pb (l : Fin P.r) : L.pb l ∈ MSl P := by
  rw [hL.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_c (l : Fin P.r) : L.c l ∈ MSl P := by
  rw [hL.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_ci (l : Fin P.r) : L.ci l ∈ MSl P := by
  rw [hL.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_cb (l : Fin P.r) : L.cb l ∈ MSl P := by
  rw [hL.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_cbi (l : Fin P.r) : L.cbi l ∈ MSl P := by
  rw [hL.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem zeta_mem_self_adjoint_levels : L.ζ ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_zi : L.ζi ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_zb : L.ζb ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_zbi : L.ζbi ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_gg : L.GG ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_ggi : L.GGi ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]; exact sc_memL P (by simp [DAlg.gens])
theorem lvL_nab : L.nab ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (gen_loc P (by simp [DAlg.gens]))
    (Subalgebra.smul_mem _ (mul_mem (gen_loc P (by simp [DAlg.gens])) (gen_loc P (by simp [DAlg.gens]))) _)
theorem lvL_nabs : L.nabs ∈ MSl P := by
  rw [hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => add_mem (neg_mem (gen_loc P (by simp [DAlg.gens])))
    (Subalgebra.smul_mem _ (mul_mem (gen_loc P (by simp [DAlg.gens])) (gen_loc P (by simp [DAlg.gens]))) _)

theorem lvL_Dr : L.Dr ∈ MSl P := by
  unfold LevelData.Dr
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lvL_c hL l
theorem lvL_Drb : L.Drb ∈ MSl P := by
  unfold LevelData.Drb
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lvL_cb hL l
theorem lvL_Dri : L.Dri ∈ MSl P := by
  unfold LevelData.Dri
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lvL_ci hL l
theorem lvL_Drbi : L.Drbi ∈ MSl P := by
  unfold LevelData.Drbi
  refine Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx; obtain ⟨l, rfl⟩ := hx; exact lvL_cbi hL l

theorem lvL_Tprod (Y : ℂ) : L.Tprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSl P) (Fin 2) := by
  unfold LevelData.Tprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (Subalgebra.algebraMap_mem _ _) (lvL_p hL l)
  · exact neg_mem (lvL_c hL l)
  · exact lvL_ci hL l
  · exact zero_mem _

theorem lvL_Tvprod (Y : ℂ) : L.Tvprod Y ∈ Formalism.FourierDecayAlt.P.MAx2.Jet.matSub (MSl P) (Fin 2) := by
  unfold LevelData.Tvprod
  refine Subalgebra.list_prod_mem _ fun M hM => ?_
  rw [List.mem_reverse, List.mem_ofFn] at hM
  obtain ⟨l, rfl⟩ := hM
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [LevelData.Tvl, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact sub_mem (Subalgebra.algebraMap_mem _ _) (lvL_pb hL l)
  · exact neg_mem (lvL_cb hL l)
  · exact lvL_cbi hL l
  · exact zero_mem _

theorem lvL_hat {X : A P (DQ P)} (hX : X ∈ hatSet P L) : X ∈ MSl P := by
  have hl0 : ∀ Y, L.l0 Y ∈ MSl P := fun Y => by
    unfold LevelData.l0
    exact sub_mem (neg_mem (lvL_nab hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (lvL_zb hL) (lvL_ggi hL)))
  have hm0 : ∀ Y, L.m0 Y ∈ MSl P := fun Y => by
    unfold LevelData.m0
    exact sub_mem (neg_mem (lvL_nabs hL)) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (zeta_mem_self_adjoint_levels hL) (lvL_ggi hL)))
  rcases hX with ((⟨Y, rfl⟩ | ⟨Y, rfl⟩) | ⟨Y, rfl⟩) | ⟨Y, rfl⟩
  · exact mul_mem (lvL_Dr hL) (lvL_Tprod hL Y 0 0)
  · exact mul_mem (mul_mem (lvL_Drb hL) (lvL_gg hL))
      (add_mem (mul_mem (hl0 Y) (lvL_Tprod hL Y 0 0)) (lvL_Tprod hL Y 1 0))
  · exact mul_mem (lvL_Drb hL) (lvL_Tvprod hL Y 0 0)
  · exact mul_mem (mul_mem (lvL_Dr hL) (lvL_gg hL))
      (add_mem (mul_mem (hm0 Y) (lvL_Tvprod hL Y 0 0)) (lvL_Tvprod hL Y 1 0))

theorem lvL_SS (i : ℕ) : SS P (DQ P) i ∈ MSl P := fun a b => by
  simp only [SS, Matrix.of_apply]
  split_ifs
  · exact Subalgebra.algebraMap_mem _ _
  · exact zero_mem _

theorem lvL_kap (g : M.Ty P → ℂ) : kap P (DQ P) g ∈ MSl P := by
  have : kap P (DQ P) g = Matrix.diagonal fun π => algebraMap ℂ (DQ P).Pr (g π) := rfl
  rw [this]
  exact Formalism.FourierDecayAlt.P.MAx2.Jet.diag_mem _ _ fun π => Subalgebra.algebraMap_mem _ _

theorem lvL_bdd {b : A P (DQ P)} (hb : b ∈ bddSet P L) : b ∈ MSl P := by
  have hD : L.D ∈ MSl P := mul_mem (lvL_Dr hL) (zeta_mem_self_adjoint_levels hL)
  have hDi : L.Di ∈ MSl P := mul_mem (lvL_zi hL) (lvL_Dri hL)
  have hDb : L.Db ∈ MSl P := mul_mem (lvL_Drb hL) (lvL_zb hL)
  have hDbi : L.Dbi ∈ MSl P := mul_mem (lvL_zbi hL) (lvL_Drbi hL)
  have hS : ∀ i, L.Drb * L.Dri * SS P (DQ P) i ∈ MSl P := fun i =>
    mul_mem (mul_mem (lvL_Drb hL) (lvL_Dri hL)) (lvL_SS hL i)
  rcases hb with ((h4 | ⟨g, rfl⟩) | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h4
    rcases h4 with rfl | rfl | rfl | rfl
    · exact lvL_zi hL
    · exact lvL_zbi hL
    · exact mul_mem hD hDbi
    · exact mul_mem hDb hDi
  · exact lvL_kap hL g
  · exact hS i
  · exact star_memL P (hS i)

end LvL

theorem closure_loc {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) {a : A P (DQ P)}
    (ha : a ∈ Submonoid.closure (hatSet P L ∪ bddSet P L)) : ∀ π π', a π π' ∈ locSub P := by
  have hsub : Submonoid.closure (hatSet P L ∪ bddSet P L) ≤ (MSl P).toSubmonoid :=
    Submonoid.closure_le.2 fun x hx => by
      rcases hx with hx | hx
      · exact lvL_hat hL hx
      · exact lvL_bdd hL hx
  exact hsub ha

end LocSub

section cut

variable {r : ℕ} {TT : ℝ}

theorem exists_cutoffR {K : Set (E r)} (hK : IsCompact K) (hKQ : K ⊆ Qset r TT) :
    ∃ (f : E r → ℝ) (V W : Set (E r)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ IsOpen V ∧ K ⊆ V ∧
      (∀ y ∈ V, f y = 1) ∧ IsCompact W ∧ W ⊆ Qset r TT ∧ ∀ y, y ∉ W → f y = 0 := by
  have hρ : ∀ x ∈ K, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x (3 * ρ) ⊆ Qset r TT := fun x hx => by
    obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 (Qset_open r TT) x (hKQ hx)
    exact ⟨ε / 3, by positivity, by rw [show 3 * (ε / 3) = ε by ring]; exact h⟩
  choose! ρ hρpos hρsub using hρ
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (ρ x))
    (fun x hx => Metric.ball_mem_nhds x (hρpos x hx))
  let σ : E r → ℝ := fun x => if 0 < ρ x then ρ x else 1
  have hσ : ∀ x, 0 < σ x := fun x => by
    simp only [σ]; split_ifs with h
    · exact h
    · exact one_pos
  have hσK : ∀ x ∈ K, σ x = ρ x := fun x hx => by simp [σ, hρpos x hx]
  let bb : ∀ x : E r, ContDiffBump x := fun x => ⟨σ x, 2 * σ x, hσ x, by linarith [hσ x]⟩
  refine ⟨fun y => 1 - ∏ x ∈ t, (1 - bb x y), ⋃ x ∈ t, Metric.ball x (σ x),
    ⋃ x ∈ t, Metric.closedBall x (2 * σ x), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (contDiff_prod fun x _ => contDiff_const.sub (bb x).contDiff)
  · exact isOpen_biUnion fun x _ => Metric.isOpen_ball
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
    exact Set.mem_iUnion₂.2 ⟨x, hx, by rw [hσK x (htK x hx)]; exact hyx⟩
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
    have h1 : bb x y = 1 := (bb x).one_of_mem_closedBall (Metric.ball_subset_closedBall hyx)
    show 1 - ∏ x ∈ t, (1 - bb x y) = 1
    rw [Finset.prod_eq_zero hx (show (1 : ℝ) - bb x y = 0 by rw [h1]; ring), sub_zero]
  · exact t.isCompact_biUnion fun x _ => isCompact_closedBall x _
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
    have hxK := htK x hx
    apply hρsub x hxK
    rw [← hσK x hxK]
    exact Metric.closedBall_subset_ball (by linarith [hσ x]) hyx
  · intro y hy
    have h0 : ∀ x ∈ t, bb x y = 0 := fun x hx => by
      have hy' : y ∉ Metric.ball x (2 * σ x) := fun h =>
        hy (Set.mem_iUnion₂.2 ⟨x, hx, Metric.ball_subset_closedBall h⟩)
      have : y ∉ Function.support (bb x) := by
        rw [(bb x).support_eq]; exact hy'
      simpa using this
    show 1 - ∏ x ∈ t, (1 - bb x y) = 0
    rw [Finset.prod_eq_one (fun x hx => show (1 : ℝ) - bb x y = 1 by rw [h0 x hx]; ring), sub_self]

theorem exists_cutoff {K : Set (E r)} (hK : IsCompact K) (hKQ : K ⊆ Qset r TT) :
    ∃ (χ : SmQ r TT) (V : Set (E r)), χ ∈ Test r TT ∧ IsOpen V ∧ K ⊆ V ∧
      ∀ q : Qp r TT, q.1 ∈ V → (χ : Qp r TT → ℂ) q = 1 := by
  obtain ⟨f, V, W, hf, hV, hKV, hf1, hW, hWQ, hf0⟩ := exists_cutoffR hK hKQ
  have hsm : (fun q : Qp r TT => ((f q.1 : ℝ) : ℂ)) ∈ smSub r TT := by
    show ContDiffOn ℝ sm (MA.ext fun q : Qp r TT => ((f q.1 : ℝ) : ℂ)) (Qset r TT)
    exact ((Complex.ofRealCLM.contDiff.comp hf).contDiffOn).congr fun x hx => by
      simp [MA.ext, hx]
  refine ⟨⟨_, hsm⟩, V, ?_, hV, hKV, fun q hq => by simp [hf1 q.1 hq]⟩
  have hsupp : Function.support (MA.ext fun q : Qp r TT => ((f q.1 : ℝ) : ℂ)) ⊆ W := by
    intro x hx
    by_contra hxW
    apply hx
    by_cases hxQ : x ∈ Qset r TT
    · simp [MA.ext, hxQ, hf0 x hxW]
    · simp [MA.ext, hxQ]
  have hts : tsupport (MA.ext fun q : Qp r TT => ((f q.1 : ℝ) : ℂ)) ⊆ W :=
    closure_minimal hsupp hW.isClosed
  exact ⟨IsCompact.of_isClosed_subset hW (isClosed_tsupport _) hts, hts.trans hWQ⟩

end cut

section main

open Formalism.FourierDecayAlt.P.MAx2.Adj

variable {r : ℕ} {TT : ℝ}

theorem inner_product_congr_left {f f' g : SmQ r TT}
    (h : ∀ q, (f : Qp r TT → ℂ) q * conj ((g : Qp r TT → ℂ) q) = (f' : Qp r TT → ℂ) q * conj ((g : Qp r TT → ℂ) q)) :
    MA.ip0 f g = MA.ip0 f' g := by
  unfold MA.ip0; congr 1; funext q; exact h q

theorem loc_eq {X : Module.End ℂ (SmQ r TT)} (hX : IsLoc X) {u u' : SmQ r TT} {V : Set (E r)} (hV : IsOpen V)
    (h : ∀ q : Qp r TT, q.1 ∈ V → (u : Qp r TT → ℂ) q = (u' : Qp r TT → ℂ) q) :
    ∀ q : Qp r TT, q.1 ∈ V → ((X u : SmQ r TT) : Qp r TT → ℂ) q = ((X u' : SmQ r TT) : Qp r TT → ℂ) q := by
  intro q hq
  have := hX (u - u') V hV (fun q' hq' => by simp [h q' hq']) q hq
  rw [map_sub] at this
  simpa [sub_eq_zero] using this

theorem zero_off_tsupport (U : SmQ r TT) (q : Qp r TT) (hq : q.1 ∉ tsupport (MA.ext (U : Qp r TT → ℂ))) :
    (U : Qp r TT → ℂ) q = 0 := by
  have := image_eq_zero_of_notMem_tsupport hq
  simpa [MA.ext, q.2] using this

end main

theorem evQ_sum (P : M.Par) {ι : Type*} (s : Finset ι) (g : ι → (DQ P).R) (q : Qp P.r P.TT) :
    MA.evQ P (∑ i ∈ s, g i) q = ∑ i ∈ s, MA.evQ P (g i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    have e1 : (∑ i ∈ insert a s, g i) = g a + ∑ i ∈ s, g i := Finset.sum_insert ha
    have e2 : MA.evQ P (∑ i ∈ insert a s, g i) q = MA.evQ P (g a + ∑ i ∈ s, g i) q :=
      congrArg (fun x => MA.evQ P x q) e1
    rw [e2, Finset.sum_insert ha, ← ih]
    rfl

theorem model_adjoint_identity_holds : SAModelAdj := by
  intro P L hτ hL a ha u U hU
  have hAdj : ∀ π π', IsAdj (a π π') := Formalism.FourierDecayAlt.P.CutMP.JA.transfer_is_adjoint_holds P L hτ hL a ha
  have hLoc := closure_loc hL ha
  have hK : IsCompact (⋃ π, tsupport (MA.ext (U π : Qp P.r P.TT → ℂ))) := isCompact_iUnion fun π => (hU π).1
  have hKQ : (⋃ π, tsupport (MA.ext (U π : Qp P.r P.TT → ℂ))) ⊆ Qset P.r P.TT :=
    Set.iUnion_subset fun π => (hU π).2
  obtain ⟨χ, V, hχ, hV, hKV, hχ1⟩ := exists_cutoff hK hKQ
  have hUoff : ∀ π (q : Qp P.r P.TT), q.1 ∉ V → (U π : Qp P.r P.TT → ℂ) q = 0 := fun π q hq =>
    zero_off_tsupport (U π) q fun h => hq (hKV (Set.mem_iUnion.2 ⟨π, h⟩))
  have haUoff : ∀ π π' (q : Qp P.r P.TT), q.1 ∉ V → MA.evQ P ((a π π').1 (U π')) q = 0 := by
    intro π π' q hq
    exact (hLoc π π').1 (U π') (tsupport (MA.ext (U π' : Qp P.r P.TT → ℂ)))ᶜ (isClosed_tsupport _).isOpen_compl
      (fun q' hq' => zero_off_tsupport (U π') q' hq') q (fun h => hq (hKV (Set.mem_iUnion.2 ⟨π', h⟩)))
  let ut : M.Ty P → SmQ P.r P.TT := fun π => χ * u π
  have hutT : ∀ π, ut π ∈ Test P.r P.TT := fun π => Formalism.FourierDecayAlt.P.MAx2.Adj.test_mul_right hχ (u π)
  have hutV : ∀ π (q : Qp P.r P.TT), q.1 ∈ V → (ut π : Qp P.r P.TT → ℂ) q = (u π : Qp P.r P.TT → ℂ) q := by
    intro π q hq; simp [ut, hχ1 q hq]
  show ∑ π, MA.ip0 (∑ π', ((star a) π π').1 (u π')) (U π) = ∑ π, MA.ip0 (u π) (∑ π', (a π π').1 (U π'))
  calc ∑ π, MA.ip0 (∑ π', ((star a) π π').1 (u π')) (U π)
      = ∑ π, MA.ip0 (∑ π', (a π' π).2.unop (ut π')) (U π) := by
        refine Finset.sum_congr rfl fun π _ => inner_product_congr_left fun q => ?_
        by_cases hq : q.1 ∈ V
        · have e : MA.evQ P (∑ π', ((star a) π π').1 (u π')) q = MA.evQ P (∑ π', (a π' π).2.unop (ut π')) q := by
            rw [evQ_sum, evQ_sum]
            refine Finset.sum_congr rfl fun π' _ => ?_
            exact loc_eq (hLoc π' π).2 hV (fun q hq => (hutV π' q hq).symm) q hq
          exact congrArg (· * _) e
        · have := hUoff π q hq
          simp [this]
    _ = ∑ π, ∑ π', MA.ip0 ((a π' π).2.unop (ut π')) (U π) :=
        Finset.sum_congr rfl fun π _ =>
          Formalism.FourierDecayAlt.P.MAx2.Adj.inner_sum_left_alt _ _ (fun π' _ => (hAdj π' π).2.1 _ (hutT π')) _
    _ = ∑ π, ∑ π', MA.ip0 (ut π') ((a π' π).1 (U π)) := by
        refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun π' _ => ?_
        have h1 := Formalism.FourierDecayAlt.P.MAx2.Adj.inner_conj_symm_alt ((a π' π).2.unop (ut π')) (U π)
        have h2 := (hAdj π' π).2.2 (U π) (hU π) (ut π') (hutT π')
        have h3 := Formalism.FourierDecayAlt.P.MAx2.Adj.inner_conj_symm_alt (ut π') ((a π' π).1 (U π))
        exact h1.trans ((congrArg (starRingEnd ℂ) h2.symm).trans h3.symm)
    _ = ∑ π', ∑ π, MA.ip0 (ut π') ((a π' π).1 (U π)) := Finset.sum_comm
    _ = ∑ π', MA.ip0 (ut π') (∑ π, (a π' π).1 (U π)) :=
        Finset.sum_congr rfl fun π' _ => (Formalism.FourierDecayAlt.P.MAx2.Adj.inner_sum_right_alt (hutT π') _ _).symm
    _ = ∑ π', MA.ip0 (u π') (∑ π, (a π' π).1 (U π)) := by
        refine Finset.sum_congr rfl fun π' _ => inner_product_congr_left fun q => ?_
        by_cases hq : q.1 ∈ V
        · rw [hutV π' q hq]
        · have : MA.evQ P (∑ π, (a π' π).1 (U π)) q = 0 := by
            rw [evQ_sum]
            exact Finset.sum_eq_zero fun π _ => haUoff π' π q hq
          have e : MA.evQ P (ut π') q * conj (MA.evQ P (∑ π, (a π' π).1 (U π)) q) =
              MA.evQ P (u π') q * conj (MA.evQ P (∑ π, (a π' π).1 (U π)) q) := by
            rw [this]; simp
          exact e

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
