import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.RhoLoc
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic
import GroundTheory.GlobalFields.LocalFieldAtPlace

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

section SlopeTestRemainingChoices

open UpperTheory.ConvolutionTheory GlobalTheory.LFun Formalism.UG

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem kgl_eq (w : Pl K) : GLnLocal.integralGL (w.adicCompletion K) n = KGL w n := by
  have h : ∀ O : Subring (w.adicCompletion K), O = (ValuativeRel.valuation (w.adicCompletion K)).integer →
      GLnLocal.integralGL (w.adicCompletion K) n = GLint (Fin n) O := by
    rintro _ rfl
    rfl
  exact h _ (Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm)

private theorem diagJ_mul {L : Type} [Field L] (a b : L) (j : ℕ) : diagJ n a j * diagJ n b j = diagJ n (a * b) j := by
  rw [diagJ, diagJ, diagJ, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

private theorem diagJ_one {L : Type} [Field L] (j : ℕ) : diagJ n (1 : L) j = 1 := by
  simp [diagJ]

private theorem exists_unit (w : Pl K) {u : w.adicCompletion K} (hu : Valued.v u = 1) (j : ℕ) :
    ∃ k ∈ KGL w n, (k : Matrix (Fin n) (Fin n) (w.adicCompletion K)) = diagJ n u j := by
  have h0 : u ≠ 0 := by rintro rfl; simp at hu
  have hm : ∀ x : w.adicCompletion K, Valued.v x = 1 → ∀ a b,
      diagJ n x j a b ∈ (ValuativeRel.valuation (w.adicCompletion K)).integer := fun x hx a b => by
    rw [diagJ, Matrix.diagonal_apply]
    split_ifs
    · exact (GroundTheory.Global.mem_valuationInteger_iff w x).2 hx.le
    · exact one_mem _
    · exact zero_mem _
  refine ⟨⟨diagJ n u j, diagJ n u⁻¹ j, by rw [diagJ_mul, mul_inv_cancel₀ h0, diagJ_one],
    by rw [diagJ_mul, inv_mul_cancel₀ h0, diagJ_one]⟩, ?_, rfl⟩
  rw [← kgl_eq]
  exact (GLnLocal.mem_integralGL_iff _ n).2 ⟨hm u hu, hm u⁻¹ (by rw [map_inv₀, hu, inv_one])⟩

private theorem tj_eq (w : Pl K) {ϖ ϖ₀ : w.adicCompletion K} (h : IsUnifV K w ϖ) (h₀ : IsUnifV K w ϖ₀) (j : ℕ)
    (x : GL (Fin n) (w.adicCompletion K)) (hx : (x : Matrix (Fin n) (Fin n) (w.adicCompletion K)) = diagJ n ϖ₀ j) :
    Tj ℂ n (Ov K w) ϖ j = dosetInd ℂ (KGL w n) x := by
  have h0 : ϖ₀ ≠ 0 := fun e => by simp [IsUnifV, e] at h₀
  obtain ⟨k, hk, hk'⟩ := exists_unit (n := n) w (u := ϖ₀⁻¹ * ϖ) (by
    rw [map_mul, map_inv₀, h, h₀]; exact inv_mul_cancel₀ WithZero.coe_ne_zero) j
  have e : diagJ n ϖ j = ((x * k : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)) := by
    rw [Units.val_mul, hx, hk', diagJ_mul, mul_inv_cancel_left₀ h0]
  unfold Tj dosetInd
  congr 1
  ext g
  rw [DoubleCoset.mem_doubleCoset, Set.mem_setOf_eq, e]
  constructor
  · rintro ⟨a, ha, b, hb, hg⟩
    refine ⟨a, ha, k * b, mul_mem hk hb, Units.ext ?_⟩
    rw [hg]; simp only [Units.val_mul, mul_assoc]
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, k⁻¹ * b, mul_mem (inv_mem hk) hb, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group

private theorem out_mem_iff {G : Type} [Group G] (J : Subgroup G) (x : G) (c : G ⧸ J) :
    c.out ∈ DoubleCoset.doubleCoset x (J : Set G) J ↔ ∃ k ∈ J, c = QuotientGroup.mk (k * x) := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    exact ⟨a, ha, by rw [← c.out_eq', e]; exact QuotientGroup.mk_mul_of_mem _ hb⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul J (k * x)
    exact ⟨k, hk, b, b.2, hb⟩

variable (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)

private theorem hop_apply (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
    (hJ : IsCommensurated J) {v : LL μ} (hv : v ∈ fixL μ w J) :
    Hop μ w J x v = heckeVec (localRepresentationL2 μ w) J (dosetInd ℂ J x) v := by
  classical
  have hp : prj (fixL μ w J) v = v :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hv)
  have hS : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets (f := dosetInd ℂ J x) hJ ⟨{x}, fun g hg => ?_⟩).subset fun c hc => ?_
    · obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 (Set.mem_of_indicator_ne_zero hg)
      exact ⟨x, Finset.mem_singleton_self x, ⟨a, ha⟩, ⟨b, hb⟩, e⟩
    · simp [dosetInd, (out_mem_iff J x c).2 hc]
  rw [Hop, ContinuousLinearMap.comp_apply, hp, finsum_mem_eq_finite_toFinset_sum _ hS,
    ContinuousLinearMap.sum_apply, ← finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_def, heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : ∃ k ∈ J, c = QuotientGroup.mk (k * x)
  · rw [Set.indicator_of_mem (by exact hc), dosetInd, Set.indicator_of_mem ((out_mem_iff J x c).2 hc), rhoLoc]
    simp
  · rw [Set.indicator_of_notMem (by exact hc), dosetInd, Set.indicator_of_notMem (mt (out_mem_iff J x c).1 hc),
      zero_smul]

private theorem mem_fixL (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (v : LL μ) :
    v ∈ fixL μ w J ↔ ∀ k ∈ J, localRepresentationL2 μ w k v = v := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
  constructor
  · intro h k hk
    rw [← rhoLoc]
    exact h _ ⟨k, hk, rfl⟩
  · rintro h _ ⟨k, hk, rfl⟩
    exact (rhoLoc K n μ w k v).trans (h k hk)

private theorem scal (B : Multiset ℂˣ) (i : Fin n) (y v : LL μ) :
    (((Ideal.absNorm w.asIdeal : ℝ) ^ (-((((i : ℕ) + 1) * (n - ((i : ℕ) + 1)) : ℕ) : ℝ) / 2) : ℝ) : ℂ) • y =
      (B.map fun b : ℂˣ => (b : ℂ)).esymm (i + 1) • v ↔ y = satEig (qV K w) n B (i + 1) • v := by
  have hq : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (qV_ne_zero w))
  have he : (qV K w : ℂ) ^ (((((i : ℕ) + 1 : ℕ) : ℂ) * ((n : ℂ) - (((i : ℕ) + 1 : ℕ) : ℂ))) / 2) =
      ((((Ideal.absNorm w.asIdeal : ℝ) ^ (-((((i : ℕ) + 1) * (n - ((i : ℕ) + 1)) : ℕ) : ℝ) / 2) : ℝ) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.rpow_neg hq.le, Complex.ofReal_cpow hq.le, qV]
    congr 1
    push_cast [Nat.cast_sub (Nat.succ_le_of_lt i.2)]
    ring
  rw [satEig, he, mul_smul, eq_inv_smul_iff₀ (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne')]

private theorem tsph_iff {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) (B : Multiset ℂˣ) (v : V)
    (hv : (v : LL μ) ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n)) {ϖ : w.adicCompletion K}
    (h : IsUnifV K w ϖ) (i : Fin n) :
    Tsph μ w i v = (B.map fun b : ℂˣ => (b : ℂ)).esymm (i + 1) • (v : LL μ) ↔
      heckeVec (locOn hV w) (KGL w n) (Tj ℂ n (Ov K w) ϖ (i + 1)) v = satEig (qV K w) n B (i + 1) • v := by
  have e := map_heckeVec (ρ := locOn hV w) (ρ' := localRepresentationL2 μ w) (Final.GLintComm K w n) (Tj_mem_hecke h (i + 1))
    V.subtype (fun _ _ => rfl) v
  have ht := tj_eq w h (GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w) (i + 1)
    (Cartan.diagPow (w.adicCompletion K) n fun a => if a ≤ i then 1 else 0) (by
      rw [Cartan.coe_diagPow, diagJ]
      congr 1
      funext a
      by_cases ha : a ≤ i
      · rw [if_pos ha, if_pos (Nat.lt_succ_of_le ha), zpow_one]
      · rw [if_neg ha, if_neg (fun h' => ha (Nat.le_of_lt_succ h')), zpow_zero])
  rw [kgl_eq] at hv
  rw [Tsph, ContinuousLinearMap.smul_apply, scal, kgl_eq, hop_apply μ w _ _ (Final.GLintComm K w n) hv, ← ht]
  exact ⟨fun h' => Subtype.ext (e.trans h'), fun h' => e.symm.trans (congrArg Subtype.val h')⟩

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Dp.tsphVec :
    UpperTheory.ConvolutionTheory.Dp.TsphVec := by
  intro K _ _ n μ _ w V hV B
  have hf : ∀ v : V, v ∈ GlobalTheory.PRep.fixed (locOn hV w) (GlobalTheory.LFun.KGL w n) ↔
      (v : LL μ) ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := fun v => by
    rw [GlobalTheory.LGrp.mem_fixed, mem_fixL, kgl_eq]
    exact forall₂_congr fun k _ => Subtype.ext_iff
  obtain ⟨ϖ₀, h₀⟩ := GlobalTheory.LFun.exists_isUnifV w
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_vec
    refine ⟨by rw [Multiset.card_map, h.card], (Submodule.ne_bot_iff _).2
      ⟨x, ⟨x.2, (hf x).1 hx.2.1⟩, fun e => hx.1 (Subtype.ext e)⟩, fun i v hv => ?_⟩
    by_cases h0 : v = 0
    · simp [h0]
    · exact (tsph_iff μ w hV B ⟨v, hv.1⟩ hv.2 h₀ i).2
        ((h.2 ⟨v, hv.1⟩ ((hf _).2 hv.2) fun e => h0 (congrArg Subtype.val e)).2.2.2 ϖ₀ h₀ _ i.2)
  · rintro ⟨hc, hne, h⟩
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine ⟨(Submodule.ne_bot_iff _).2 ⟨⟨v, hv.1⟩, (hf _).2 hv.2, fun e => h0 (congrArg Subtype.val e)⟩,
      fun x hx hx0 => ⟨hx0, hx, by rwa [Multiset.card_map] at hc, fun ϖ hϖ j hj => ?_⟩⟩
    rcases j with _ | j
    · rw [tj_eq w hϖ hϖ 0 1 (by simp [Formalism.UG.diagJ]),
        GlobalTheory.LFun.heckeVec_dosetInd (R := {1}) hx (by simpa using DoubleCoset.mem_doubleCoset_self _ _ _) ?_]
      · simp [GlobalTheory.LFun.satEig, Multiset.esymm]
      · intro g hg
        obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
        exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using mul_mem ha hb⟩,
          fun y hy => Finset.mem_singleton.1 hy.1⟩
    · exact (tsph_iff μ w hV B x ((hf x).1 hx) hϖ ⟨j, hj⟩).1 (h ⟨j, hj⟩ x ⟨x.2, (hf x).1 hx⟩)
