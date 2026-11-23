import Development.WeilBound.ThetaLifts.FrameEstimates.SqAllC
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
import Development.WeilBound.ThetaLifts.FrameEstimates.RankIffRight

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem sq_iff {a P L : ℝ≥0∞} : a ^ 2 ≤ P ^ 2 * L ↔ a ≤ P * L ^ (1 / 2 : ℝ) := by
  have e : L = (L ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  conv_lhs => rw [e, ← mul_pow]
  exact ⟨fun h => (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h, fun h => by gcongr⟩

theorem latSum_mono {τ : ∀ w : InfinitePlace F, EmbOver E w} {C C' : Set (Ten F E n d)} (hC : C ⊆ C') (N : ℕ) (S)
    (g : UA σ X.J) (h : UA σ W.J) : latSum τ C N S g h ≤ latSum τ C' N S g h := by
  refine ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_
  by_cases hx : ∃ c ∈ C, At (evI F) (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ - c)
  · obtain ⟨c, h1, h2⟩ := hx
    unfold maj
    rw [if_pos ⟨c, h1, h2⟩, if_pos ⟨c, hC h1, h2⟩]
  · conv_lhs => unfold maj
    rw [if_neg hx]
    exact sq_maj_nonneg _ _ _ _

variable (B om) in

def Qb (N : ℕ) (Φ : SInf F (Fin n × Fin d) → Fn F n d) : Prop :=
  (∀ f, Φ f ∈ schA F (Fin n × Fin d)) ∧ ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧
    IsCompact C ∧ ∀ f g h, ‖theta om (Φ f) g h‖ₑ ^ 2 ≤ ENNReal.ofReal (p f) ^ 2 * latSum B.emb C N (fullRank E n d) g h

theorem qb_zero (N : ℕ) : Qb B om N fun _ => 0 :=
  ⟨fun _ => zero_mem _, 0, ∅, continuous_const, isCompact_empty, fun f g h => by simp [theta, thetaSum]⟩

theorem Qb.add (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ Ψ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (h2 : Qb B om N Ψ) : Qb B om N fun f => Φ f + Ψ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  obtain ⟨a2, q, C', b2, c2, d2⟩ := h2
  refine ⟨fun f => add_mem (a1 f) (a2 f), p + q, C ∪ C', (b1.add b2 : Continuous fun f => p f + q f), c1.union c2,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 ((d1 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_left N _ g h) _))
  have e2 := sq_iff.1 ((d2 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_right N _ g h) _))
  rw [theta_add hp (a1 f) (a2 f), Seminorm.add_apply, ENNReal.ofReal_add (apply_nonneg p f) (apply_nonneg q f), add_mul]
  exact (enorm_add_le _ _).trans (add_le_add e1 e2)

theorem Qb.smul (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (c : ℂ) : Qb B om N fun f => c • Φ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  refine ⟨fun f => Submodule.smul_mem _ _ (a1 f), ‖c‖₊ • p, C, (continuous_const.mul b1 : Continuous fun f => ‖c‖ * p f), c1,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 (d1 f g h)
  rw [theta_smul hp c (a1 f), enorm_mul, show (‖c‖₊ • p) f = ‖c‖ * p f from rfl, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, mul_assoc]
  exact mul_le_mul_right e1 _

theorem qb_sum (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {ι : Type} (S : Finset ι)
    {Φ : ι → SInf F (Fin n × Fin d) → Fn F n d} (h : ∀ i, Qb B om N (Φ i)) : Qb B om N fun f => ∑ i ∈ S, Φ i f := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using qb_zero N
  | insert a S ha ih => simpa [Finset.sum_insert ha] using (h a).add hp ih

theorem thetaSum_neg {κ : Type} (Φ : (κ → AF F) → ℂ) : thetaSum F (fun x => Φ (-x)) = thetaSum F Φ := by
  unfold thetaSum
  rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun ξ => congrArg Φ (funext fun i => ?_)
  simp

theorem theta_neg (hP : Parity) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g h) :
    theta om (fun x => Φ (-x)) g h = theta om Φ g h := by
  obtain ⟨e, c, he, hc, h1⟩ := hP F E σ B n d X W M χX χW om r s r' s' hp
  have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h) Φ hΦ
  have hcomm : g * e = e * g := Subtype.ext (Units.ext (by
    change mat g * mat e = mat e * mat g
    rw [he]; simp))
  have e1 : om (g, h) (om (e, 1) Φ) = om (e, 1) (om (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, hcomm, mul_one,
      one_mul]
  rw [h1 Φ hΦ, h1 _ hs, map_smul] at e1
  unfold theta
  rw [smul_right_injective _ hc0 e1, thetaSum_neg]

set_option maxHeartbeats 800000 in
open scoped Classical in

theorem qb_piece (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) (hp : IsPair B M χX χW om r s r' s') (N : ℕ)
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB _)
    (h0 : ∀ (f : SInf F (Fin n × Fin d)) (μ : Measure (Fin n × Fin d → AF F)), μ.IsAddHaarMeasure → ∀ z : Ten F E n d,
      (z.map (piW (B.τ₁.comp σ))).rank ≠ n → coef F B.ψ μ (pureA F f φ) (fun x => pureA F f φ (-x)) (M.co.e z) = 0) :
    Qb B om N fun f => pureA F f φ := by
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  have hφ' : (fun y => φ (-y)) ∈ SB (Fin n × Fin d → Af F) :=
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ _ hφ' N
  let P : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)
  have hPf : ∀ f : SInf F (Fin n × Fin d), (fun x => pureA F f φ (-x)) = pureA F (P f) fun y => φ (-y) := fun f => by
    funext x
    unfold pureA
    congr 1
    exact congrArg f (funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1)
  let q : Seminorm ℂ (SInf F (Fin n × Fin d)) := p + p.comp P.toLinearMap
  have hq : Continuous q := (hpc.add (hpc.comp P.continuous) : Continuous fun f => p f + p (P f))
  refine ⟨fun f => pureA_mem f hφ, NNReal.mk √c (Real.sqrt_nonneg c) • q, C,
    (continuous_const.mul hq : Continuous fun f => √c * q f), hC, fun f g h => ?_⟩
  have hm := pureA_mem f hφ
  have e := h1 _ hm _ (ParityOfCoefficients.neg_mem_schA hm) g h
  rw [theta_neg hP hp hm] at e
  refine sq_le_of_coef hc (apply_nonneg q f) e (fun x hx => h0 f μ hμ _ fun hr => hx ?_) fun x => ?_
  · rw [Matrix.map_mul, Matrix.map_mul, ThKEst.W.incM_piW] at hr
    have hr2 := ThKEst.W.rank_of_mul _ _ _ hr
    exact ThKEst.W.rank_of_map (B.τ₁.comp σ).toRingHom x hr2
  · rw [hPf]
    refine (h2 f (P f) _).trans (mul_le_mul_of_nonneg_right ?_ (sq_maj_nonneg _ _ _ _))
    have a1 := apply_nonneg p f
    have a2 := apply_nonneg p (P f)
    change p f * p (P f) ≤ (p f + p (P f)) * (p f + p (P f))
    nlinarith

end

theorem sqSo_of' (hF : SoFin) (hC : SoCut) (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqSo := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨m, c, χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.2 φ hφ
  have key : Qb B om N fun f => ∑ i, c i • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i) := qb_sum hp _ fun i => Qb.smul hp (c := c i) <| by
    obtain ⟨k, ξ, e1, hξ⟩ := hC F E σ B n d X W M χX χW om r s r' s' hp _ (hχ i).2.2
    have hstd : ∀ᶠ u in cofinite, χ i u = ThKEst.W.stdF _ u := ((hχ i).2.1.and hp.good.std).mono fun v hv => hv.1.trans hv.2
    have hg : ThKEst.W.Good (χ i) := ⟨(hχ i).1, hstd⟩
    have e2 : (fun f : SInf F (Fin n × Fin d) => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i)) =
        fun f : SInf F (Fin n × Fin d) => ∑ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) := funext fun f => by
      conv_lhs => rw [← Function.update_eq_self B.v₁ (χ i), ThKEst.W.pure_update (v := B.v₁) f hstd, e1]
      have e3 : ∀ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) =
          tens (evFin F B.v₁) (ξ j) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update (χ i) B.v₁ 1)) := fun j =>
        ThKEst.W.pure_update (v := B.v₁) f hstd (ξ j)
      rw [Finset.sum_congr rfl fun j _ => e3 j]
      funext x
      rw [Finset.sum_apply]
      unfold tens
      rw [Finset.sum_apply, Finset.sum_mul]
    rw [e2]
    refine qb_sum hp _ fun j => qb_piece hP hS hE hB hp N (ThKEst.W.pf_mem (hg.update (hξ j).1.1)) fun f μ hμ z hz => ?_
    rw [← ThKEst.W.pure_eq, ThKEst.W.pure_update (v := B.v₁) f hstd]
    refine (hξ j).2 _ ⟨fun x z hz => ?_, ?_⟩ μ hμ z hz
    · have h1 := (ThKEst.W.at_iff (v := B.v₁) z).1 hz
      have h2 : z = fun i => GlobalTheory.EmbChart.atPlace B.v₁ (evFin F B.v₁ (z i)) := funext fun i =>
        (congrFun h1 i).symm.trans (ThKEst.W.ep_mul (v := B.v₁) (z i))
      rw [h2]
      exact ThKEst.W.indep_pure (v := B.v₁) f (χ i) x _
    · rw [← ThKEst.W.pure_update (v := B.v₁) f hstd]
      exact ThKEst.W.pure_mem f (hg.update (hξ j).1.1)
  obtain ⟨-, p, C, h1, h2, h3⟩ := key
  exact ⟨p, C, h1, h2, fun f g h => by rw [e f]; exact h3 f g h⟩

end PositivityTheory.ThKEst

end
