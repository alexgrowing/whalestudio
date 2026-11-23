import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleWordMemBoundedLetterLists

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section
open Classical

theorem integrable_decay3 : Integrable (fun c : ℂ => ((1 + ‖c‖) ^ 3)⁻¹) := by
  have hi : Integrable (fun c : ℂ => (1 + ‖c‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine hi.congr (Eventually.of_forall fun c => ?_)
  simp only
  rw [Real.rpow_neg (by positivity)]
  norm_cast

section limB

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem ae_coords_ne (S : C.HidaSetting E Wp Wq) : ∀ᵐ c : J.CV E, ∀ v, c (S.pl v) ≠ 0 := by
  have hnull : volume (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S ⁻¹' (⋃ v, {y : Fin S.f → ℂ | y v = 0})) = 0 := by
    rw [(Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).measure_preimage (MeasurableSet.iUnion fun v =>
      measurableSet_eq_fun (measurable_pi_apply v) measurable_const).nullMeasurableSet]
    exact measure_iUnion_null fun v => Measure.pi_hyperplane _ v 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with c hc
  intro v hv
  exact hc (Set.mem_preimage.mpr (Set.mem_iUnion.mpr ⟨v, by simp [Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply, hv]⟩))

theorem continuous_coord (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Continuous fun c : J.CV E => c (S.pl v) :=
  (EuclideanSpace.proj (𝕜 := ℂ) (S.pl v)).continuous

theorem continuous_psiInf (S : C.HidaSetting E Wp Wq) (l : E) : Continuous fun c : J.CV E => S.psiInf l c := by
  have : (fun c : J.CV E => S.psiInf l c) = fun c => ∏ v, KB.psiL S (S.σ v l) (c (S.pl v)) :=
    funext fun c => psiInf_eq_prod S l c
  rw [this]
  exact continuous_finsetProd _ fun v _ => (continuous_psiL S _).comp (continuous_coord S v)

theorem norm_psiInf (S : C.HidaSetting E Wp Wq) (l : E) (c : J.CV E) : ‖S.psiInf l c‖ = 1 := by
  rw [psiInf_eq_prod, norm_prod]
  simp [norm_psiL]

theorem aestronglyMeasurable_level_norm (S : C.HidaSetting E Wp Wq) (hInt : KB.IntAll S) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i)
    (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E)) (hY : ∀ h ∈ Y, TB.level h = i - 1)
    (κ : TB.Pt E → TB.Pt E → ℂ) : AEStronglyMeasurable (S.N1 ε i w.1 Y κ) volume := by
  have H : ∀ (v : Fin S.f) (h h' : Y), ∃ φ : ℂ → ℂ, Continuous φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])) := by
    intro v h h'
    obtain ⟨φ, hc, he, -, -⟩ := hInt v ε hε i hi1 hi2 w (C.loc (S.σ v) h) (C.loc (S.σ v) h')
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
    exact ⟨φ, hc, he⟩
  choose φ hφc hφe using H
  set Φ : J.CV E → ℂ := fun c =>
    (∑ h : Y, ∑ h' : Y, κ h h' * ∏ v, φ v h h' (c (S.pl v))) / (C.Word.size S.P w.1 : ℂ) with hΦ
  have hΦc : Continuous Φ := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun h _ => continuous_finsetSum _ fun h' _ =>
      continuous_const.mul (continuous_finsetProd _ fun v _ => (hφc v h h').comp (continuous_coord S v))
  refine hΦc.aestronglyMeasurable.congr ?_
  filter_upwards [ae_coords_ne S] with c hc
  simp only [hΦ, C.HidaSetting.N1]
  congr 1
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun h' _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hφe v h h' _ (hc v)]

end limB

section limB2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gram_withRR (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (ε : ℝ) (k : ℕ) (w : C.Word S.f) (h h' : TB.Pt E) :
    (KB.withRR S RR).gram ε k w h h' = if k ≤ S.G.r + 1 then
      ∏ v, (KB.withRR S RR).gramLoc v ε k (w v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') else 0 := rfl

theorem level_norm_of_regularization_eq (S : C.HidaSetting E Wp Wq) (RR : Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
    (ε : ℝ) (i : ℕ) (w : C.Word S.f) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ) (c : J.CV E) :
    (KB.withRR S RR).N1 ε i w Y κ c = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, (KB.withRR S RR).gramLoc v ε i (w v)
      (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
        (C.Word.size S.P w : ℂ) := rfl

variable (S : C.HidaSetting E Wp Wq) (RR : ℕ → Fin S.f → ℝ → ℕ → List C.Letter → C.LPt → C.LPt → ℂ)
  (hconv : ∀ v ε, 0 < ε → ∀ i a, D.AdmAt S v a → ∀ p q,
    Tendsto (fun n => RR n v ε i a p q) atTop (𝓝 ((S.pd v).RR ε i a p q)))

include hconv

theorem tendsto_gramLoc' (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (a : List C.Letter) (ha : D.AdmAt S v a)
    (p q : C.LPt) :
    Tendsto (fun n => ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G p) * √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G q) : ℝ) : ℂ) *
      RR n v ε i a p q) atTop (𝓝 (S.gramLoc v ε i a p q)) :=
  (hconv v ε hε i a ha p q).const_mul _

theorem tendsto_gram (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : k ≤ S.G.r + 1) (w' : S.W) (h h' : TB.Pt E) :
    Tendsto (fun n => (KB.withRR S (RR n)).gram ε k w'.1 h h') atTop (𝓝 (S.gram ε k w'.1 h h')) := by
  have e1 : (fun n => (KB.withRR S (RR n)).gram ε k w'.1 h h') = fun n =>
      ∏ v : Fin S.f, ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h)) *
        √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h')) : ℝ) : ℂ) *
          RR n v ε k (w'.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') :=
    funext fun n => by rw [gram_withRR, if_pos hk]; rfl
  have e2 : S.gram ε k w'.1 h h' = ∏ v, S.gramLoc v ε k (w'.1 v) (C.loc (S.σ v) h) (C.loc (S.σ v) h') := by
    simp only [C.HidaSetting.gram, if_pos hk]
  rw [e1, e2]
  exact tendsto_finsetProd _ fun v _ => tendsto_gramLoc' S RR hconv v ε hε k (w'.1 v) ⟨w', rfl⟩ _ _

theorem tendsto_base_norm_of_regularization (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : k ≤ S.G.r + 1) (w' : S.W) (Y : Finset (TB.Pt E))
    (κ : TB.Pt E → TB.Pt E → ℂ) :
    Tendsto (fun n => (KB.withRR S (RR n)).base.N0 ε k w' Y κ) atTop (𝓝 (S.base.N0 ε k w' Y κ)) := by
  have e : ∀ n, (KB.withRR S (RR n)).base.N0 ε k w' Y κ =
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * (KB.withRR S (RR n)).gram ε k w'.1 h h').re / C.Word.size S.P w'.1 :=
    fun n => rfl
  simp only [e]
  show Tendsto _ atTop (𝓝 ((∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * S.gram ε k w'.1 h h').re / C.Word.size S.P w'.1))
  exact ((Complex.continuous_re.tendsto _).comp (tendsto_finsetSum _ fun h _ => tendsto_finsetSum _
    fun h' _ => tendsto_const_nhds.mul (tendsto_gram S RR hconv ε hε k hk w' h h'))).div_const _

theorem tendsto_level_norm_of_regularization (ε : ℝ) (hε : 0 < ε) (i : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (c : J.CV E) :
    Tendsto (fun n => (KB.withRR S (RR n)).N1 ε i w.1 Y κ c) atTop (𝓝 (S.N1 ε i w.1 Y κ c)) := by
  have e1 : (fun n => (KB.withRR S (RR n)).N1 ε i w.1 Y κ c) = fun n =>
      (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v : Fin S.f,
        ((√(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h ++ [(1, c (S.pl v))])) *
          √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) : ℝ) : ℂ) *
          RR n v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
          (C.Word.size S.P w.1 : ℂ) := funext fun n => rfl
  have e2 : S.N1 ε i w.1 Y κ c = (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v)
        (C.loc (S.σ v) h ++ [(1, c (S.pl v))]) (C.loc (S.σ v) h' ++ [(1, c (S.pl v))])) /
          (C.Word.size S.P w.1 : ℂ) := rfl
  rw [e1, e2]
  exact (tendsto_finsetSum _ fun h _ => tendsto_finsetSum _ fun h' _ => tendsto_const_nhds.mul
    (tendsto_finsetProd _ fun v _ => tendsto_gramLoc' S RR hconv v ε hε i (w.1 v) ⟨w, rfl⟩ _ _)).div_const _

theorem tendsto_Nhat (hInt : ∀ n, KB.IntAll (KB.withRR S (RR n)))
    (hbd : ∀ v ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a → ∀ h h', D.ptSize h = i - 1 →
      D.ptSize h' = i - 1 → ∃ C : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
        ‖(KB.withRR S (RR n)).gramLoc v ε i a (h ++ [(1, c)]) (h' ++ [(1, c)])‖ ≤ C * ((1 + ‖c‖) ^ 3)⁻¹)
    (ε : ℝ) (hε : 0 < ε) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ S.G.r + 1) (w : S.W) (Y : Finset (TB.Pt E))
    (hY : ∀ h ∈ Y, TB.level h = i - 1) (κ : TB.Pt E → TB.Pt E → ℂ) (l : E) :
    Tendsto (fun n => (KB.withRR S (RR n)).Nhat ε i w.1 Y κ l) atTop (𝓝 (S.Nhat ε i w.1 Y κ l)) := by
  have e : ∀ n, (KB.withRR S (RR n)).Nhat ε i w.1 Y κ l =
      ((ZLattice.covolume (J.eLat E (S6.perLat E S.g (S6.nuBlock S.G.r i 1) 1) 1) : ℝ) : ℂ)⁻¹ *
        ∫ c : J.CV E, (KB.withRR S (RR n)).N1 ε i w.1 Y κ c * S.psiInf l c := fun n => rfl
  simp only [e]
  unfold C.HidaSetting.Nhat
  refine Tendsto.const_mul _ ?_
  have hB : ∀ v (h h' : Y), ∃ Cc : ℝ, ∀ n, ∀ c : ℂ, c ≠ 0 →
      ‖(KB.withRR S (RR n)).gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(1, c)])
        (C.loc (S.σ v) h' ++ [(1, c)])‖ ≤ Cc * ((1 + ‖c‖) ^ 3)⁻¹ :=
    fun v h h' => hbd v ε hε i hi1 hi2 (w.1 v) ⟨w, rfl⟩ _ _
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h h.2)
      (by rw [Formalism.FourierDecayAlt.P.JCx1.needs.ptSize_loc]; exact hY h' h'.2)
  choose Cb hCb using hB
  set sz : ℂ := (C.Word.size S.P w.1 : ℂ) with hsz
  let g : (Fin S.f → ℂ) → ℝ := fun y =>
    (∑ h : Y, ∑ h' : Y, ‖κ h h'‖ * ∏ v, (Cb v h h' * ((1 + ‖y v‖) ^ 3)⁻¹)) / ‖sz‖
  have hgi : Integrable g := by
    refine Integrable.div_const (integrable_finsetSum _ fun h _ => integrable_finsetSum _ fun h' _ =>
      Integrable.const_mul (Integrable.fintype_prod (f := fun v c => Cb v h h' * ((1 + ‖c‖) ^ 3)⁻¹)
        fun v => integrable_decay3.const_mul _) _) _
  have hbi : Integrable (fun c : J.CV E => g (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c)) :=
    (Formalism.FourierDecayAlt.P.JCx1.needs.Qm_mp S).integrable_comp_of_integrable hgi
  refine tendsto_integral_of_dominated_convergence (fun c => g (Formalism.FourierDecayAlt.P.JCx1.needs.Qm S c)) (fun n => ?_) hbi
    (fun n => ?_) ?_
  · exact (aestronglyMeasurable_level_norm (KB.withRR S (RR n)) (hInt n) ε hε i hi1 hi2 w Y hY κ).mul
      (continuous_psiInf S l).aestronglyMeasurable
  · filter_upwards [ae_coords_ne S] with c hc
    rw [norm_mul, norm_psiInf, mul_one, level_norm_of_regularization_eq, norm_div]
    simp only [g, Formalism.FourierDecayAlt.P.JCx1.needs.Qm_apply]
    refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
    rw [← Finset.sum_coe_sort Y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ => ?_)
    rw [← Finset.sum_coe_sort Y]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' _ => ?_)
    rw [norm_mul, norm_prod]
    exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun v _ => norm_nonneg _)
      fun v _ => hCb v h h' _ _ (hc v)) (norm_nonneg _)
  · exact Eventually.of_forall fun c => (tendsto_level_norm_of_regularization S RR hconv ε hε i w Y κ c).mul_const _

end limB2

end

end Formalism.FourierDecayAlt.P.PBB
