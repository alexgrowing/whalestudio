import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelIntegrandAestronglyMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra

open MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section B

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

def levelProduct (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (i : ℕ) :
    SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π')) :=
  if h : i < r then levelProduct L w (i + 1) * bTl L ⟨i, h⟩ w else 1
termination_by r - i

theorem level_product_of_lt (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (i : ℕ) (h : i < r) :
    levelProduct L w i = levelProduct L w (i + 1) * bTl L ⟨i, h⟩ w := by
  rw [levelProduct, dif_pos h]

theorem level_product_of_ge (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (i : ℕ) (h : r ≤ i) :
    levelProduct L w i = 1 := by
  rw [levelProduct, dif_neg (by omega)]

theorem level_product_eq_list_prod (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (n : ℕ) :
    ∀ i, r - i = n → i ≤ r →
    levelProduct L w i = ((List.range' i n).reverse.map fun j => if h : j < r then bTl L ⟨j, h⟩ w else 1).prod := by
  induction n with
  | zero =>
    intro i hn hi
    rw [level_product_of_ge L w i (by omega)]
    simp
  | succ n ihn =>
    intro i hn hi
    have hlt : i < r := by omega
    rw [level_product_of_lt L w i hlt, ihn (i + 1) (by omega) (by omega), List.range'_succ, List.reverse_cons,
      List.map_append, List.prod_append]
    simp [hlt]

theorem level_product_zero (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) :
    levelProduct L w 0 = bTall L w := by
  have hfr : (List.finRange r).map Fin.val = List.range r := by
    first
    | exact List.map_val_finRange r
    | exact List.map_coe_finRange r
    | exact List.map_coe_finRange
    | simp
  rw [level_product_eq_list_prod L w r 0 (Nat.sub_zero r) (Nat.zero_le r), bTall, ← List.range_eq_range',
    ← hfr, List.map_reverse, List.map_map, List.map_reverse]
  congr 2
  apply List.map_congr_left
  intro j _
  simp [j.isLt]

theorem level_product_act_succ (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (w : List (Letter ℂ S)) (l : Fin r)
    (x : Ix S → RadSp k r z z' π π') :
    act (levelProduct L w l.val) x = act (levelProduct L w (l.val + 1)) (act (bTl L l w) x) := by
  rw [level_product_of_lt L w l.val l.isLt, act_mul]

def levelIntegrand (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (i : Fin (r + 1)) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (q : Cf r i × Mt k r) : ℂ :=
  ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
    topDens L st w (act (levelProduct L w i.val) x) (act (levelProduct L w i.val) y) (glue i c q.1) (Matrix.of q.2)

def coordinateSplitAssoc (l : Fin r) {β : Type} [MeasurableSpace β] : Cf r l.castSucc × β ≃ᵐ ℂ × (Cf r l.succ × β) :=
  ((coordinateSplit l).prodCongr (MeasurableEquiv.refl β)).trans MeasurableEquiv.prodAssoc

theorem coordinate_split_assoc_measurePreserving (l : Fin r) {β : Type} [MeasurableSpace β] (ν : Measure β) [SFinite ν] :
    MeasurePreserving (coordinateSplitAssoc l (β := β)) (volume.prod ν) (volume.prod (volume.prod ν)) := by
  have h1 : MeasurePreserving (Prod.map (coordinateSplit l) (id : β → β)) (volume.prod ν)
      ((volume : Measure (ℂ × Cf r l.succ)).prod ν) :=
    (coordinate_split_measurePreserving l).prod (MeasurePreserving.id ν)
  exact (measurePreserving_prodAssoc volume volume ν).comp h1

theorem level_integrand_split_point (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (w : List (Letter ℂ S)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ)
    (q : Cf r l.succ × Mt k r) :
    levelIntegrand L st w l.castSucc x y c ((coordinateSplitAssoc l).symm (t, q)) =
      ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * levelIntegrand L st w l.succ (act (bTl L l w) x) (act (bTl L l w) y)
        (Function.update c l t) q := by
  have hq : (coordinateSplitAssoc l).symm (t, q) = ((coordinateSplit l).symm (t, q.1), q.2) := rfl
  rw [hq]
  simp only [levelIntegrand]
  rw [weight_coordinate_split l ((coordinateSplit l).symm (t, q.1)), glue_coordinate_split l c]
  simp only [MeasurableEquiv.apply_symm_apply, Fin.coe_castSucc, Fin.val_succ, level_product_act_succ]
  push_cast
  ring

end B

section Main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)} [SFinite μ]
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

def LevelIntegralFormula (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (w : List (Letter ℂ S)) (i : Fin (P.r + 1)) :
    Prop :=
  ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → InK (K i) y → ∀ c ∈ OmX P.r,
    Integrable (levelIntegrand L st w i x y c) (volume.prod μ) ∧
      RRform L st μ i w x y c = ∫ q, levelIntegrand L st w i x y c q ∂(volume.prod μ)

theorem level_product_preserves_compact (hS : SliceIn (S := S) P z z' π π' L st K l0) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (i : Fin (P.r + 1)) :
    ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → InK (K (Fin.last P.r)) (act (levelProduct L w i.val) x) := by
  suffices H : ∀ n i, P.r - i = n → ∀ (hi : i ≤ P.r) (x : Ix S → RadSp P.k P.r z z' π π'),
      InK (K ⟨i, Nat.lt_succ_of_le hi⟩) x → InK (K (Fin.last P.r)) (act (levelProduct L w i) x) by
    intro x hx
    exact H _ i.val rfl (Nat.lt_succ_iff.mp i.isLt) x hx
  intro n
  induction n with
  | zero =>
    intro i hn hi x hx
    have hir : i = P.r := by omega
    subst hir
    rw [level_product_of_ge L w _ le_rfl, act_one_hermitian_curvature]
    exact hx
  | succ n ihn =>
    intro i hn hi x hx
    have hlt : i < P.r := by omega
    rw [show levelProduct L w i = levelProduct L w (i + 1) * bTl L ⟨i, hlt⟩ w from level_product_of_lt L w i hlt, act_mul]
    exact ihn (i + 1) (by omega) hlt (act (bTl L ⟨i, hlt⟩ w) x) (hS w hw ⟨i, hlt⟩ x hx)

theorem level_integral_formula_top (hT : TopIdent (S := S) P z z' π π' μ L st K l0) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) : LevelIntegralFormula P z z' π π' μ L st K w (Fin.last P.r) := by
  intro x y hx hy c hc
  obtain ⟨hI, hE⟩ := hT w hw x y hx hy c hc
  have hf : levelIntegrand L st w (Fin.last P.r) x y c = fun q => topDens L st w x y c (Matrix.of q.2) := by
    funext q
    simp only [levelIntegrand, Fin.val_last, level_product_of_ge L w P.r le_rfl, act_one_hermitian_curvature, glue_last_level]
    haveI : IsEmpty {l : Fin P.r // P.r ≤ l.val} := ⟨fun l => by have := l.1.isLt; have := l.2; omega⟩
    rw [Fintype.prod_empty]
    simp
  have hT' := integral_top_level_point μ (fun q : Cf P.r (Fin.last P.r) × Mt P.k P.r => topDens L st w x y c (Matrix.of q.2))
  rw [hf]
  exact ⟨hT'.1.2 hI, hE.trans hT'.2.symm⟩

theorem integrable_of_quartic_decay (φ : ℂ → ℂ) (hφc : Continuous φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) :
    Integrable φ := by
  have hI : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
  refine (hI.const_mul C).mono' hφc.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have h4 : (1 + ‖t‖) ^ (-(4 : ℝ)) = (1 + ‖t‖) ^ (-4 : ℤ) := by
    rw [show (-(4 : ℝ)) = ((-4 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  rw [h4]
  exact hC t

theorem ae_complex_ne_zero : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  simp

theorem complex_norm_eq_re_of_nonneg {z : ℂ} (hz : 0 ≤ z) : ‖z‖ = z.re := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.mp hz
  have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [← h2])
  conv_lhs => rw [hz']
  rw [Complex.norm_real, Real.norm_of_nonneg h1]

private lemma act_add_smul_hermitian_curvature (M : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π')))
    (x y : Ix S → RadSp P.k P.r z z' π π') (a : ℂ) : act M (x + a • y) = act M x + a • act M y := by
  funext b
  simp only [act, Pi.add_apply, Pi.smul_apply, map_add, map_smul, Finset.sum_add_distrib, Finset.smul_sum]

private lemma inK_add_smul_of_inK {Kc : Submodule ℂ (RadSp P.k P.r z z' π π')} {x y : Ix S → RadSp P.k P.r z z' π π'}
    (hx : InK Kc x) (hy : InK Kc y) (a : ℂ) : InK Kc (x + a • y) :=
  fun b => Kc.add_mem (hx b) (Kc.smul_mem a (hy b))

private lemma densNonneg_S_consequence (hN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hS : SliceIn (S := S) P z z' π π' L st K l0) (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (u : Ix S → RadSp P.k P.r z z' π π') (hu : InK (K i) u) (c : Fin P.r → ℂ)
    (hc : c ∈ OmX P.r) (q : Cf P.r i × Mt P.k P.r) : 0 ≤ levelIntegrand L st w i u u c q := by
  unfold levelIntegrand
  by_cases h0 : ∀ j, q.1 j ≠ 0
  · have hg : glue i c q.1 ∈ OmX P.r := by
      simp only [OmX, Set.mem_setOf_eq]
      intro l
      unfold glue
      split_ifs with h
      · exact h0 _
      · exact hc l
    have hwt : (0 : ℂ) ≤ ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (Finset.prod_nonneg fun l _ => zpow_nonneg (norm_nonneg _) _)
    exact mul_nonneg hwt (hN w hw _ (level_product_preserves_compact hS w hw i u hu) _ hg _)
  · push_neg at h0
    obtain ⟨j, hj⟩ := h0
    have h1 : (∏ l, ‖q.1 l‖ ^ (-2 : ℤ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, norm_zero]; exact zero_zpow _ (by norm_num))
    rw [h1]
    simp

theorem level_integral_formula_step (hN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hS : SliceIn (S := S) P z z' π π' L st K l0) (hD : StepDens (S := S) P z z' π π' μ L st K l0)
    (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (lf : Fin P.r) (ih : LevelIntegralFormula P z z' π π' μ L st K w lf.succ) :
    LevelIntegralFormula P z z' π π' μ L st K w lf.castSucc := by
  intro x y hx hy c hc
  have hE := coordinate_split_assoc_measurePreserving lf (β := Mt P.k P.r) μ
  have hEs := MeasurePreserving.symm (coordinateSplitAssoc lf) hE
  have hupd : ∀ t : ℂ, t ≠ 0 → Function.update c lf t ∈ OmX P.r := by
    intro t ht
    simp only [OmX, Set.mem_setOf_eq] at hc ⊢
    intro j
    by_cases hj : j = lf
    · subst hj
      simp [ht]
    · rw [Function.update_of_ne hj]
      exact hc j
  have hSl : ∀ u, InK (K lf.castSucc) u → InK (K lf.succ) (act (bTl L lf w) u) :=
    fun u hu => hS w hw lf u hu
  have hmeasF : ∀ u v, InK (K lf.castSucc) u → InK (K lf.castSucc) v →
      AEStronglyMeasurable (levelIntegrand L st w lf.castSucc u v c) (volume.prod μ) := fun u v hu hv =>
    level_integrand_aestronglyMeasurable hM w _ _ (level_product_preserves_compact hS w hw _ u hu) (level_product_preserves_compact hS w hw _ v hv) lf.castSucc c
  have hdiag : ∀ u, InK (K lf.castSucc) u → Integrable (levelIntegrand L st w lf.castSucc u u c) (volume.prod μ) := by
    intro u hu
    obtain ⟨φ, hφc, hφe, ⟨C, hC⟩, -⟩ := hD w hw lf u u hu hu c hc
    have hφi := integrable_of_quartic_decay φ hφc C hC
    rw [← hEs.integrable_comp_emb (coordinateSplitAssoc lf).symm.measurableEmbedding]
    refine (integrable_prod_iff ((hmeasF u u hu hu).comp_measurePreserving hEs)).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_complex_ne_zero] with t ht
      simp only [Function.comp_apply, level_integrand_split_point]
      exact ((ih _ _ (hSl u hu) (hSl u hu) _ (hupd t ht)).1).const_mul _
    · refine hφi.re.congr ?_
      filter_upwards [ae_complex_ne_zero] with t ht
      have hF := ih _ _ (hSl u hu) (hSl u hu) _ (hupd t ht)
      have hnn := fun q => densNonneg_S_consequence hN hS w hw lf.succ _ (hSl u hu) _ (hupd t ht) q
      have ha : (0 : ℝ) ≤ ‖t‖ ^ (-2 : ℤ) := zpow_nonneg (norm_nonneg _) _
      have hre : ∫ q, (levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
          (Function.update c lf t) q).re ∂(volume.prod μ) =
          (∫ q, levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
          (Function.update c lf t) q ∂(volume.prod μ)).re := by
        have := integral_re hF.1
        simpa using this
      calc RCLike.re (φ t) = (ph L st μ lf w u u c t).re := by rw [hφe t ht]; rfl
        _ = ‖t‖ ^ (-2 : ℤ) * (∫ q, levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
              (Function.update c lf t) q ∂(volume.prod μ)).re := by
            rw [ph, hF.2, Complex.re_ofReal_mul]
        _ = ∫ q, ‖t‖ ^ (-2 : ℤ) * (levelIntegrand L st w lf.succ (act (bTl L lf w) u) (act (bTl L lf w) u)
              (Function.update c lf t) q).re ∂(volume.prod μ) := by
            rw [integral_const_mul, hre]
        _ = ∫ q, ‖(levelIntegrand L st w lf.castSucc u u c ∘ (coordinateSplitAssoc lf).symm) (t, q)‖ ∂(volume.prod μ) := by
            congr 1
            funext q
            rw [Function.comp_apply, level_integrand_split_point, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha,
              complex_norm_eq_re_of_nonneg (hnn q)]
  have hint : ∀ u v, InK (K lf.castSucc) u → InK (K lf.castSucc) v →
      Integrable (levelIntegrand L st w lf.castSucc u v c) (volume.prod μ) := by
    intro u v hu hv
    have hb := fun s : ℂ => hdiag (u + s • v) (inK_add_smul_of_inK hu hv s)
    refine (((((hb 1).norm.add (hb Complex.I).norm).add (hb (-1)).norm).add (hb (-Complex.I)).norm).div_const
      4).mono' (hmeasF u v hu hv) (Filter.Eventually.of_forall fun q => ?_)
    refine sesquilinear_polarization_norm (fun a b => levelIntegrand L st w lf.castSucc a b c q) (fun a a' b s => ?_)
      (fun a b b' s => ?_) u v
    · simp only [levelIntegrand, act_add_smul_hermitian_curvature, top_density_add_left]
      ring
    · simp only [levelIntegrand, act_add_smul_hermitian_curvature, top_density_add_right]
      ring
  refine ⟨hint x y hx hy, ?_⟩
  obtain ⟨φ, -, hφe, -, hφI⟩ := hD w hw lf x y hx hy c hc
  have hGi : Integrable (fun p => levelIntegrand L st w lf.castSucc x y c ((coordinateSplitAssoc lf).symm p))
      (volume.prod (volume.prod μ)) :=
    (hEs.integrable_comp_emb (coordinateSplitAssoc lf).symm.measurableEmbedding).mpr (hint x y hx hy)
  calc RRform L st μ lf.castSucc w x y c = ∫ t, φ t := hφI.symm
    _ = ∫ t, ∫ q, levelIntegrand L st w lf.castSucc x y c ((coordinateSplitAssoc lf).symm (t, q)) ∂(volume.prod μ) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_complex_ne_zero] with t ht
        rw [hφe t ht, ph, (ih _ _ (hSl x hx) (hSl y hy) _ (hupd t ht)).2]
        simp only [level_integrand_split_point]
        rw [integral_const_mul]
    _ = ∫ p, levelIntegrand L st w lf.castSucc x y c ((coordinateSplitAssoc lf).symm p) ∂(volume.prod (volume.prod μ)) :=
        (integral_prod _ hGi).symm
    _ = _ := hEs.integral_comp' _

theorem integral_formula_level_zero (hT : TopIdent (S := S) P z z' π π' μ L st K l0) (hN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hS : SliceIn (S := S) P z z' π π' L st K l0) (hD : StepDens (S := S) P z z' π π' μ L st K l0)
    (hM : TopDensMeas S P z z' π π' μ L st K) : CompositeFormulaLevelZero (S := S) P z z' π π' μ L st K l0 := by
  intro w hw x y hx hy c hc
  have H : ∀ n (i : Fin (P.r + 1)), P.r - i.val = n → LevelIntegralFormula P z z' π π' μ L st K w i := by
    intro n
    induction n with
    | zero =>
      intro i hn
      have hi : i = Fin.last P.r := Fin.ext (by rw [Fin.val_last]; have := i.isLt; omega)
      subst hi
      exact level_integral_formula_top hT w hw
    | succ n ihn =>
      intro i hn
      have hlt : i.val < P.r := by omega
      have hi : i = (⟨i.val, hlt⟩ : Fin P.r).castSucc := Fin.ext rfl
      rw [hi]
      exact level_integral_formula_step hN hS hD hM w hw ⟨i.val, hlt⟩ (ihn _ (by show P.r - (i.val + 1) = n; omega))
  have h0 := H _ 0 rfl x y hx hy c hc
  have hf : levelIntegrand L st w 0 x y c = fun q => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w (act (bTall L w) x) (act (bTall L w) y) (glue 0 c q.1) (Matrix.of q.2) := by
    funext q
    simp only [levelIntegrand, Fin.val_zero, level_product_zero]
  rw [hf] at h0
  exact h0

theorem integral_formula_of_steps : CompositeFormulaOfDensities := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ _ L st l0 K hT hN hS hD hM
  exact integral_formula_level_zero hT hN hS hD hM

end Main

end Formalism.FourierDecayAlt.P5
