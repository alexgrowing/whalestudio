import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

private theorem cmp_val (w : PlacesOver E v) (g : GL (Fin n) (CompletionsOver E v)) (i j : Fin n) :
    (UpperTheory.ConvolutionTheory.GM.cmp w g).val i j = g.val i j w := rfl

private theorem cmp_continuous (w : PlacesOver E v) :
    Continuous (UpperTheory.ConvolutionTheory.GM.cmp (n := n) w) := by
  have hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val := by
    refine continuous_matrix fun i j => ?_
    simp only [cmp_val]
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have : (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val)
      = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact this ▸ hv.comp continuous_inv

private theorem loc_bd (w : Pl E) {C : Set (GL (Fin n) (w.adicCompletion E))} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, locHeight g ≤ B := by
  have hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion E) → ℝ) := by
    unfold locHeight
    refine continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))
    · exact (Units.continuous_val.matrix_elem _ _).nnnorm
    · exact (Units.continuous_coe_inv.matrix_elem _ _).nnnorm
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

private theorem infAt_finEmb' (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) : infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem lies_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_of_lies {w : Pl E} {v : Pl F} (hl : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 F) = v := by
  ext1
  exact (hl.over).symm

end

theorem UpperTheory.height_bounded_on_support_of_compact_test_functions :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (S : Finset (Pl F)) (q : Pl F) (κ : Finset (Pl E))
        (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
        (∀ v ∈ S, HasCompactSupport (ψ v)) → (∀ w ∈ κ, HasCompactSupport (h w)) →
        ∃ Yf : ℝ, 1 ≤ Yf ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n, (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) →
          (∀ w ∈ κ, h w (cf w x) ≠ 0) → x ∈ Cnd S q κ → heightOff q (finEmb E n x) ≤ Yf := by
  classical
  intro F E _ _ _ _ _ n S q κ ψ h hψ hh
  have key : ∀ w : Pl E, ∃ M : ℝ, 1 ≤ M ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n,
      (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) → (∀ w ∈ κ, h w (cf w x) ≠ 0) →
      (w ∈ κ ∨ w.under (𝓞 F) ∈ S) → locHeight (cf w x) ≤ M := by
    intro w
    by_cases hk : w ∈ κ
    · obtain ⟨B, hB1, hB⟩ := loc_bd w (hh w hk).isCompact
      exact ⟨B, hB1, fun x _ h2 _ => hB _ (subset_tsupport _ (Function.mem_support.2 (h2 w hk)))⟩
    · by_cases hs : w.under (𝓞 F) ∈ S
      · have hc := (hψ _ hs).isCompact.image (cmp_continuous (n := n) (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F))))
        obtain ⟨B, hB1, hB⟩ := loc_bd w hc
        refine ⟨B, hB1, fun x h1 _ _ => ?_⟩
        have e : UpperTheory.ConvolutionTheory.GM.cmp (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F)))
            (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) = cf w x := by
          ext i j
          rfl
        rw [← e]
        exact hB _ ⟨_, subset_tsupport _ (Function.mem_support.2 (h1 _ hs)), rfl⟩
      · exact ⟨1, le_rfl, fun x _ _ hd => absurd hd (by simp [hk, hs])⟩
  choose M hM1 hM using key
  let W : Finset (Pl E) := κ ∪ S.biUnion fun v => (Finset.univ : Finset (PlacesOver E v)).image Subtype.val
  have hW : ∀ w, w ∈ W ↔ (w ∈ κ ∨ w.under (𝓞 F) ∈ S) := by
    intro w
    simp only [W, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    refine or_congr Iff.rfl ⟨?_, fun hs => ⟨_, hs, ⟨w, lies_under w⟩, rfl⟩⟩
    rintro ⟨v, hv, p, rfl⟩
    rwa [under_of_lies p.2]
  refine ⟨∏ w ∈ W, M w, Finset.prod_induction _ (fun y : ℝ => 1 ≤ y)
    (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun w _ => hM1 w, ?_⟩
  intro x h1 h2 hx
  unfold heightOff
  have hi : (∏ w : InfinitePlace E, locHeight (infAt w (finEmb E n x)) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]
  rw [hi, one_mul]
  have hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (finEmb E n x))) =
      if w.under (𝓞 F) ≠ q then locHeight (cf w x) else 1 := by
    intro w
    rw [finprod_eq_if]
    rfl
  simp only [hg]
  rw [finprod_eq_prod_of_mulSupport_subset (s := W)]
  · refine Finset.prod_le_prod (fun w _ => ?_) fun w hw => ?_
    · split_ifs
      · exact (locHeight_pos _).le
      · exact zero_le_one
    · split_ifs with hq
      · exact hM w x h1 h2 ((hW w).1 hw)
      · exact hM1 w
  · intro w hw
    by_contra hc
    apply hw
    have hc' : w ∉ W := hc
    rw [hW, not_or] at hc'
    by_cases hq : w.under (𝓞 F) = q
    · simp [hq]
    · simp only [ne_eq, hq, not_false_eq_true, if_true]
      exact locHeight_eq_one_of_mem_integralGL (hx w hc'.1 hc'.2 hq)
