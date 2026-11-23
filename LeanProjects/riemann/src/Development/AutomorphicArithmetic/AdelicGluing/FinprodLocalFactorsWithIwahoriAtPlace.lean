import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem under_over {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem cmp_atFin {v : Pl F} (w : PlacesOver E v) (g : AdelicGLn.AdelicGL E n) :
    cmp w (mapGL n (atFin v) g) = finAt w.1 g := by
  ext i j
  rfl

private theorem fin_above (v : Pl F) : {w : Pl E | w.under (𝓞 F) = v}.Finite := by
  refine (Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  rintro w rfl
  exact ⟨⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem a_fin (U : Set (Pl E)) (hU : U.Finite) (f : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ)
    (hf : ∀ w ∉ U, f w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1)
    (x : AdelicGLn.FiniteAdelicGL E n) : (Function.mulSupport fun w => f w (cf w x)).Finite := by
  have h := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL E n (finEmb E n x))
  refine (h.union hU).subset fun v hv => ?_
  by_contra hc
  rw [Set.mem_union, not_or] at hc
  have h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion E) n := not_not.1 hc.1
  apply hv
  simp only [hf v hc.2]
  exact Set.indicator_of_mem (by exact h1) _

open Classical in
private theorem iw_split {q : Pl F} (w₀ : PlacesOver E q) (m : Fin n → ℤ) (x : AdelicGLn.FiniteAdelicGL E n) :
    iwFn w₀ m (mapGL n (atFin q) (finEmb E n x)) = (iwCoset w₀.1 m).indicator 1 (cf w₀.1 x) *
      ∏ᶠ w : PlacesOver E q, if w = w₀ then 1 else (iwCoset w.1 (0 : Fin n → ℤ)).indicator 1 (cf w.1 x) := by
  unfold iwFn prodFn
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]
  have key : ∀ w : PlacesOver E q, (iwCoset w.1 (if w = w₀ then m else 0)).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ) (cmp w (mapGL n (atFin q) (finEmb E n x))) =
      (if w = w₀ then (iwCoset w₀.1 m).indicator (1 : GL (Fin n) (w₀.1.adicCompletion E) → ℂ) (cf w₀.1 x) else 1) *
        (if w = w₀ then 1 else (iwCoset w.1 (0 : Fin n → ℤ)).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ) (cf w.1 x)) := by
    intro w
    rw [cmp_atFin]
    by_cases hw : w = w₀
    · subst hw
      simp [cf]
    · simp [hw, cf]
  rw [Finset.prod_congr rfl fun w _ => key w, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ w₀]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.finprod_local_factors_with_iwahori_at_place :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (S : Finset (Pl F)) (q : Pl F), q ∉ S → ∀ (w₀ : PlacesOver E q)
        (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E)),
        (∀ w ∈ κ, w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q) →
        ∀ (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
        (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) →
        ∀ (m : Fin n → ℤ) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ),
        (∀ v ∈ S, φ v = ψ v) → φ q = iwFn w₀ m →
        (∀ v ∉ S, v ≠ q → φ v = prodFn fun w : PlacesOver E v => h w.1) → ∀ x : AdelicGLn.FiniteAdelicGL E n,
        ∏ᶠ v, φ v (mapGL n (atFin v) (finEmb E n x)) =
          rF S w₀ ψ κ x * (iwCoset w₀.1 m).indicator 1 (cf w₀.1 x) * ∏ w ∈ κ, h w (cf w x) := by
  intro F E _ _ _ _ _ n S q hq w₀ ψ κ hκ h hh m φ hS hqφ hoff x
  classical
  let T : Set (Pl E) := {w | w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q}
  have hTfin : T.Finite := by
    refine ((insert q S : Finset (Pl F)).finite_toSet.biUnion fun v _ => fin_above (E := E) v).subset ?_
    intro w hw
    refine Set.mem_biUnion (x := w.under (𝓞 F)) ?_ rfl
    rcases hw with hw | hw
    · simp [hw]
    · simp [hw]
  let h' : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ := fun w => if w ∈ T then 1 else h w
  have hh'T : ∀ w ∈ T, h' w = 1 := fun w hw => by simp only [h', if_pos hw]
  have hh'N : ∀ w ∉ T, h' w = h w := fun w hw => by simp only [h', if_neg hw]
  have hUfin : (T ∪ (κ : Set (Pl E))).Finite := hTfin.union κ.finite_toSet
  have hU : ∀ w ∉ T ∪ (κ : Set (Pl E)), h' w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1 := by
    intro w hw
    rw [Set.mem_union, not_or] at hw
    rw [hh'N w hw.1]
    exact hh w hw.2
  have hafin := a_fin _ hUfin h' hU x
  have hten := UpperTheory.ConvolutionTheory.Tf.tensEProd F E n h'
    (Filter.eventually_cofinite.2 (hUfin.subset fun w hw => by_contra fun hc => hw (hU w hc))) (finEmb E n x)
  let X : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) := fun v => mapGL n (atFin v) (finEmb E n x)
  let B : Pl F → ℂ := fun v => prodFn (v := v) (fun w => h' w.1) (X v)
  let A : Pl F → ℂ := fun v => if v ∈ insert q S then φ v (X v) else 1
  have hB1 : ∀ v ∈ insert q S, B v = 1 := by
    intro v hv
    have hw : ∀ w : PlacesOver E v, h' w.1 (cmp w (X v)) = 1 := by
      intro w
      have : w.1 ∈ T := by
        have := Finset.mem_insert.1 hv
        rcases this with rfl | hv
        · exact Or.inr (under_over w)
        · exact Or.inl ((under_over w).symm ▸ hv)
      rw [hh'T _ this]
      rfl
    simp only [B, prodFn, hw, finprod_one]
  have hfac : ∀ v, φ v (X v) = A v * B v := by
    intro v
    by_cases hv : v ∈ insert q S
    · simp only [A, if_pos hv, hB1 v hv, mul_one]
    · have hv' := Finset.mem_insert.not.1 hv
      push_neg at hv'
      simp only [A, if_neg hv, one_mul, B]
      rw [hoff v hv'.2 hv'.1]
      unfold prodFn
      refine finprod_congr fun w => ?_
      show h w.1 (cmp w (X v)) = h' w.1 (cmp w (X v))
      rw [hh'N]
      rintro (h1 | h1)
      · exact hv'.2 (under_over w ▸ h1)
      · exact hv'.1 ((under_over w).symm.trans h1)
  have hAsub : Function.mulSupport A ⊆ (insert q S : Finset (Pl F)) := by
    intro v hv
    by_contra hc
    exact hv (if_neg hc)
  have hAfin : (Function.mulSupport A).Finite := (Finset.finite_toSet _).subset hAsub
  have hBfin : (Function.mulSupport B).Finite := by
    refine (hafin.image fun w : Pl E => w.under (𝓞 F)).subset ?_
    intro v hv
    by_contra hc
    apply hv
    have hw : ∀ w : PlacesOver E v, h' w.1 (cmp w (X v)) = 1 := by
      intro w
      by_contra hne
      refine hc ⟨w.1, ?_, under_over w⟩
      intro h0
      apply hne
      rw [show cmp w (X v) = cf w.1 x from cmp_atFin w _]
      exact h0
    simp only [B, prodFn, hw, finprod_one]
  have hAprod : ∏ᶠ v, A v = iwFn w₀ m (X q) * ∏ v ∈ S, ψ v (X v) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hAsub, Finset.prod_insert hq]
    congr 1
    · simp only [A, Finset.mem_insert_self, if_true, hqφ]
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [A, if_pos (Finset.mem_insert_of_mem hv), hS v hv]
  have hBprod : ∏ᶠ v, B v = ∏ᶠ w, h' w (cf w x) := hten
  have haprod : ∏ᶠ w, h' w (cf w x) = (Cnd S q κ).indicator 1 x * ∏ w ∈ κ, h w (cf w x) := by
    by_cases hx : x ∈ Cnd S q κ
    · have hsub : Function.mulSupport (fun w => h' w (cf w x)) ⊆ κ := by
        intro w hw
        by_contra hc
        apply hw
        show h' w (cf w x) = 1
        by_cases hT : w ∈ T
        · rw [hh'T w hT]
          rfl
        · rw [hU w (by simp only [Set.mem_union, not_or]; exact ⟨hT, hc⟩)]
          have hT' : w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q := by
            simpa [T, not_or] using hT
          exact Set.indicator_of_mem (hx w hc hT'.1 hT'.2) _
      rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Set.indicator_of_mem hx]
      simp only [Pi.one_apply, one_mul]
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [hh'N]
      rintro (h1 | h1)
      · exact (hκ w hw).1 h1
      · exact (hκ w hw).2 h1
    · have hex : ∃ w, w ∉ κ ∧ w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q ∧
          cf w x ∉ GLnLocal.integralGL (w.adicCompletion E) n := by
        by_contra hc
        push_neg at hc
        exact hx fun w h1 h2 h3 => hc w h1 h2 h3
      obtain ⟨w, hwκ, hwS, hwq, hnot⟩ := hex
      have hwT : w ∉ T := by
        rintro (h1 | h1)
        · exact hwS h1
        · exact hwq h1
      have h0 : h' w (cf w x) = 0 := by
        rw [hU w (by simp only [Set.mem_union, not_or]; exact ⟨hwT, hwκ⟩)]
        exact Set.indicator_of_notMem hnot _
      rw [finprod_eq_zero (fun w => h' w (cf w x)) w h0 hafin, Set.indicator_of_notMem hx, zero_mul]
  have hfinal : ∏ᶠ v, φ v (X v) = (∏ᶠ v, A v) * ∏ᶠ v, B v := by
    rw [← finprod_mul_distrib hAfin hBfin]
    exact finprod_congr hfac
  show ∏ᶠ v, φ v (X v) = _
  rw [hfinal, hAprod, hBprod, haprod, iw_split]
  unfold rF
  ring
