import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem locHeight_diagPow_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ν : Fin n → ℤ) (j : ℕ) :
    locHeight (Cartan.diagPow (w.adicCompletion E) n fun i => (j : ℤ) * ν i) ≤
      locHeight (Cartan.diagPow (w.adicCompletion E) n ν) ^ j := by
  induction j with
  | zero =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((0 : ℕ) : ℤ) * ν i) = 1 :=
      Units.ext (by simp [Cartan.coe_diagPow])
    rw [h, locHeight_one, pow_zero]
  | succ j ih =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((j + 1 : ℕ) : ℤ) * ν i) =
        Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) *
          Cartan.diagPow (w.adicCompletion E) n ν := by
      refine Units.ext ?_
      rw [Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Cartan.coe_diagPow,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      push_cast
      rw [add_mul, one_mul, zpow_add₀ (Cartan.uniformizer_ne_zero _)]
    rw [h, pow_succ]
    exact (locHeight_mul_le_of_ultrametric _ _).trans
      (mul_le_mul_of_nonneg_right ih (locHeight_pos _).le)

private theorem locHeight_iwahori {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {a : GL (Fin n) (w.adicCompletion E)} (ha : a ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    locHeight a = 1 :=
  locHeight_eq_one_of_mem_integralGL (GLnLocal.iwahori_le_integralGL _ _ ha)

theorem UpperTheory.ConvolutionTheory.GM.htTot :
    HtTot := by
  classical
  intro F E _ _ _ _ _ n q w₀ ν
  refine ⟨locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν), one_le_locHeight _, ?_⟩
  intro j Y f hS g hg
  obtain ⟨h1, h2, h3⟩ := hS g hg
  have hfin := finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL E n)
  have hbelow : ∀ x : HeightOneSpectrum (𝓞 E), x.asIdeal.LiesOver q.asIdeal →
      AdeleBaseChange.below F x = q := by
    intro x hx
    refine HeightOneSpectrum.ext ?_
    have e1 := (AdeleBaseChange.liesOver_below (K := F) x).over
    have e2 := hx.over
    exact e1.trans e2.symm
  have split : (∏ᶠ w : HeightOneSpectrum (𝓞 E), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) =
      (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) *
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    have h := finprod_mem_union' (f := fun w : HeightOneSpectrum (𝓞 E) =>
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)))
      (s := {w | AdeleBaseChange.below F w ≠ q}) (t := {w | AdeleBaseChange.below F w = q})
      (Set.disjoint_left.2 fun w h₁ h₂ => h₁ h₂) (hfin.inter_of_right _) (hfin.inter_of_right _)
    have hu : {w : HeightOneSpectrum (𝓞 E) | AdeleBaseChange.below F w ≠ q} ∪
        {w | AdeleBaseChange.below F w = q} = Set.univ := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (em _).symm
    rw [hu, finprod_mem_univ] at h
    exact h
  have hC : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) ≤
      locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν) ^ j := by
    rw [finprod_eq_single _ w₀.1 ?_, finprod_eq_if, if_pos (hbelow _ w₀.2)]
    · obtain ⟨a, ha, b, hb, e⟩ := h2
      rw [e]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori hb, mul_one]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori ha, one_mul]
      exact locHeight_diagPow_le _ _ _ _
    · intro x hx
      rw [finprod_eq_if]
      split_ifs with hq
      · have hl : x.asIdeal.LiesOver q.asIdeal := hq ▸ AdeleBaseChange.liesOver_below x
        exact locHeight_iwahori (h3 ⟨x, hl⟩ fun h => hx (congrArg Subtype.val h))
      · rfl
  have hB : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hC0 : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hoff : 0 ≤ heightOff q (g : AdelicGLn.AdelicGL E n) :=
    mul_nonneg (zero_le_one.trans (one_le_prod_locHeight _)) hB
  have key : AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) =
      heightOff q (g : AdelicGLn.AdelicGL E n) *
        ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
          locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    rw [AutomorphicForm.height, split, heightOff, mul_assoc]
  rw [key]
  exact mul_le_mul h1 hC hC0 (hoff.trans h1)
