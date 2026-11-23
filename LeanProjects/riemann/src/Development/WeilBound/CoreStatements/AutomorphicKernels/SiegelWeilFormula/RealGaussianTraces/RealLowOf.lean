import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.CpowProdOfReal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem card_places (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) {ι : Type} [Fintype ι]
    (θ : ι → (Ainf F ⊗[F] E →+* ℂ)) (l : ι → ℝ) (hP : IsPlaces σ ψ θ l) :
    Fintype.card ι = Module.finrank ℚ F := by
  classical
  haveI : IsTotallyReal F := hCM.1
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let eT := GlobalTheory.SiegelWeilConvCompare.tensHomeo (F := F) (E := E) (Ainf F) b
  let eR : Ainf F ≃ₜ (InfinitePlace F → ℝ) := Homeomorph.piCongrRight fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).toHomeomorph
  have hRadd : ∀ x y : InfinitePlace F → ℝ, eR.symm (x + y) = eR.symm x + eR.symm y := by
    intro x y; funext v
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.map_add (x v) (y v)
  have hTadd : ∀ x y : Fin 2 → Ainf F, eT.symm (x + y) = eT.symm x + eT.symm y := by
    intro x y
    exact (Algebra.TensorProduct.basis (Ainf F) b).equivFun.symm.map_add x y
  let f : (Fin 2 → InfinitePlace F → ℝ) → (ι → ℂ) := fun x i => θ i (eT.symm (fun k => eR.symm (x k)))
  have hfadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y; funext i
    simp only [f, Pi.add_apply]
    rw [show (fun k => eR.symm (x k + y k)) = (fun k => eR.symm (x k)) + (fun k => eR.symm (y k)) from
      funext fun k => hRadd (x k) (y k), hTadd, map_add]
  let fA : (Fin 2 → InfinitePlace F → ℝ) →+ (ι → ℂ) :=
    { toFun := f
      map_zero' := by
        have h0 := hfadd 0 0
        rw [add_zero] at h0
        exact (add_eq_left.1 h0.symm)
      map_add' := hfadd }
  have hfc : Continuous fA := continuous_pi fun i => (hP.cont i).comp
    (eT.symm.continuous.comp (continuous_pi fun k => eR.symm.continuous.comp (continuous_apply k)))
  let L := fA.toRealLinearMap hfc
  have hbij : Function.Bijective L := by
    have h1 : Function.Bijective (fun x : Fin 2 → InfinitePlace F → ℝ => fun k => eR.symm (x k)) :=
      (Equiv.piCongrRight fun _ => eR.symm.toEquiv).bijective
    exact hP.bij.comp (eT.symm.bijective.comp h1)
  have hr := (LinearEquiv.ofBijective (L : (Fin 2 → InfinitePlace F → ℝ) →ₗ[ℝ] (ι → ℂ)) hbij).finrank_eq
  simp only [Module.finrank_pi, Module.finrank_fin_fun, Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Module.finrank_self] at hr
  have hc : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      add_zero, IsTotallyReal.finrank]
  omega

theorem realLow_of (h : WROrd) : RealLow := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hMn ψ hψ ι _ θ l hP e fr hfr g μ ν hμ hν T hT
  classical
  haveI : IsTotallyReal F := hCM.1
  haveI := secondCountable_tens (F := F) (E := E)
  haveI := borel_tens (F := F) (E := E)
  haveI := borel_herm (F := F) (E := E) σ n
  obtain ⟨eC, heC⟩ := exists_crdHomeo σ hCM ψ θ l hP fr g
  obtain ⟨eb, heb⟩ := exists_ybHomeo σ hCM ψ θ l hP g
  haveI := haar_volE ι n
  haveI := haar_volW ι M n
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨cμ, -, hcμ⟩ := exists_map_eq_smul (volume : Measure (ι → Fin M → Fin n → ℂ)) μ eC
  obtain ⟨cb, -, hcb⟩ := exists_map_eq_smul (volume : Measure (ι → WR.E n)) ν eb
  have hl : ∀ i, l i ≠ 0 := hP.ne
  have hβ : ∀ i, (herm (ygAll σ θ g T i)).det ≠ 0 := det_herm_ygAll σ hCM ψ θ l hP g T hT
  have hw : ∀ i, ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ ∃ σ₀ : ℝ, ∀ z : ℂ, σ₀ < z.re →
      Integrable (fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z) ∧
      z ^ (n - M) * W z = ∫ y, fw (fun _ : Fin M => e i) (l i) (1 : PX M n) (ygAll σ θ g T i) z y := by
    intro i
    have hc : 0 < 2 * Real.pi * |l i| := by have := abs_pos.2 (hl i); positivity
    have ht : 2 * Real.pi * l i = 2 * Real.pi * |l i| ∨ 2 * Real.pi * l i = -(2 * Real.pi * |l i|) := by
      rcases le_or_gt 0 (l i) with h | h
      · left; rw [abs_of_nonneg h]
      · right; rw [abs_of_neg h]; ring
    exact h M n hMn (e i) (2 * Real.pi * |l i|) (2 * Real.pi * l i) hc ht (ygAll σ θ g T i) (hβ i)
  choose Wi hWid hrest using hw
  choose σ₀ hσ₀ using hrest
  set s0 : ℂ := ((M : ℂ) - n) / 2 with hs0
  refine ⟨fun z => (cb : ℂ) * (cμ : ℂ) * ∏ i, Wi i (z - s0), ?_, ((M : ℝ) - n) / 2 + ∑ i, |σ₀ i|,
    fun z hz => ?_⟩
  · refine (differentiable_const _).mul ?_
    have := Differentiable.finset_prod (u := Finset.univ) (f := fun i z => Wi i (z - s0))
      (fun i _ => (hWid i).comp (differentiable_id.sub_const s0))
    rw [Finset.prod_fn] at this
    exact this
  · have hzi : ∀ i, σ₀ i < (z - s0).re := by
      intro i
      have h1 : (z - s0).re = z.re - ((M : ℝ) - n) / 2 := by
        rw [hs0]; simp
      have h2 : σ₀ i ≤ ∑ j, |σ₀ j| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |σ₀ j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i))
      rw [h1]; linarith
    have hint : ∀ i, Integrable (fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i)
        (ygAll σ θ g T i) (z - s0)) := fun i => (hσ₀ i _ (hzi i)).1
    obtain ⟨h1, h2⟩ := integral_whI σ hCM ψ θ l hP J (fun i _ => e i) fr hfr g (fun _ => 1) μ eC heC cμ hcμ ν eb heb
      cb hcb T z hint
    refine ⟨h1, ?_⟩
    rw [← hs0] at h2
    rw [h2]
    have h3 : ∀ i, ∫ y, fw ((fun i (_ : Fin M) => e i) i) (l i) ((fun _ => (1 : PX M n)) i)
        (ygAll σ θ g T i) (z - s0) y = (z - s0) ^ (n - M) * Wi i (z - s0) := fun i => ((hσ₀ i _ (hzi i)).2).symm
    simp only [h3]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places σ hCM ψ θ l hP, ← pow_mul,
      mul_comm (n - M)]
    ring

end PositivityTheory.SiegelWeilFormula.GReal
