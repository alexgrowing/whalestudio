import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.EnormAddSqLe
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.ChainGen
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.DecayAssembly.Source

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.SA

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

theorem hasChar_path (hS : StepChar) {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (ss : List (Fin n))
    (h : HasChar X χ) : HasChar (path X χ ss) (pathEnd χ ss) := by
  induction ss generalizing X χ with
  | nil => exact h
  | cons s ss ih => exact ih _ _ (hS n X χ s h)

theorem assembly_of : Assembly := by
  intro hSC hAbs hGeo hLF hHaar hPoly hRR hLR hKR hGr hPk
  intro _ n ε H _ _ _ σ D E hK χ ss hU hSq hChar hN
  have hXc : HasChar (path ⟨D, E, hK.gl⟩ χ ss) (pathEnd χ ss) := hasChar_path hSC _ χ ss hChar
  obtain ⟨m, A, τ, c₁, R₀, C, hc₁, hgrad, hτc, hτK, hline, hτadd, hcover, hhs, hcontr⟩ := hGeo n ε
  choose ν hν using fun j => hHaar n ε (A j) (hgrad j)
  choose p hpm hp using fun j => hPoly n ε (path ⟨D, E, hK.gl⟩ χ ss) (pathEnd χ ss) (A j) hXc (hgrad j)
  obtain ⟨M, hM⟩ := hGr n ε H σ D E hK χ ss hU hSq
  apply hPk n ε H σ D E hK χ ss hU
  intro i u

  have hexp : ∀ j t, ReciprocityTheory.ChartRestriction.DS.inUJ ε (aT (A j) t) := fun j t => by
    obtain ⟨y, hy⟩ := hline j 1 t
    have hm : ReciprocityTheory.ChartRestriction.DS.inUJ ε (S7.toM (y : S7.UJ ε)) := (y : S7.UJ ε).2
    rw [hy] at hm
    simpa [show S7.toM (1 : S7.UJ ε) = 1 from rfl] using hm

  have hgline : ∀ j (q : (D × List (Fin n)) × (path ⟨D, E, hK.gl⟩ χ ss).V) (x : S7.UJ ε),
      Continuous fun t : ℝ => gen σ D E hK.gl χ ss q (S7.toM x * aT (A j) t) := fun j q x =>
    continuous_iff_continuousAt.mpr fun t =>
      (line_deriv hRR hK χ ss hU (A j) (hgrad j).1 (hexp j) q.1 q.2 (S7.toM x) x.2 t).continuousAt
  have hcontS : ∀ f ∈ SS σ D E hK.gl χ ss, Continuous fun g : S7.UJ ε => f (S7.toM g) :=
    cont_span (gen σ D E hK.gl χ ss) (fun g : S7.UJ ε => S7.toM g)
      (fun q => (hKR n ε H σ D E hK χ ss hU q.1 q.2).1)
  have hdomS : ∀ f ∈ SS σ D E hK.gl χ ss, ∃ (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)) (Cf : ℝ),
      (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧ ∀ (g : S7.UJ ε) (k k' : S7.KG ε),
        ‖f (S7.toMK k * S7.toM g * S7.toMK k')‖ ^ 2 ≤ Cf * ∑ h ∈ T, ‖h (S7.toM g)‖ ^ 2 := by
    intro f hf
    obtain ⟨T, Cf, hTS, hb⟩ := dom_span (gen σ D E hK.gl χ ss)
      (fun b : S7.UJ ε × S7.KG ε × S7.KG ε => S7.toMK b.2.1 * S7.toM b.1 * S7.toMK b.2.2)
      (fun b : S7.UJ ε × S7.KG ε × S7.KG ε => S7.toM b.1)
      (fun q => by
        obtain ⟨T, Cf, h⟩ := (hKR n ε H σ D E hK χ ss hU q.1 q.2).2
        exact ⟨T, Cf, fun b => h b.1 b.2.1 b.2.2⟩) f hf
    exact ⟨T, Cf, hTS, fun g k k' => hb (g, k, k')⟩
  have hchainS : ∀ f ∈ SS σ D E hK.gl χ ss, ∀ j, ∃ (f₀ : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (T : Finset (Matrix (Fin n) (Fin n) ℂ → ℂ)), Chain ε (SS σ D E hK.gl χ ss) (A j) ((p j).roots.toFinset) f f₀ ∧
        (∀ h ∈ T, h ∈ SS σ D E hK.gl χ ss) ∧ ∀ x : PSub ε (A j), 0 ≤ τ j x →
          ‖f₀ (S7.toM (x : S7.UJ ε))‖ ≤ Real.exp (-τ j x) * ∑ h ∈ T, ‖h (S7.toM (x : S7.UJ ε))‖ := by
    intro f hf j
    set zs := (p j).roots.toList with hzs
    have hQ := chain_span (gen σ D E hK.gl χ ss) ε (A j) (τ j) zs.length (fun k => zs[(k : ℕ)]'k.isLt)
      (fun q => by
        refine ⟨fun k => famP σ D E hK.gl χ ss q.1 (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 (k : ℕ)),
          fun k => gen_mem σ D E hK.gl χ ss _ _, ?_, ?_, ?_⟩
        · show famP σ D E hK.gl χ ss q.1 (wv _ (A j) zs q.2 (Fin.last zs.length : ℕ)) = _
          rw [Fin.val_last, wv_length]
          rfl
        · intro k g t hg
          have hd := line_deriv hRR hK χ ss hU (A j) (hgrad j).1 (hexp j) q.1
            (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 ((k : ℕ) + 1)) g hg t
          rw [wv_succ _ (A j) zs q.2 k k.isLt, map_add, map_smul] at hd
          simpa only [Fin.val_succ, Fin.val_castSucc, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul] using hd
        · obtain ⟨m', Y, v, hY, hpu⟩ := hp j q.2
          obtain ⟨T, hTS, hT⟩ := source_gen hLR hK χ ss hU (A j) (τ j) C (hcontr j) q.1 m' Y v hY
          refine ⟨T, hTS, fun x hx => ?_⟩
          have e : wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2 ((0 : Fin (zs.length + 1)) : ℕ) =
              ∑ k, actM (path ⟨D, E, hK.gl⟩ χ ss) (Y k) (v k) := by
            rw [Fin.val_zero, hzs, wv_zero _ (A j) (p j) (hpm j) q.2, hpu]
          show ‖famP σ D E hK.gl χ ss q.1 (wv (path ⟨D, E, hK.gl⟩ χ ss) (A j) zs q.2
            ((0 : Fin (zs.length + 1)) : ℕ)) (S7.toM (x : S7.UJ ε))‖ ≤ _
          rw [e]
          exact hT x hx) f hf
    obtain ⟨F, hFS, hFl, hFd, T, hTS, hT⟩ := hQ
    refine ⟨F 0, T, ⟨zs.length, fun k => zs[(k : ℕ)]'k.isLt, F, fun k => ?_, hFS, hFl, rfl, hFd⟩, hTS, hT⟩
    exact Multiset.mem_toFinset.mpr (Multiset.mem_toList.mp (List.getElem_mem _))
  have hqualS : ∀ f ∈ SS σ D E hK.gl χ ss, ∀ j, ∀ᵐ (x : PSub ε (A j)) ∂(ν j), (∫⁻ t in Set.Ioi (0 : ℝ),
      ‖f (S7.toM (x : S7.UJ ε) * aT (A j) t)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (2 * (rhoA (A j) + 1) * t))) < ⊤ := by
    intro f hf j
    refine ae_lint_span (gen σ D E hK.gl χ ss) (ν j) (volume.restrict (Set.Ioi (0 : ℝ)))
      (fun (x : PSub ε (A j)) (t : ℝ) => S7.toM (x : S7.UJ ε) * aT (A j) t)
      (fun t => ENNReal.ofReal (Real.exp (2 * (rhoA (A j) + 1) * t))) ?_ ?_ f hf
    · intro f' hf' x
      have hc := cont_span (gen σ D E hK.gl χ ss) (fun t : ℝ => S7.toM (x : S7.UJ ε) * aT (A j) t)
        (fun q => hgline j q (x : S7.UJ ε)) f' hf'
      exact ((continuous_enorm.comp hc).measurable.pow_const 2).mul
        (Measurable.ennreal_ofReal (by fun_prop)) |>.aemeasurable
    · intro q
      have h := hN (A j) (muPar ε (A j) (ν j)) (hgrad j) ⟨ν j, rfl, hν j⟩ q.2
      simp only [NSet, Set.mem_ofPred_eq] at h
      have h2 : ∀ᵐ y ∂((ν j).map Subtype.val), lineInt ε (famP σ D E hK.gl χ ss q.1 q.2) (A j) (-rhoA (A j) - 1) y < ⊤ :=
        h q.1
      have h3 := ae_of_ae_map measurable_subtype_coe.aemeasurable h2
      filter_upwards [h3] with x hx
      have e : ∀ t : ℝ, -2 * (-rhoA (A j) - 1) * t = 2 * (rhoA (A j) + 1) * t := fun t => by ring
      simp only [lineInt, e] at hx
      exact hx
  have hlevelS : ∀ f ∈ SS σ D E hK.gl χ ss, LevelF ε f (-M) := by
    intro f hf
    have hhs : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
      unfold Formalism.REAL.hs
      have := S7.continuous_toM ε
      fun_prop
    exact lint_span (gen σ D E hK.gl χ ss) Measure.haar (fun g : S7.UJ ε => S7.toM g)
      (fun g => ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-M)))
      (fun f' hf' => (((continuous_enorm.comp (hcontS f' hf')).measurable.pow_const 2).mul
        (hhs.measurable.pow_const (-M)).ennreal_ofReal).aemeasurable)
      (fun q => hM q.1 q.2) f hf
  have key := hAbs n ε (SS σ D E hK.gl χ ss) m A ν τ (fun j => rhoA (A j)) (fun j => (p j).roots.toFinset) M c₁ R₀ C
    hc₁ (fun j => hLF n ε (A j) (ν j) (τ j) (hgrad j) (hν j) (hτc j) (fun x t y hy => hτadd j x t y hy))
    hτc hτK (fun j x t => by obtain ⟨y, hy⟩ := hline j x t; exact ⟨y, hy, hτadd j x t y hy⟩)
    hcover hhs hcontS hdomS hchainS hqualS hlevelS
  exact key _ (gen_mem σ D E hK.gl χ ss i u)

end CompanionTheory.RgExh.Dec.L.SA
