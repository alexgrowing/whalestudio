import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ExistsInsW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.VolumeIsAddHaar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cov_split (d : SD σ) (w : InfinitePlace F) (ins : Matrix (Fin d.m) (Fin d.n) ℂ → Mx F E d.m d.n)
    (hins : ∀ M, d.cw w (ins M) = M ∧ (∀ w', w' ≠ w → d.cw w' (ins M) = 0) ∧ finOne F • ins M = 0)
    (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) :
    (∀ f ∈ d.schM, Integrable f ν) ∧ ∃ (c : ℝ) (ν₀ : Measure (d.restW w)), 0 < c ∧
      ∀ G : Mx F E d.m d.n → ℂ, Integrable G ν →
        ∫ X, G X ∂ν = c * ∫ v : Fin d.m → Fin d.n → ℂ, ∫ Z : d.restW w, G (ins (Matrix.of v) + Z.1) ∂ν₀ := by
  haveI := hν.1
  refine ⟨fun f hf => int_schM d ν hν.1 hf, ?_⟩
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI : LocallyCompactSpace (Mx F E d.m d.n) := inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E))
  haveI : SecondCountableTopology (Mx F E d.m d.n) :=
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E))
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  have hcl : IsClosed ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n)) :=
    isClosed_eq (Place.continuous_cw d w) continuous_const
  haveI : LocallyCompactSpace (d.restW w) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (d.restW w) :=
    TopologicalSpace.Subtype.secondCountableTopology ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI : BorelSpace (d.restW w) := Subtype.borelSpace ((d.restW w : AddSubgroup (Mx F E d.m d.n)) : Set (Mx F E d.m d.n))
  haveI := volume_isAddHaar d.m d.n
  obtain ⟨s, hsc, hs1, hs2, hsa, -⟩ := Place.exists_sec d.cm d.B.emb
  let sW : (Fin d.m → Fin d.n → ℂ) → Mx F E d.m d.n := fun u i j => s fun w' => if w' = w then u i j else 0
  have cw_sW : ∀ u, d.cw w (sW u) = Matrix.of u := fun u => by
    ext i j
    show piInf (d.B.emb w) (s _) = u i j
    rw [hs1, if_pos rfl]
  have cw_sW' : ∀ u w', w' ≠ w → d.cw w' (sW u) = 0 := fun u w' h => by
    ext i j
    show piInf (d.B.emb w') (s _) = 0
    rw [hs1, if_neg h]
  have fin_sW : ∀ u, finOne F • sW u = 0 := fun u => by
    ext i j
    show finOne F • s _ = 0
    exact hs2 _
  have ins_eq : ∀ u, ins (Matrix.of u) = sW u := fun u => by
    obtain ⟨h1, h2, h3⟩ := hins (Matrix.of u)
    refine Place.cw_ext d (fun w' => ?_) (by rw [h3, fin_sW])
    by_cases h : w' = w
    · subst h; rw [h1, cw_sW]
    · rw [h2 w' h, cw_sW' u w' h]
  have sW_add : ∀ u v, sW (u + v) = sW u + sW v := fun u v => by
    ext i j
    show s _ = s _ + s _
    rw [← hsa]
    congr 1
    funext w'
    show _ = (if w' = w then u i j else 0) + (if w' = w then v i j else 0)
    by_cases h : w' = w
    · rw [if_pos h, if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h, if_neg h, add_zero]
  have hsW : Continuous sW := by
    refine continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun w' => ?_)
    split_ifs
    · exact (continuous_apply j).comp (continuous_apply i)
    · exact continuous_const
  have cw_sub : ∀ X Z : Mx F E d.m d.n, d.cw w (X - Z) = d.cw w X - d.cw w Z := fun X Z =>
    Matrix.map_sub _ (map_sub _) X Z
  have cw_add : ∀ X Z : Mx F E d.m d.n, d.cw w (X + Z) = d.cw w X + d.cw w Z := fun X Z =>
    Matrix.map_add _ (map_add _) X Z
  let cwf : Mx F E d.m d.n → Fin d.m → Fin d.n → ℂ := fun X i j => d.cw w X i j
  have hcwf : ∀ X, Matrix.of (cwf X) = d.cw w X := fun X => rfl
  have hccwf : Continuous cwf := Place.continuous_cw d w
  have mem : ∀ X, X - sW (cwf X) ∈ d.restW w := fun X => by
    show d.cw w (X - sW (cwf X)) = 0
    rw [cw_sub, cw_sW, hcwf]
    exact sub_self _
  let Φ : (Fin d.m → Fin d.n → ℂ) × d.restW w ≃ₜ+ Mx F E d.m d.n :=
    { toFun := fun p => sW p.1 + p.2.1
      invFun := fun X => (cwf X, ⟨X - sW (cwf X), mem X⟩)
      left_inv := fun p => by
        obtain ⟨u, b, hb⟩ := p
        have hb' : d.cw w b = 0 := hb
        have e1 : cwf (sW u + b) = u := by
          show Matrix.of.symm (d.cw w (sW u + b)) = u
          rw [cw_add, cw_sW, hb', add_zero]; rfl
        refine Prod.ext e1 (Subtype.ext ?_)
        show sW u + b - sW (cwf (sW u + b)) = b
        rw [e1]
        exact add_sub_cancel_left _ _
      right_inv := fun X => by
        show sW (cwf X) + (X - sW (cwf X)) = X
        rw [add_sub_cancel]
      map_add' := fun p q => by
        show sW (p.1 + q.1) + (p.2.1 + q.2.1) = sW p.1 + p.2.1 + (sW q.1 + q.2.1)
        rw [sW_add]; abel
      continuous_toFun := (hsW.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
      continuous_invFun := hccwf.prodMk ((continuous_id.sub (hsW.comp hccwf)).subtype_mk _) }
  obtain ⟨c, hc, hνc⟩ := measure_split ν (volume : Measure (Fin d.m → Fin d.n → ℂ)) (Measure.addHaar : Measure (d.restW w)) Φ
  refine ⟨c, Measure.addHaar, NNReal.coe_pos.mpr hc, fun G hG => ?_⟩
  let e : (Fin d.m → Fin d.n → ℂ) × d.restW w ≃ᵐ Mx F E d.m d.n := Φ.toHomeomorph.toMeasurableEquiv
  have hme : Measure.map Φ ((volume : Measure (Fin d.m → Fin d.n → ℂ)).prod (Measure.addHaar : Measure (d.restW w))) =
      Measure.map e ((volume : Measure (Fin d.m → Fin d.n → ℂ)).prod (Measure.addHaar : Measure (d.restW w))) := rfl
  rw [hνc, hme] at hG
  have hG1 := (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).1 hG
  have hG2 := (integrable_map_equiv e G).1 hG1
  rw [hνc, hme, integral_smul_nnreal_measure, integral_map_equiv]
  show c • ∫ x, (G ∘ e) x ∂_ = _
  rw [integral_prod _ hG2, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  show G (sW v + Z.1) = G (ins (Matrix.of v) + Z.1)
  rw [ins_eq]

end PositivityTheory.SiegelWeilFormula.KFock

end
