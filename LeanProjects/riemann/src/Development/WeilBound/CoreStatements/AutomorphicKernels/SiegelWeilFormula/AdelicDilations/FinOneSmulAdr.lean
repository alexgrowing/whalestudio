import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneAdr

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def adrU [IsTotallyReal F] (w : InfinitePlace F) (τ : ℝ) : (AF F)ˣ :=
  ⟨adr w (Real.exp τ), adr w (Real.exp (-τ)),
    by rw [adr_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, adr_one],
    by rw [adr_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, adr_one]⟩

theorem evInf_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) : evInf F u (adr w r) = (adr w r).1 u := rfl

theorem evFin_adr [IsTotallyReal F] (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (r : ℝ) :
    evFin F v (adr w r) = 1 := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (adr w r).2 = 1
  rw [adr_snd, map_one]

theorem norm_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) : ‖(adr w r).1 u‖ = |if u = w then r else 1| := by
  rw [← (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding u).norm_map_of_map_zero (map_zero _),
    ext_adr, Complex.norm_real, Real.norm_eq_abs]

theorem piInf_adr (h : IsCMExt F E σ) (τ' : ∀ w : InfinitePlace F, EmbOver E w) (w u : InfinitePlace F) (r : ℝ) :
    haveI := h.1
    piInf (τ' u) (algebraMap (AF F) (AE F E) (adr w r)) = ((if u = w then r else 1 : ℝ) : ℂ) := by
  haveI := h.1
  show GlobalTheory.AdelicU.infEmb (τ' u) (GlobalTheory.AdelicU.compInf F E u (algebraMap (AF F) (AE F E) (adr w r))) = _
  rw [Algebra.TensorProduct.algebraMap_apply]
  show GlobalTheory.AdelicU.infEmb (τ' u)
    (Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F u) (AlgHom.id F E) (adr w r ⊗ₜ[F] (1 : E))) = _
  rw [Algebra.TensorProduct.map_tmul, evInf_adr, AlgHom.id_apply]
  simp only [GlobalTheory.AdelicU.infEmb, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  exact ext_adr w u r

theorem finOne_smul_adr (h : IsCMExt F E σ) (w : InfinitePlace F) (r : ℝ) :
    haveI := h.1
    finOne F • algebraMap (AF F) (AE F E) (adr w r) = finOne F • (1 : AE F E) := by
  haveI := h.1
  rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, finOne_adr, mul_one]

theorem absE_adrU (h : IsCMExt F E σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := h.1
    ((absE F E (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℝ≥0) : ℝ) = Real.exp (2 * τ) := by
  haveI := h.1
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) = 1 := by
    intro v
    have h1 : GlobalTheory.Doubling.unitFin F E v
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) = 1 := by
      apply Units.ext
      show GlobalTheory.AdelicU.compFin F E v (algebraMap (AF F) (AE F E) (adr w (Real.exp τ))) = 1
      rw [Algebra.TensorProduct.algebraMap_apply]
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E)
        (adr w (Real.exp τ) ⊗ₜ[F] (1 : E)) = 1
      rw [Algebra.TensorProduct.map_tmul, evFin_adr, AlgHom.id_apply, ← Algebra.TensorProduct.one_def]
    rw [h1, map_one]
  have hinf : ∀ u, (GlobalTheory.Doubling.absEw F E u (GlobalTheory.Doubling.unitInf F E u
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) : ℝ) =
      |if u = w then Real.exp τ else 1| ^ 2 := by
    intro u
    have hval : ((GlobalTheory.Doubling.unitInf F E u
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : (TensorProduct F u.Completion E)ˣ) :
          TensorProduct F u.Completion E) =
        algebraMap u.Completion (TensorProduct F u.Completion E) ((adr w (Real.exp τ)).1 u) := by
      show GlobalTheory.AdelicU.compInf F E u (algebraMap (AF F) (AE F E) (adr w (Real.exp τ))) = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F u) (AlgHom.id F E)
        (adr w (Real.exp τ) ⊗ₜ[F] (1 : E)) = _
      rw [Algebra.TensorProduct.map_tmul, evInf_adr, AlgHom.id_apply]
      rfl
    have hmult : u.mult = 1 := by
      rw [NumberField.InfinitePlace.mult, if_pos (NumberField.IsTotallyReal.isReal u)]
    show ((‖Algebra.norm u.Completion ((GlobalTheory.Doubling.unitInf F E u
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : (TensorProduct F u.Completion E)ˣ) :
          TensorProduct F u.Completion E)‖₊ ^ u.mult : ℝ≥0) : ℝ) = _
    rw [hval, hmult, pow_one, Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1, coe_nnnorm,
      norm_pow, norm_adr]
  show (((∏ u, GlobalTheory.Doubling.absEw F E u (GlobalTheory.Doubling.unitInf F E u
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)))) *
      ∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) : ℝ≥0) : ℝ) = _
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod, Finset.prod_eq_single w]
  · rw [hinf, if_pos rfl, Real.abs_exp, sq, ← Real.exp_add, two_mul]
  · intro b _ hb
    rw [hinf, if_neg hb, abs_one, one_pow]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

theorem chi_adrU (d : SD σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := d.cm.1
    (d.χ (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℂ) = 1 := by
  haveI := d.cm.1
  have hmem : adrU w τ ∈ (Units.map (Algebra.norm (AF F) (S := AE F E))).range := by
    refine ⟨Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w (τ / 2)), ?_⟩
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (TensorProduct F (AF F) E) (adr w (Real.exp (τ / 2)))) =
      adr w (Real.exp τ)
    rw [Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) d.bs), Fintype.card_fin, pow_two,
      adr_mul, ← Real.exp_add, add_halves]
  have h2 := d.ok.res (adrU w τ)
  split_ifs at h2 with hc
  · exact h2
  · exact absurd (Subgroup.mem_sup_right hmem) hc

end PositivityTheory.SiegelWeilFormula.AStep

end
