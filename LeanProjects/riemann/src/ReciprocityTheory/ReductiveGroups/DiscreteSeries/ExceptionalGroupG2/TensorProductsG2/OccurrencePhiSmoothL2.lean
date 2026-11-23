import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccurrencePhiKEquivariant
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occurrence_pairing (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hP' : IsPsiFor ε lam' T' Ψ')
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hB : ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0) :
    ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0 := by
  obtain ⟨ξ, ζ, v', hI⟩ := hB
  have hσ := rreg_isURepOn ε
  let jm : T.V → smD ε (rreg ε) := fun v => ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  have hjm : ∀ v, jm v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) := fun v =>
    layer_le_genSub (ε := ε) 0 ((mem_datumV_iff hP v₀ _).2 ⟨v, rfl⟩)
  have hη : (fun c => jm (ξ c)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := tset_mem.2 fun c => hjm _
  have hf : (fun c => jm (ζ c)) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) := tset_mem.2 fun c => hjm _
  refine ⟨fun c => jm (ξ c), hη, fun c => jm (ζ c), hf, ⟨uniformisationL2 ε Ψ' v₀' v', datumEmbedding_mem_smooth hP' v₀' v'⟩,
    layer_le_genSub (ε := ε) 0 ((mem_datumV_iff hP' v₀' _).2 ⟨v', rfl⟩), ?_⟩
  have hF : ∀ g, inUJ ε g → occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε)) g =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g := by
    intro g hg
    have hg' : g ∈ UJset ε := hg
    simp only [occCoef, occPsiCoef, tensGrp, jm, inner_sum, inner_smul_right, formulaF hgap hP hv₀ hg',
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  have hM1 : MemLp (fun g : Formalism.REAL.UJ ε => (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) *
      occPsiCoef dual Ψ ξ ζ g) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    (occA_coef_memLp dual hσ hW _ _ hη hf).ae_eq (Filter.Eventually.of_forall fun g => hF _ g.2)
  have e1 : toL2 ε (occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε))) =
      toL2 ε (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g) := toL2_congr_of_forall_inUJ_eq hF
  have e2 : inner ℂ (toL2 ε (fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g))
      (toL2 ε (jfun Ψ' v₀' v')) = starRingEnd ℂ (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)) *
        ∫ g : Formalism.REAL.UJ ε, starRingEnd ℂ (occPsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
          inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v') ∂(Formalism.REAL.muG ε) := by
    rw [inner_toL2_eq_theta_pairing ε (F := fun g => ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * occPsiCoef dual Ψ ξ ζ g)
      (G := jfun Ψ' v₀' v') hM1 (dt_memLp hP' v₀' v'), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [map_mul, jfun, mul_assoc]
  have hC : starRingEnd ℂ (((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    rw [Complex.conj_ofReal]
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 (datumEmbedding_highest_ne_zero hgap hP hv₀))
  have ex : ((⟨uniformisationL2 ε Ψ' v₀' v', datumEmbedding_mem_smooth hP' v₀' v'⟩ : smD ε (rreg ε)) : L2 ε) = toL2 ε (jfun Ψ' v₀' v') := rfl
  rw [ex]
  show inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((jm (ξ c) : smD ε (rreg ε)) : L2 ε))
      (fun c => ((jm (ζ c) : smD ε (rreg ε)) : L2 ε)))) (toL2 ε (jfun Ψ' v₀' v')) ≠ 0
  rw [e1, e2]
  exact mul_ne_zero hC hI

theorem occurrence_phi_smooth_L2 (dual : Bool)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    {η f : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    IsSmoothL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε)) (fun c => ((f c : smD ε (rreg ε)) : L2 ε))) := by
  have hσ := rreg_isURepOn ε
  refine ⟨occA_coef_smooth dual hσ _ _ (fun d => (mem_smD_iff ε (rreg ε) _).1 (f d).2), fun w => ?_⟩
  exact (occA_coef_memLp dual hσ hW η (tensWord dual (smE ε (rreg ε)) w f) hη (occA_tensWord_mem dual w f hf)).ae_eq
    (Filter.Eventually.of_forall fun g => (occA_coef_Eword dual hσ (isDerivedOn_smE hσ) _ w f g.2).symm)

end Psi

end ReciprocityTheory.ChartRestriction.DS.G2
