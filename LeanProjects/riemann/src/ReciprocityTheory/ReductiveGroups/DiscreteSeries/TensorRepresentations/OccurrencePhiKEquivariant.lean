import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ProjectionCommutesDerivedAction
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.CompactIsDSUniqueOfCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumIrr

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Phi

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}

def occC2phi (dual : Bool) (ε : Fin n → Bool) (η f : Fin n → smD ε (rreg ε)) : L2 ε :=
  toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε)) (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))

theorem occurrence_phi_add (dual : Bool)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    {η f f' : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf' : f' ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    occC2phi dual ε η (f + f') = occC2phi dual ε η f + occC2phi dual ε η f' := by
  unfold occC2phi
  have e : (fun c => (((f + f') c : smD ε (rreg ε)) : L2 ε)) =
      (fun c => ((f c : smD ε (rreg ε)) : L2 ε)) + (fun c => ((f' c : smD ε (rreg ε)) : L2 ε)) := by
    funext c; simp
  rw [e, occurrence_coef_add]
  exact toL2_add_smooth ε (occA_coef_memLp dual (rreg_isURepOn ε) hW η f hη hf)
    (occA_coef_memLp dual (rreg_isURepOn ε) hW η f' hη hf')

theorem occurrence_phi_smul (dual : Bool) (η f : Fin n → smD ε (rreg ε)) (a : ℂ) :
    occC2phi dual ε η (a • f) = a • occC2phi dual ε η f := by
  unfold occC2phi
  have e : (fun c => (((a • f) c : smD ε (rreg ε)) : L2 ε)) = a • (fun c => ((f c : smD ε (rreg ε)) : L2 ε)) := by
    funext c; simp
  rw [e, occurrence_coef_smul]
  exact toL2_smul_smooth ε a _

theorem occurrence_phi_k_equivariant (dual : Bool) (η f f' : Fin n → smD ε (rreg ε)) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε)
    (hff : (fun c => ((f' c : smD ε (rreg ε)) : L2 ε)) = kDiag dual (rreg ε) k (fun c => ((f c : smD ε (rreg ε)) : L2 ε))) :
    rreg ε k (occC2phi dual ε η f) = occC2phi dual ε η f' := by
  unfold occC2phi
  rw [rightRegular_toL2 ε _ (cf_kset_sub hk)]
  apply toL2_congr_of_forall_inUJ_eq
  intro g hg
  show ∑ c, _ = ∑ c, _
  rw [occA_tensGrp_mul dual (rreg_isURepOn ε) hg hk, ← hff]

end Phi

section Mem

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occurrence_projection_mem (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (η f : Fin n → smD ε (rreg ε)) (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f) ∈
      (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')).map (smD ε (rreg ε)).subtype := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV := datumV_isKIrrHW hP hv₀
  obtain ⟨j, hj⟩ := tensor_generated_mem_layer hD.glRep hV.2.1 hf
  set W := layer ε (smE ε (rreg ε)) (datumV ε Ψ v₀) j with hWdef
  have : FiniteDimensional ℂ W := finiteDimensional_layer hV.1 j
  have hWM : ∀ u : Fin n → W, (fun c => ((u c : W) : smD ε (rreg ε))) ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) :=
    fun u => (tset_mem).2 fun c => layer_le_genSub j (u c).2
  let P := (Hlam ε Ψ' v₀').starProjection
  let Φ : (Fin n → W) →ₗ[ℂ] L2 ε :=
    { toFun := fun u => P (occC2phi dual ε η (fun c => ((u c : W) : smD ε (rreg ε))))
      map_add' := fun u u' => by
        have e : (fun c => (((u + u') c : W) : smD ε (rreg ε))) =
            (fun c => ((u c : W) : smD ε (rreg ε))) + (fun c => ((u' c : W) : smD ε (rreg ε))) := by
          funext c; simp
        rw [e, occurrence_phi_add dual hW hη (hWM u) (hWM u'), map_add]
      map_smul' := fun a u => by
        have e : (fun c => (((a • u) c : W) : smD ε (rreg ε))) = a • (fun c => ((u c : W) : smD ε (rreg ε))) := by
          funext c; simp
        simp only [RingHom.id_apply]
        rw [e, occurrence_phi_smul, map_smul] }
  have hSf : FiniteDimensional ℂ (LinearMap.range Φ) := LinearMap.finiteDimensional_range Φ
  have hS : LinearMap.range Φ ≤ closGen (smE ε (rreg ε)) (datumV ε Ψ' v₀') := by
    rintro x ⟨u, rfl⟩
    exact Submodule.starProjection_apply_mem (Hlam ε Ψ' v₀') _
  have hSK : ∀ k ∈ Kset ε, ∀ x ∈ LinearMap.range Φ, rreg ε k x ∈ LinearMap.range Φ := by
    rintro k hk x ⟨u, rfl⟩
    have hy := fun d => layer_k_stable hσ hD hV.2.1 (datumV_kStable hP v₀) j k hk (u d : W) (u d).2
    choose y hyW hy using hy
    let u' : Fin n → W := fun c => ∑ d, (cond dual (star (k c d)) (k c d)) • (⟨y d, hyW d⟩ : W)
    refine ⟨u', ?_⟩
    show P _ = rreg ε k (P _)
    rw [← projection_commutes_right_regular hgap' hP' hv₀' k (cf_kset_sub hk)]
    congr 1
    refine (occurrence_phi_k_equivariant dual η _ _ hk ?_).symm
    funext c
    simp only [u', kDiag, Submodule.coe_sum, Submodule.coe_smul, hy]
  have hle := data_kfin_le hgap' hσ hD (datumV_isKIrrHW hP' hv₀') (datumV_casimir hP' v₀') (datumV_kStable hP' v₀')
    (LinearMap.range Φ) hS hSf hSK
  apply hle
  refine ⟨fun c => ⟨f c, hj c⟩, ?_⟩
  rfl

end Mem

end ReciprocityTheory.ChartRestriction.DS
