import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccATensWordMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccBLowKShiftF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccurrencePhiSmoothL2

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def occPsOK (dual : Bool) (ε : Fin n → Bool) (M M' : Submodule ℂ (smD ε (rreg ε)))
    (ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε)) : Prop :=
  (∀ f ∈ tensSub M, ps f ∈ M') ∧
    (∀ a b, ∀ f ∈ tensSub M, ps (tensF dual (smE ε (rreg ε)) a b f) = smE ε (rreg ε) a b (ps f)) ∧
    ∀ k ∈ Kset ε, ∀ f ∈ tensSub M, ∀ f' ∈ tensSub M,
      (fun c => ((f' c : smD ε (rreg ε)) : L2 ε)) = kDiag dual (rreg ε) k (fun c => ((f c : smD ε (rreg ε)) : L2 ε)) →
      ((ps f' : smD ε (rreg ε)) : L2 ε) = rreg ε k ((ps f : smD ε (rreg ε)) : L2 ε)

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
  {v₀ : T.V} {v₀' : T'.V}

theorem occC_pairing (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
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
  exact occurrence_pairing dual hgap hP hv₀ hP' hW hB

theorem occC_proj_smD (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0) (x : L2 ε)
    (hx : x ∈ smD ε (rreg ε)) : ((Hlam ε Ψ' v₀').orthogonalProjectionOnto x : L2 ε) ∈ smD ε (rreg ε) := by
  exact projection_preserves_smooth hgap' hP' hv₀' x hx

theorem occC_proj_smE (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0) (x : smD ε (rreg ε))
    (a b : Fin n) :
    ((smE ε (rreg ε) a b ⟨((Hlam ε Ψ' v₀').orthogonalProjectionOnto (x : L2 ε) : L2 ε),
        occC_proj_smD hgap' hP' hv₀' x x.2⟩ : smD ε (rreg ε)) : L2 ε) =
      ((Hlam ε Ψ' v₀').orthogonalProjectionOnto ((smE ε (rreg ε) a b x : smD ε (rreg ε)) : L2 ε) : L2 ε) := by
  exact projection_commutes_derived_action hgap' hP' hv₀' x (projection_preserves_smooth hgap' hP' hv₀' _ x.2) a b

theorem occC_proj_mem (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (η f : Fin n → smD ε (rreg ε)) (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))) :
    ∃ y ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'), (y : L2 ε) =
      ((Hlam ε Ψ' v₀').orthogonalProjectionOnto (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
        (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) : L2 ε) := by
  obtain ⟨y, hy, e⟩ := occurrence_projection_mem dual hP hv₀ hgap' hP' hv₀' hW η f hη hf
  exact ⟨y, hy, e⟩

theorem occC_exists_ps (dual : Bool) (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hgap' : StdGap ε lam') (hP' : IsPsiFor ε lam' T' Ψ') (hv₀' : v₀' ≠ 0)
    (hW : ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
        inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2 (Formalism.REAL.muG ε))
    (hne : ∃ η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      ∃ x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀'),
        inner ℂ (toL2 ε (occCoef dual (rreg ε) (fun c => ((η c : smD ε (rreg ε)) : L2 ε))
          (fun c => ((f c : smD ε (rreg ε)) : L2 ε)))) ((x' : smD ε (rreg ε)) : L2 ε) ≠ 0) :
    ∃ ps : (Fin n → smD ε (rreg ε)) →ₗ[ℂ] smD ε (rreg ε),
      occPsOK dual ε (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) (genSub (smE ε (rreg ε)) (datumV ε Ψ' v₀')) ps ∧
      ∃ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), ps f ≠ 0 := by
  obtain ⟨η, hη, f₀, hf₀, x', hx', hne0⟩ := hne
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hsm : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)), occC2phi dual ε η f ∈ smD ε (rreg ε) :=
    fun f hf => toL2_mem_smD_of_isSmoothL2 (occurrence_phi_smooth_L2 dual hW hη hf)
  have hsmP : ∀ f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)),
      (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f) ∈ smD ε (rreg ε) :=
    fun f hf => projection_preserves_smooth hgap' hP' hv₀' _ (hsm f hf)
  let ps0 : tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)) →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨(Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f.1), hsmP f.1 f.2⟩
      map_add' := fun f f' => Subtype.ext (by
        show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (f.1 + f'.1)) = _
        rw [occurrence_phi_add dual hW hη f.2 f'.2, map_add]
        rfl)
      map_smul' := fun a f => Subtype.ext (by
        show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (a • f.1)) = _
        rw [occurrence_phi_smul, map_smul]
        rfl) }
  obtain ⟨ps, hps⟩ := LinearMap.exists_extend ps0
  have hpsf : ∀ f (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))),
      ps f = ⟨(Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f), hsmP f hf⟩ :=
    fun f hf => LinearMap.congr_fun hps ⟨f, hf⟩
  refine ⟨ps, ⟨fun f hf => ?_, fun a b f hf => ?_, fun k hk f hf f' hf' hff => ?_⟩, f₀, hf₀, ?_⟩
  · obtain ⟨y, hy, hyeq⟩ := occurrence_projection_mem dual hP hv₀ hgap' hP' hv₀' hW η f hη hf
    have e : ps f = y := by rw [hpsf f hf]; exact Subtype.ext hyeq.symm
    rw [e]; exact hy
  · have hf2 := tensSub_stable dual a b f hf
    rw [hpsf _ hf2, hpsf f hf]
    have h3 := projection_commutes_derived_action hgap' hP' hv₀' (⟨occC2phi dual ε η f, hsm f hf⟩ : smD ε (rreg ε)) (hsmP f hf) a b
    apply Subtype.ext
    refine Eq.trans ?_ h3.symm
    show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η (tensF dual (smE ε (rreg ε)) a b f)) =
      (Hlam ε Ψ' v₀').starProjection ((smE ε (rreg ε) a b ⟨occC2phi dual ε η f, hsm f hf⟩ : smD ε (rreg ε)) : L2 ε)
    congr 1
    refine Eq.trans ?_ (rightDerivative_toL2 (occurrence_phi_smooth_L2 dual hW hη hf) a b).symm
    apply toL2_congr_of_forall_inUJ_eq
    intro g hg
    exact (occA_coef_Eab dual hσ hD _ f a b hg).symm
  · rw [hpsf f' hf', hpsf f hf]
    show (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f') =
      rreg ε k ((Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f))
    rw [← occurrence_phi_k_equivariant dual η f f' hk hff, projection_commutes_right_regular hgap' hP' hv₀' k (cf_kset_sub hk)]
  · intro h0
    apply hne0
    have hP0 : (Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f₀) = 0 := by
      have := congrArg Subtype.val ((hpsf f₀ hf₀).symm.trans h0)
      exact this
    have hx'H : ((x' : smD ε (rreg ε)) : L2 ε) ∈ Hlam ε Ψ' v₀' :=
      Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hx')
    rw [← (Submodule.starProjection_eq_self_iff (K := Hlam ε Ψ' v₀')).2 hx'H,
      ← Submodule.inner_starProjection_left_eq_right]
    show inner ℂ ((Hlam ε Ψ' v₀').starProjection (occC2phi dual ε η f₀)) _ = 0
    rw [hP0, inner_zero_left]

end Psi

end ReciprocityTheory.ChartRestriction.DS
