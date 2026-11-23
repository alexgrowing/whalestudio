import Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.IsAvLeft
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane

noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKEnd.Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d j : ℕ}
  {W : Spc F E d} {u u' : Matrix (Fin d) (Fin j) E}

theorem conj_N {γ : UA σ W.J} {g g' : Matrix (Fin d) (Fin d) E} (e : mat γ = incM F g) (e' : mat γ⁻¹ = incM F g')
    {U U' : Submodule E (Fin d → E)} (h1 : ∀ z ∈ U, g *ᵥ z ∈ U') (h2 : ∀ z ∈ U', g' *ᵥ z ∈ U) (s : UA σ W.J) (hs : s ∈ unipU σ W U) :
    γ * s * γ⁻¹ ∈ unipU σ W U' := by
  obtain ⟨a, b⟩ := ((unipU_eq U).choose_spec.choose_spec.2 s).1 hs
  have k : ∀ z, mat (γ * s * γ⁻¹) *ᵥ incV F z = mat γ *ᵥ (mat s *ᵥ incV F (g' *ᵥ z)) := fun z => by
    rw [mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e', incM_mulVec]
  have k' : ∀ z, mat γ *ᵥ incV F (g' *ᵥ z) = incV F z := fun z => by
    rw [← incM_mulVec, ← e', Matrix.mulVec_mulVec, mat_mul_inv, Matrix.one_mulVec]
  refine ((unipU_eq U').choose_spec.choose_spec.2 _).2 ⟨fun z hz => by rw [k, a _ (h2 z hz), k'], fun z hz => ?_⟩
  have := b (g' *ᵥ z) fun x hx => PositivityTheory.ThKF.inclR_inj (F := F) (by
    rw [← fa_inc, ← fa_mat γ, k', e, incM_mulVec, fa_inc, hz _ (h1 x hx)])
  rw [k, ← k' z, ← Matrix.mulVec_sub]
  refine (Submodule.span_le (p := (Submodule.span (AE F E) (incV F '' (U' : Set (Fin d → E)))).comap (mat γ).mulVecLin)).2 ?_ this
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.subset_span ⟨_, h1 x hx, by rw [Matrix.mulVecLin_apply, e, incM_mulVec]⟩

theorem av_line (C : Ctx σ W) {d₁ : ℕ} {W₁ : Spc F E d₁} {H : Plane E d d₁} (hH : IsPlane σ H W W₁) {f : UA σ W.J → ℂ}
    (hf : IsAut (W := W) f) (h0 : IsCT H f 0) {x : Fin d → E} (hx : x ≠ 0) (hi : form σ W.J x x = 0) :
    Av σ W (Submodule.span E {x}) f 0 := by
  have h1 : Av σ W (Submodule.span E {H.x}) f 0 := by
    rw [Av, ← unipLine F E σ C.cm d d₁ W W₁ H (Or.inr C.skew) hH]; exact h0
  obtain ⟨g, g1, g2⟩ := wittVec F E σ C.cm d W.J C.skew C.det x H.x hx (fun e => by simpa [e, form] using hH.xy) hi hH.xx
  let γ : UA σ W.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) g, by
    change (incM F g.1)ᵀ * _ * (incM F g.1).map _ = _
    rw [incM_conj, ← incM_transpose_cuspidal_averages, ← incM_mul, ← incM_mul, g1]⟩
  have r : γ ∈ ratU σ W.J := Subgroup.mem_subgroupOf.2 ⟨g, rfl⟩
  have a1 : ∀ z ∈ Submodule.span E {x}, g.1 *ᵥ z ∈ Submodule.span E {H.x} := fun z hz => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Matrix.mulVec_smul, g2]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have a2 : ∀ z ∈ Submodule.span E {H.x}, (g⁻¹).1 *ᵥ z ∈ Submodule.span E {x} := fun z hz => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Matrix.mulVec_smul, ← g2, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have := isAv_transport (Γ := (ratU σ W.J).subgroupOf (unipU σ W (Submodule.span E {x}))) (conjE γ (conj_N rfl rfl a1 a2) fun s hs => by simpa using conj_N (γ := γ⁻¹) rfl rfl a2 a1 s hs)
    (fun s => conj_rat r s.1) h1
  intro μ 𝓕 b1 b2 b3 y
  refine (this μ 𝓕 b1 b2 b3 (γ * y)).trans ?_
  congr 1
  funext s
  change f (γ * s.1 * γ⁻¹ * (γ * y)) = _
  rw [mul_assoc, inv_mul_cancel_left, mul_assoc, hf.2 γ r]

theorem Ctx.frame (C : Ctx σ W) (U : Submodule E (Fin d → E)) (hU : ∀ x ∈ U, ∀ y ∈ U, form σ W.J x y = 0) :
    ∃ u u' : Matrix (Fin d) (Fin (Module.finrank E U)) E, colSp u = U ∧ Fr (σ : E →+* E) W.J u u' := by
  let b := Module.finBasis E U
  let u : Matrix (Fin d) (Fin (Module.finrank E U)) E := Matrix.of fun i k => (b k).1 i
  obtain ⟨u', h⟩ := exists_dual (c := (σ : E →+* E)) (J := W.J) (u := u) (GlobalTheory.SiegelSet.sigma_sigma C.cm) (Matrix.ext C.skew) C.det
    (Matrix.mulVec_injective_iff.2 (b.linearIndependent.map' U.subtype U.ker_subtype)) (Matrix.ext fun a k => by
      rw [Matrix.mul_assoc]; exact hU _ (b a).2 _ (b k).2)
  refine ⟨u, u', ?_, h⟩
  have := congrArg (Submodule.map U.subtype) b.span_eq
  rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at this

theorem Ctx.int_zero (C : Ctx σ W) {U : Submodule E (Fin d → E)} {f : UA σ W.J → ℂ} (h : Av σ W U f 0) (μ : Measure (unipU σ W U))
    (𝓕 : Set (unipU σ W U)) (h1 : μ.IsHaarMeasure) (h2 : IsFundamentalDomain ((ratU σ W.J).subgroupOf (unipU σ W U)) 𝓕 μ) (x) :
    ∫ s in 𝓕, f (s.1 * x) ∂μ = 0 := by
  obtain ⟨a, b⟩ := (C.good U).fin μ 𝓕 h1 h2
  have := h ((μ 𝓕)⁻¹ • μ) 𝓕 (Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 b.ne) (ENNReal.inv_ne_top.2 a))
    (h2.mono Measure.smul_absolutelyContinuous) (by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel a b.ne]) x
  rw [Measure.restrict_smul, integral_smul_measure] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 b.ne, ENNReal.inv_ne_top.2 a⟩)

end PositivityTheory.ThKEnd.Cusp

end
