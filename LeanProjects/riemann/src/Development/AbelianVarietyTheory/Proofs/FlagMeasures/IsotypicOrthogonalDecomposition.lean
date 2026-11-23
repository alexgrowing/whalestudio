import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfAdjointEqAlgebraMapOfCommuteIrreducible
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

section Abstract

variable {G H L : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

omit [CompleteSpace H] in
theorem inner_of_norm (A : H →L[ℂ] H) (hA : ∀ u, ‖A u‖ = ‖u‖) (x y : H) : ⟪A x, A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let e : H →ₗᵢ[ℂ] H := { toLinearMap := (A : H →ₗ[ℂ] H), norm_map' := hA }
  exact e.inner_map_map x y

theorem inner_intertwiners (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g u, ‖σ g u‖ = ‖u‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, σ g u ∈ S) → S = ⊥ ∨ S = ⊤)
    (R : G → (L →L[ℂ] L)) (hR : ∀ g u, ‖R g u‖ = ‖u‖) (w : H) (hw : ‖w‖ = 1)
    (T T' : H →L[ℂ] L) (hT : ∀ g, T.comp (σ g) = (R g).comp T) (hT' : ∀ g, T'.comp (σ g) = (R g).comp T')
    (u u' : H) : ⟪T u, T' u'⟫_ℂ = ⟪T w, T' w⟫_ℂ * ⟪u, u'⟫_ℂ := by
  have hinv : ∀ g (v : H), σ g (σ g⁻¹ v) = v := by
    intro g v
    rw [← ContinuousLinearMap.mul_apply, ← map_mul]
    simp
  have hSin : ∀ v x, ⟪v, ((ContinuousLinearMap.adjoint T) ∘L T') x⟫_ℂ = ⟪T v, T' x⟫_ℂ := by
    intro v x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  have hcomm : ∀ g, (ContinuousLinearMap.adjoint T) ∘L T' * σ g = σ g * ((ContinuousLinearMap.adjoint T) ∘L T') := by
    intro g
    refine ContinuousLinearMap.ext fun x => ?_
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hSin]
    have h1 : T v = R g (T (σ g⁻¹ v)) := by
      have := congrArg (fun F : H →L[ℂ] L => F (σ g⁻¹ v)) (hT g)
      simp only [ContinuousLinearMap.comp_apply, hinv] at this
      exact this
    have h2 : T' (σ g x) = R g (T' x) := by
      have := congrArg (fun F : H →L[ℂ] L => F x) (hT' g)
      simpa only [ContinuousLinearMap.comp_apply] using this
    have h3 : ⟪v, σ g (((ContinuousLinearMap.adjoint T) ∘L T') x)⟫_ℂ
        = ⟪σ g⁻¹ v, ((ContinuousLinearMap.adjoint T) ∘L T') x⟫_ℂ := by
      conv_lhs => rw [← hinv g v]
      exact inner_of_norm (σ g) (hσ g) _ _
    rw [h3, hSin, h1, h2, inner_of_norm (R g) (hR g)]
  obtain ⟨c, hc⟩ := GlobalTheory.schur_unitary_irreducible G H σ hσ hirr _ hcomm
  have key : ∀ a b, ⟪T a, T' b⟫_ℂ = c * ⟪a, b⟫_ℂ := by
    intro a b
    rw [← hSin, hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]
    simp
  rw [key, key w w, hww, mul_one]

omit [CompleteSpace H] [CompleteSpace L] in

theorem exists_frame (V : Submodule ℂ (H →L[ℂ] L)) [FiniteDimensional ℂ V] (w : H)
    (hV : ∀ T ∈ V, ∀ T' ∈ V, ∀ u u', ⟪T u, T' u'⟫_ℂ = ⟪T w, T' w⟫_ℂ * ⟪u, u'⟫_ℂ) :
    ∃ T : Fin (Module.finrank ℂ V) → (H →L[ℂ] L), (∀ i, T i ∈ V) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧
      (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ Submodule.span ℂ (Set.range T) = V := by
  classical
  let Φ : V →ₗ[ℂ] L := (ContinuousLinearMap.apply ℂ L w : (H →L[ℂ] L) →ₗ[ℂ] L) ∘ₗ V.subtype
  have hΦ : ∀ T : V, Φ T = (T : H →L[ℂ] L) w := fun T => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    apply Subtype.ext
    refine ContinuousLinearMap.ext fun u => ?_
    have h := hV T T.2 T T.2 u u
    rw [← hΦ, hT, inner_zero_left, zero_mul] at h
    simpa using (inner_self_eq_zero.mp h)
  have hdim : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ V :=
    (LinearEquiv.ofInjective Φ hinj).finrank_eq.symm
  let b := (stdOrthonormalBasis ℂ (LinearMap.range Φ)).reindex (finCongr hdim)
  have he : ∀ x, (((LinearEquiv.ofInjective Φ hinj).symm x : V) : H →L[ℂ] L) w = (x : L) := by
    intro x
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective Φ hinj).apply_symm_apply x)
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  have hin : ∀ i j u u', ⟪(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u,
      (((LinearEquiv.ofInjective Φ hinj).symm (b j) : V) : H →L[ℂ] L) u'⟫_ℂ
      = (if i = j then 1 else 0) * ⟪u, u'⟫_ℂ := by
    intro i j u u'
    rw [hV _ ((LinearEquiv.ofInjective Φ hinj).symm (b i)).2 _ ((LinearEquiv.ofInjective Φ hinj).symm (b j)).2,
      he, he, ← Submodule.coe_inner, orthonormal_iff_ite.mp b.orthonormal i j]
  refine ⟨fun i => (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L),
    fun i => ((LinearEquiv.ofInjective Φ hinj).symm (b i)).2, ?_, ?_, ?_⟩
  · intro i u
    have h : ⟪(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u,
        (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u⟫_ℂ = ⟪u, u⟫_ℂ := by
      rw [hin]
      simp
    have h2 : ‖(((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
    nlinarith [norm_nonneg ((((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L) u), norm_nonneg u]
  · intro i j hij u u'
    rw [hin]
    simp [hij]
  · have hbasis : Submodule.span ℂ (Set.range fun i => (LinearEquiv.ofInjective Φ hinj).symm (b i)) = ⊤ := by
      have := (b.toBasis.map (LinearEquiv.ofInjective Φ hinj).symm).span_eq
      rw [← this, Module.Basis.coe_map, OrthonormalBasis.coe_toBasis]
      rfl
    have hr : Set.range (fun i => (((LinearEquiv.ofInjective Φ hinj).symm (b i) : V) : H →L[ℂ] L))
        = V.subtype '' Set.range (fun i => (LinearEquiv.ofInjective Φ hinj).symm (b i)) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, hbasis, Submodule.map_top, Submodule.range_subtype]

end Abstract

theorem exists_orthonormal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R → ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ (∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0) ∧ Submodule.span ℂ (Set.range T) = B.I.eHom B.σs B.μf B.fund B.R B.Re := by
  intro B d hd hfin hle
  haveI := hfin
  obtain ⟨hU, hI, -, hw, -⟩ := GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree B d hd
  obtain ⟨h1, hmul, hnorm, -⟩ := hU
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs, map_one' := h1, map_mul' := fun a b => hmul a b }
  have hR := (GlobalTheory.RightRegFund.rightReg_unitary_continuous B).2.2.1
  have hirr : ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ u ∈ S, σ g u ∈ S) →
      S = ⊥ ∨ S = ⊤ := by
    intro S hS hSinv
    have hI' : ∀ S : Submodule ℂ B.Hs, IsClosed (S : Set B.Hs) → (∀ g, ∀ v ∈ S, B.σs g v ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
      simpa [IsIrr] using hI
    exact hI' S hS hSinv
  have hV : ∀ T ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, ∀ T' ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, ∀ u u',
      ⟪T u, T' u'⟫_ℂ = ⟪T (B.tens B.w), T' (B.tens B.w)⟫_ℂ * ⟪u, u'⟫_ℂ := by
    intro T hT T' hT' u u'
    exact inner_intertwiners σ (fun g u => hnorm g u) hirr (fun g => B.R (g, 1)) (fun g u => hR (g, 1) u)
      (B.tens B.w) hw T T' (fun g => hle hT g) (fun g => hle hT' g) u u'
  exact exists_frame (B.I.eHom B.σs B.μf B.fund B.R B.Re) (B.tens B.w) hV

end GlobalTheory.IntertwinerFrame
