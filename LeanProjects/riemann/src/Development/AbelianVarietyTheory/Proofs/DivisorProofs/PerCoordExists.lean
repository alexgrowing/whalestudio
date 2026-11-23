import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapOneInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinearStatement

open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj det_ne_zero_of_pos colMat exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

theorem coords_sum {d : ℕ} (π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ)) (S : Matrix (Fin g) (Fin g) ℂ) (k : Fin d) :
    π S k = ∑ i, ∑ j, S i j * π (Matrix.single i j 1) k := by
  conv_lhs => rw [matrix_eq_sum_single S]
  simp only [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (S i j) = S i j • Matrix.single i j (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, Pi.smul_apply, smul_eq_mul]

theorem perCoord_exists : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar), ∃ d, PerCoord D ρ d := by
  intro O _ bar g ρ D
  classical
  refine ⟨Module.finrank ℂ (Tsp bar ρ), fun P₀ hP₀ => ?_⟩
  set d := Module.finrank ℂ (Tsp bar ρ)
  let bV := Module.finBasis ℂ (Tsp bar ρ)
  obtain ⟨p, hp⟩ := (Tsp bar ρ).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let ι : (Fin d → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := (Tsp bar ρ).subtype ∘ₗ bV.equivFun.symm.toLinearMap
  let π : Matrix (Fin g) (Fin g) ℂ →ₗ[ℂ] (Fin d → ℂ) := bV.equivFun.toLinearMap ∘ₗ p
  have hιeq : ∀ b, ι b = ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) := fun b => rfl
  have hιT : ∀ b, ι b ∈ Tsp bar ρ := fun b => by rw [hιeq]; exact Submodule.coe_mem _
  have hpv : ∀ v : Tsp bar ρ, p ((Tsp bar ρ).subtype v) = v := fun v => LinearMap.congr_fun hp v
  have hπι : ∀ b, π (ι b) = b := fun b => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show ((bV.equivFun.symm b : Tsp bar ρ) : Matrix (Fin g) (Fin g) ℂ) = (Tsp bar ρ).subtype (bV.equivFun.symm b) from rfl, hpv, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ S ∈ Tsp bar ρ, ι (π S) = S := fun S hS => by
    rw [hιeq]; simp only [π, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show S = (Tsp bar ρ).subtype ⟨S, hS⟩ from rfl, hpv, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨α, β, hαβ⟩ := exists_colMat_per hP₀
  obtain ⟨M₀, hM₀h, hpos₀, hM₀⟩ := hP₀.2.2.2.2
  have hdet₀ : M₀.det ≠ 0 := det_ne_zero_of_pos hpos₀
  have hu₀ : IsUnit M₀.det := isUnit_iff_ne_zero.2 hdet₀
  have hA₀ : colMat α P₀ = 1 ∧ colMat β P₀ = 0 :=
    realMap_inj (ext_per hP₀ fun x => by rw [← hαβ P₀ hP₀]; simp [realMap_apply])
  let Cf : (D.La → Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun f => (colMat α f)⁻¹ * colMat β f
  let Z : (D.La →+ (Fin g → ℂ)) → (Fin d → ℂ) := fun P => π ((Cf P)ᵀ * M₀)
  let Cof : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => (ι b * M₀⁻¹)ᵀ
  let Q : (Fin d → ℂ) → (D.La →+ (Fin g → ℂ)) := fun b => (realMap 1 (Cof b)).toAddMonoidHom.comp P₀
  have hQ : ∀ b x, Q b x = realMap 1 (Cof b) (P₀ x) := fun b x => rfl
  have hCofT : ∀ b, (Cof b)ᵀ * M₀ = ι b := fun b => by
    simp only [Cof, transpose_transpose, nonsing_inv_mul_cancel_right _ _ hu₀]
  obtain ⟨U, hUg, hUo, hU0⟩ := mem_nhds_iff.1 (GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix M₀ hpos₀)
  have hQper : ∀ b, Cof b ∈ U → IsPeriod D ρ (Q b) := fun b hb => by
    obtain ⟨hY, hX, hpos⟩ := hUg hb
    have hT : (Cof b)ᵀ * M₀ ∈ Tsp bar ρ := by rw [hCofT]; exact hιT b
    obtain ⟨hMh, hMim⟩ := GlobalTheory.T.riemann_relation_converse_conjAffine M₀ (Cof b) hM₀h hdet₀ hT.1 hY
    refine GlobalTheory.T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (Cof b)) _ hP₀ (realMap_one_injective hX) (fun a x => ?_) hMh hpos (fun x y => ?_)
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, star_mulVec_map, mulVec_mulVec,
        ← comm_of_mem_Tsp hP₀ hM₀ hdet₀ hT a, ← mulVec_mulVec, mulVec_add]
    · rw [realMap_apply, realMap_apply, one_mulVec, one_mulVec, hMim, hM₀]
  have hCofc : Continuous Cof := by
    exact (Continuous.matrix_mul ι.continuous_of_finiteDimensional continuous_const).matrix_transpose
  have hCof0 : Cof 0 = 0 := by simp [Cof, ι]
  have hZ0 : Z P₀ = 0 := by simp [Z, Cf, hA₀]
  have hcol : ∀ γ : Fin g → (D.La →₀ ℂ), Continuous fun f : D.La → Fin g → ℂ => colMat γ f := fun γ =>
    continuous_matrix fun i j => by simp only [colMat, of_apply]; fun_prop
  have hCfc : ContinuousAt Cf ⇑P₀ := by
    refine ContinuousAt.mul ?_ (hcol β).continuousAt
    refine ContinuousAt.comp (f := fun f => colMat α f) ?_ (hcol α).continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [hA₀.1, det_one]
    exact (Ring.inverse_eq_inv' (G₀ := ℂ)) ▸ continuousAt_inv₀ one_ne_zero
  have hCf0 : Cf P₀ = 0 := by simp [Cf, hA₀]
  have hdetc : Continuous fun f : D.La → Fin g → ℂ => (colMat α f).det := (hcol α).matrix_det
  obtain ⟨s, ε, hε, hs⟩ := exists_finset_of_mem_nhds
    ((hdetc.continuousAt (x := ⇑P₀)).eventually_ne (show (colMat α P₀).det ≠ 0 by simp [hA₀.1]) |>.and
      (hCfc.preimage_mem_nhds (hUo.mem_nhds (by rw [hCf0]; exact hU0))))
  refine ⟨Cof ⁻¹' U, Q, Z, s, ε, hUo.preimage hCofc, hε, ⟨fun b hb => hQper b hb, fun x => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let F : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => Cof b *ᵥ star (P₀ x)
        map_add' := fun b b' => by simp only [Cof, map_add, Matrix.add_mul, transpose_add, add_mulVec]
        map_smul' := fun c b => by
          simp only [Cof, map_smul, Matrix.smul_mul, transpose_smul, smul_mulVec, RingHom.id_apply] }
    have hF : Differentiable ℂ (fun b => F b) := (LinearMap.toContinuousLinearMap F).differentiable
    refine ((differentiableOn_const (P₀ x)).add hF.differentiableOn).congr fun b _ => ?_
    rw [hQ, realMap_apply, one_mulVec]; rfl
  · show Cof (Z P₀) ∈ U
    rw [hZ0, hCof0]; exact hU0
  · ext x
    rw [hZ0, hQ, hCof0, realMap_apply, one_mulVec, zero_mulVec, add_zero]
  · intro b hb _
    have h1 := hαβ (Q b) (hQper b hb)
    have key : colMat α (Q b) = 1 ∧ colMat β (Q b) = Cof b :=
      realMap_inj (ext_per hP₀ fun x => by rw [← h1 x, hQ])
    show π (((colMat α (Q b))⁻¹ * colMat β (Q b))ᵀ * M₀) = b
    rw [key.1, key.2, inv_one, Matrix.one_mul, hCofT, hπι]
  · intro P hP hn
    obtain ⟨hdetA, hCU⟩ := hs _ hn
    have hu : IsUnit (colMat α P).det := isUnit_iff_ne_zero.2 hdetA
    have hT := mem_Tsp_of_period hP₀ hP hM₀ (hαβ P hP) hdetA
    have hCofZ : Cof (Z P) = Cf P := by
      show (ι (π ((Cf P)ᵀ * M₀)) * M₀⁻¹)ᵀ = Cf P
      rw [hιπ _ hT, mul_nonsing_inv_cancel_right _ _ hu₀, transpose_transpose]
    refine ⟨show Cof (Z P) ∈ U by rw [hCofZ]; exact hCU, Matrix.toLinearEquiv' _ (invertibleOfIsUnitDet _ hu),
      fun x => ?_⟩
    rw [hQ, hCofZ]
    change P x = colMat α P *ᵥ realMap 1 ((colMat α P)⁻¹ * colMat β P) (P₀ x)
    rw [hαβ P hP x, realMap_apply, realMap_apply, one_mulVec, mulVec_add, mulVec_mulVec,
      mul_nonsing_inv_cancel_left _ _ hu]
  · intro P P' hP hP' _ _ h hh
    let H := LinearMap.toMatrix' h.toLinearMap
    have hHv : ∀ v, h v = H *ᵥ v := fun v => (LinearMap.toMatrix'_mulVec _ v).symm
    have hHinv : LinearMap.toMatrix' h.symm.toLinearMap * H = 1 := by
      rw [← LinearMap.toMatrix'_comp, show h.symm.toLinearMap ∘ₗ h.toLinearMap = LinearMap.id from
        LinearMap.ext fun v => h.symm_apply_apply v, LinearMap.toMatrix'_id]
    have hHu : IsUnit H.det := isUnit_det_of_left_inverse hHinv
    have key : colMat α P' = H * colMat α P ∧ colMat β P' = H * colMat β P :=
      realMap_inj (ext_per hP₀ fun x => by
        rw [← hαβ P' hP' x, hh x, hαβ P hP x, hHv]
        simp only [realMap_apply, mulVec_add, mulVec_mulVec])
    show π (((colMat α P')⁻¹ * colMat β P')ᵀ * M₀) = π (((colMat α P)⁻¹ * colMat β P)ᵀ * M₀)
    rw [key.1, key.2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc H⁻¹ H, nonsing_inv_mul _ hHu,
      Matrix.one_mul]
  · intro m B' P _ hP hnear
    have hc : ∀ (γ : Fin g → (D.La →₀ ℂ)) i j, DifferentiableOn ℂ (fun b => colMat γ (P b) i j) B' :=
      fun γ i j => by
        simp only [colMat, of_apply]
        exact DifferentiableOn.fun_sum fun x _ => (differentiableOn_pi.1 (hP.2 x) i).const_mul _
    have hinv := RiemannRel.differentiableOn_left_inverse (fun b => colMat α (P b)) (fun b => (colMat α (P b))⁻¹)
      (hc α) (fun b hb => nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hs _ (hnear b hb)).1))
    refine differentiableOn_pi.2 fun k => ?_
    show DifferentiableOn ℂ (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) B'
    rw [show (fun b => π (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) k) = fun b => ∑ i, ∑ j,
      (((colMat α (P b))⁻¹ * colMat β (P b))ᵀ * M₀) i j * π (Matrix.single i j 1) k from
      funext fun b => coords_sum π _ k]
    simp only [mul_apply, transpose_apply]
    exact DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
      (DifferentiableOn.fun_sum fun l _ => (DifferentiableOn.fun_sum fun n _ =>
        (hinv _ _).mul (hc β _ _)).mul_const _).mul_const _

end

end GlobalTheory.PerCoordU
