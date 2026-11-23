import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IntConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

theorem L2GramLattice.proof : L2GramLattice.Statement := by
  intro E _ _ _ X _ μ _ w hmeas hbdd hind
  classical
  set n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  have hmem : ∀ s, MemLp (w s) 2 μ := fun s => by
    obtain ⟨C, hC⟩ := hbdd s
    exact (memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top
  let F : Fin n → Lp ℂ 2 μ := fun i => (hmem (b i)).toLp _
  let ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun c => ∑ i, c i • F i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

  have hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z := by
    intro c
    show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h
      rw [h]
      rfl
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i),
        (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hind n b b.linearIndependent c
    filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2
    rw [← h1]
    exact h2

  have hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _ := by
    intro s
    ext1
    filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2
    have hs : w s = ∑ i, b.repr s i • w (b i) := by
      conv_lhs => rw [← b.sum_repr s]
      rw [map_sum]
      simp only [map_zsmul]
    rw [h1, h2, hs, Finset.sum_apply]
    simp [zsmul_eq_mul]
  let W := LinearMap.range ψ
  let e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective ψ hinj
  have hW : Module.finrank ℝ W = n := by
    rw [← e₁.finrank_eq, Module.finrank_fin_fun]
  let o := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  let T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := e₁.trans o.repr.toLinearEquiv
  have hT : ∀ c, ‖T c‖ = ‖ψ c‖ := by
    intro c
    simp only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]
    rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)
  let φ : E →+ EuclideanSpace ℝ (Fin n) :=
    (T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ)) := fun s => rfl
  let v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Pi.basisFun ℝ (Fin n)).map T
  have hφb : ∀ i, φ (b i) = v i := by
    intro i
    rw [hφ]
    simp only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]
    congr 1
    funext j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hL : imageLattice φ = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      rw [← b.sum_repr s, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, hφb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, hφb i⟩
  have key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) →
      DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
    rintro _ rfl
    exact ⟨inferInstance, by intro _; infer_instance⟩
  refine ⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩
  · intro s t hst
    rw [hφ, hφ] at hst
    apply b.equivFun.injective
    funext i
    exact_mod_cast congrFun (T.injective hst) i
  · intro s
    rw [hφ, hT, hcoord, Lp.norm_toLp,
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
