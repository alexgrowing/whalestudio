import Mathlib
import Formalism.PeriodIntegrals.ProdFormulaE

noncomputable section

open ValuativeRel

namespace PI.ProdFormulaE.ROpen

theorem isOpen_addSubgroup {G : Type*} [TopologicalSpace G] [AddCommGroup G] [ContinuousAdd G]
    (H : AddSubgroup G) (U : Set G) (hU : IsOpen U) (h0 : (0 : G) ∈ U) (hUH : U ⊆ H) :
    IsOpen (H : Set G) := by
  exact H.isOpen_of_mem_nhds (Filter.mem_of_superset (hU.mem_nhds h0) hUH)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem isOpen_integer : IsOpen ((𝒪[F] : Subring F) : Set F) :=
  Valuation.isOpen_integer (v := ValuativeRel.valuation F)

theorem isOpen_O (L : Formalism.MainNotions.S.Loc.LocE F E) : IsOpen (L.O : Set E) := by
  classical
  haveI := L.top
  haveI := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  haveI : ContinuousAdd E := by
    first
      | exact IsModuleTopology.toContinuousAdd F E
      | exact inferInstance
      | (rw [IsModuleTopology.eq_moduleTopology F E]; exact ModuleTopology.continuousAdd F E)
  set b := Module.finBasis F E
  have hint : ∀ i, ∃ d : 𝒪[F], d ≠ 0 ∧ IsIntegral 𝒪[F] (algebraMap 𝒪[F] E d * b i) := by
    intro i
    have halg : IsAlgebraic 𝒪[F] (b i) :=
      (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 (Algebra.IsIntegral.isIntegral (b i)).isAlgebraic
    obtain ⟨d, hd, hdi⟩ := halg.exists_integral_multiple
    exact ⟨d, hd, by simpa [Algebra.smul_def] using hdi⟩
  choose d hd0 hdi using hint
  set D : 𝒪[F] := ∏ i, d i with hD
  have hDint : ∀ i, IsIntegral 𝒪[F] (algebraMap 𝒪[F] E D * b i) := by
    intro i
    rw [hD, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_assoc]
    exact (isIntegral_algebraMap).mul (hdi i)
  let f : E →ₗ[F] (Fin (Module.finrank F E) → F) := b.equivFun.toLinearMap
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  let U : Set E := f ⁻¹' Set.pi Set.univ (fun _ => (fun c : F => c * ((D : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F))
  have hcont : Continuous (fun c : F => c * ((D : 𝒪[F]) : F)⁻¹) := continuous_id.mul continuous_const
  have hUo : IsOpen U := hf.isOpen_preimage _
    (isOpen_set_pi Set.finite_univ fun _ _ => hcont.isOpen_preimage _ isOpen_integer)
  refine isOpen_addSubgroup L.O.toAddSubgroup U hUo ?_ ?_
  · intro i _
    simp [U, f]
  · intro x hx
    have hx' : ∀ i, b.repr x i * ((D : 𝒪[F]) : F)⁻¹ ∈ 𝒪[F] := fun i => hx i (Set.mem_univ i)
    show x ∈ L.O
    rw [← b.sum_repr x]
    refine Subring.sum_mem _ fun i _ => ?_
    have hD0 : ((D : 𝒪[F]) : F) ≠ 0 := by
      rw [hD]
      push_cast
      exact Finset.prod_ne_zero_iff.2 fun j _ => by exact_mod_cast hd0 j
    have e : b.repr x i • b i = algebraMap 𝒪[F] E ⟨_, hx' i⟩ * (algebraMap 𝒪[F] E D * b i) := by
      rw [← mul_assoc, ← map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]
      congr 2
      show b.repr x i = b.repr x i * ((D : 𝒪[F]) : F)⁻¹ * ((D : 𝒪[F]) : F)
      rw [mul_assoc, inv_mul_cancel₀ hD0, mul_one]
    rw [e]
    exact L.O.mul_mem ((L.O_def _).2 isIntegral_algebraMap) ((L.O_def _).2 (hDint i))

theorem isOpen_R [MeasurableSpace E] (M : Formalism.MainNotions.S.Loc.Model F E) : IsOpen (M.R : Set E) := by
  classical
  haveI := M.L.top
  haveI : ContinuousAdd E := by
    first
      | exact IsModuleTopology.toContinuousAdd F E
      | exact inferInstance
  rcases hs : M.split with _ | g
  · have hR : M.R = M.L.O := by
      simp only [Formalism.MainNotions.S.Loc.Model.R, hs]
    rw [hR]
    exact isOpen_O M.L
  · have hq0 : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h
      exact g.q_irr.ne_zero (Subtype.ext h)
    have he : Continuous g.e := IsModuleTopology.continuous_of_linearMap g.e.toLinearMap
    have hV : IsOpen ((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)) :=
      (continuous_id.mul continuous_const).isOpen_preimage _ isOpen_integer
    have hU : IsOpen (g.e ⁻¹' (((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)) ×ˢ
        ((fun c : F => c * ((g.q : 𝒪[F]) : F)⁻¹) ⁻¹' (𝒪[F] : Set F)))) :=
      he.isOpen_preimage _ (hV.prod hV)
    refine isOpen_addSubgroup M.R.toAddSubgroup _ hU ?_ ?_
    · simp
    · intro x hx
      obtain ⟨h1, h2⟩ := hx
      simp only [Set.mem_preimage] at h1 h2
      have m1 : (g.e x).1 ∈ 𝒪[F] := by
        have : (g.e x).1 = (g.e x).1 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) := by
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
        rw [this]
        exact Subring.mul_mem _ h1 (g.q).2
      have m2 : (g.e x).2 ∈ 𝒪[F] := by
        have : (g.e x).2 = (g.e x).2 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) := by
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one]
        rw [this]
        exact Subring.mul_mem _ h2 (g.q).2
      have z1 : (⟨(g.e x).1, m1⟩ : 𝒪[F]) ∈ Ideal.span {g.q} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨_, h1⟩, Subtype.ext (by
          show (g.e x).1 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) = (g.e x).1
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one])⟩
      have z2 : (⟨(g.e x).2, m2⟩ : 𝒪[F]) ∈ Ideal.span {g.q} := by
        rw [Ideal.mem_span_singleton']
        exact ⟨⟨_, h2⟩, Subtype.ext (by
          show (g.e x).2 * ((g.q : 𝒪[F]) : F)⁻¹ * ((g.q : 𝒪[F]) : F) = (g.e x).2
          rw [mul_assoc, inv_mul_cancel₀ hq0, mul_one])⟩
      show x ∈ (M.R : Set E)
      simp only [Formalism.MainNotions.S.Loc.Model.R, hs]
      rw [SetLike.mem_coe, Subring.mem_comap, Subring.mem_map]
      refine ⟨(⟨(g.e x).1, m1⟩, ⟨(g.e x).2, m2⟩), ?_, rfl⟩
      show _ = _
      show Ideal.Quotient.mk (Ideal.span {g.q}) (⟨(g.e x).1, m1⟩ : 𝒪[F]) =
        Ideal.Quotient.mk (Ideal.span {g.q}) (⟨(g.e x).2, m2⟩ : 𝒪[F])
      rw [(Ideal.Quotient.eq_zero_iff_mem).2 z1, (Ideal.Quotient.eq_zero_iff_mem).2 z2]

end PI.ProdFormulaE.ROpen

end
