import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.SdExChar

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv

theorem finDim (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

attribute [local instance] finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem oev_zero : (0 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := Submodule.zero_mem _

theorem oev_add {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x + y ∈ OEv (E := E) v := Submodule.add_mem _ hx hy

theorem oev_smul {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : c • x ∈ OEv (E := E) v :=
  Submodule.smul_mem _ (⟨c, hc⟩ : v.adicCompletionIntegers F) hx

theorem oev_neg {x : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) : -x ∈ OEv (E := E) v :=
  Submodule.neg_mem _ hx

def Osub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  add_mem' := oev_add v
  zero_mem' := oev_zero v
  neg_mem' := oev_neg v

theorem inclR_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, trivial, rfl⟩

theorem exists_gens : ∃ (m : ℕ) (w : Fin m → Fv F v ⊗[F] E), (∀ k, w k ∈ OEv (E := E) v) ∧
    ∀ x ∈ OEv (E := E) v, ∃ c : Fin m → Fv F v, (∀ k, c k ∈ v.adicCompletionIntegers F) ∧
      x = ∑ k, c k • w k := by
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  set w : Fin m → Fv F v ⊗[F] E := fun k => inclR (F := F) (Fv F v) ((s k : 𝓞 E) : E) with hw
  refine ⟨m, w, fun k => inclR_mem v _, fun x hx => ?_⟩
  have hle : Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) ≤
      Submodule.span (v.adicCompletionIntegers F) (Set.range w) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    have ha : a ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      have e : inclR (F := F) (Fv F v) (((a + b : 𝓞 E)) : E) =
          inclR (F := F) (Fv F v) (a : E) + inclR (F := F) (Fv F v) (b : E) := by
        simp [map_add]
      show inclR (F := F) (Fv F v) (((a + b : 𝓞 E)) : E) ∈ _
      rw [e]
      exact Submodule.add_mem _ ha hb
    | smul z a _ ha =>
      have e : inclR (F := F) (Fv F v) (((z • a : 𝓞 E)) : E) =
          ((z : v.adicCompletionIntegers F)) • inclR (F := F) (Fv F v) (a : E) := by
        rw [Int.cast_smul_eq_zsmul]
        simp
      show inclR (F := F) (Fv F v) (((z • a : 𝓞 E)) : E) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ ha
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 (hle hx)
  exact ⟨fun k => (c k : Fv F v), fun k => (c k).2, hc.symm⟩

theorem isCompact_oev : IsCompact (OEv (E := E) v) := by
  obtain ⟨m, w, hw, hx⟩ := exists_gens (E := E) v
  have hK : IsCompact (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) :=
    isCompact_univ_pi fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hcont : Continuous fun c : Fin m → Fv F v => ∑ k, c k • w k :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).smul continuous_const
  have e : OEv (E := E) v = (fun c : Fin m → Fv F v => ∑ k, c k • w k) ''
      (Set.univ.pi fun _ : Fin m => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := hx x h
      exact ⟨c, fun k _ => hc k, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact Submodule.sum_mem _ fun k _ => oev_smul v (hc k trivial) (hw k)
  rw [e]
  exact hK.image hcont

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E,
    ∀ i, IsIntegral ℤ (b i) := by
  classical
  let b0 := Module.finBasis F E
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b0)
  have hu : ∀ i : Fin (Module.finrank F E), IsUnit ((y : F)) := fun _ =>
    isUnit_iff_ne_zero.2 (by exact_mod_cast hy0)
  refine ⟨b0.isUnitSMul hu, fun i => ?_⟩
  have h := hy (b0 i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [Module.Basis.isUnitSMul_apply]
  have e : ((y : F)) • b0 i = y • b0 i := by
    rw [← Int.cast_smul_eq_zsmul F y (b0 i)]
  rw [e]
  exact h

theorem trace_inclR (x : E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      algebraMap F (Fv F v) (Algebra.trace F E x) := by
  have e : Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (inclR (F := F) (Fv F v) x) =
      (Algebra.lmul F E x).baseChange (Fv F v) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a e
    simp [inclR]
  rw [Algebra.trace_apply, e, LinearMap.trace_baseChange]
  rfl

def ib : Module.Basis (Fin (Module.finrank F E)) F E := (exists_intBasis (F := F) (E := E)).choose

theorem ib_int (i : Fin (Module.finrank F E)) : IsIntegral ℤ (ib (F := F) (E := E) i) :=
  (exists_intBasis (F := F) (E := E)).choose_spec i

def bas : Module.Basis (Fin (Module.finrank F E)) (Fv F v) (Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.basis (Fv F v) (ib (F := F) (E := E))

theorem bas_apply (i : Fin (Module.finrank F E)) :
    bas (E := E) v i = inclR (F := F) (Fv F v) (ib (F := F) (E := E) i) := by
  simp [bas, Algebra.TensorProduct.basis_apply, inclR]

theorem bas_mem (i : Fin (Module.finrank F E)) : bas (E := E) v i ∈ OEv (E := E) v := by
  rw [bas_apply]
  exact inclR_mem v ⟨_, ib_int i⟩

theorem smul_bas_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (i : Fin (Module.finrank F E)) : c • bas (E := E) v i ∈ OEv (E := E) v :=
  oev_smul v hc (bas_mem v i)

theorem oev_mem_nhds : OEv (E := E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  set e := (bas (E := E) v).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have ho : IsOpen (e ⁻¹' (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))) :=
    (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _).preimage hc
  refine Filter.mem_of_superset (ho.mem_nhds (by simp [zero_mem])) ?_
  intro x hx
  rw [← (bas (E := E) v).sum_equivFun x]
  exact Submodule.sum_mem _ fun i _ => smul_bas_mem v (hx i trivial) i

theorem isOpen_oev : IsOpen (OEv (E := E) v) :=
  AddSubgroup.isOpen_of_mem_nhds (Osub (E := E) v) (oev_mem_nhds v)

def trC : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin (Module.finrank F E) → Fv F v) where
  toFun y i := Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bas (E := E) v i * y)
  map_add' x y := by funext i; simp [mul_add, map_add]
  map_smul' c x := by funext i; simp [map_smul]

theorem trC_apply (y : Fv F v ⊗[F] E) (i : Fin (Module.finrank F E)) :
    trC (E := E) v y i = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (bas (E := E) v i * y) := rfl

theorem trC_injective : Function.Injective (trC (E := E) v) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  set c := (bas (E := E) v).equivFun y with hc
  set M : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) (Fv F v) :=
    (algebraMap F (Fv F v)).mapMatrix (Algebra.traceMatrix F (ib (F := F) (E := E))) with hM
  have hmv : M.mulVec c = 0 := by
    funext i
    have h1 := congrFun hy i
    rw [trC_apply, ← (bas (E := E) v).sum_equivFun y, Finset.mul_sum] at h1
    simp only [mul_smul_comm, map_sum, map_smul, smul_eq_mul] at h1
    rw [Pi.zero_apply] at h1
    rw [Pi.zero_apply, ← h1, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bas_apply, bas_apply, ← map_mul, trace_inclR, mul_comm]
    simp [hM, Algebra.traceMatrix_apply, Algebra.traceForm_apply, hc]
  have hdet : M.det ≠ 0 := by
    rw [hM, ← RingHom.map_det, ← Algebra.discr_def]
    exact (map_ne_zero _).2 (Algebra.discr_not_zero_of_basis F _)
  have h0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  rw [← (bas (E := E) v).sum_equivFun y]
  simp [← hc, h0]

theorem trC_bijective : Function.Bijective (trC (E := E) v) := by
  refine ⟨trC_injective v, ?_⟩
  rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact trC_injective v
  · rw [Module.finrank_eq_card_basis (bas (E := E) v), Module.finrank_fin_fun, Fintype.card_fin]

def trE : (Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin (Module.finrank F E) → Fv F v) :=
  LinearEquiv.ofBijective (trC (E := E) v) (trC_bijective v)

theorem trE_apply (y : Fv F v ⊗[F] E) : trE (E := E) v y = trC (E := E) v y := rfl

theorem continuous_trE : Continuous (trE (E := E) v) :=
  IsModuleTopology.continuous_of_linearMap (trE (E := E) v).toLinearMap

theorem continuous_trE_symm : Continuous (trE (E := E) v).symm :=
  IsModuleTopology.continuous_of_linearMap (trE (E := E) v).symm.toLinearMap

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
