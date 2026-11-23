import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F : Type} [Field F] [NumberField F]

variable (F) in

theorem intF_isOpen (M : ℕ) (hM : 0 < M) : IsOpen (intF F M) := by
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  have hS : IsOpen (S : Set (Af F)) :=
    S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM)
  have e : intF F M = Prod.snd ⁻¹' (S : Set (Af F)) := by
    ext x
    constructor
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
    · rintro ⟨c, hc, e⟩
      exact ⟨c, hc, e⟩
  rw [e]
  exact hS.preimage continuous_snd

theorem exists_intF_one_mul (M : ℕ) (hM : 0 < M) {x : AF F} (hx : x ∈ intF F M) :
    ∃ s ∈ intF F 1, (M : AF F) * s = x := by
  obtain ⟨c, hc, e⟩ := hx
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  refine ⟨algebraMap F (AF F) ((M : F)⁻¹) * x, ⟨c, hc, ?_⟩, ?_⟩
  · show (algebraMap F (AF F) ((M : F)⁻¹)).2 * x.2 = 1 • c
    rw [e, one_smul, nsmul_eq_mul]
    have h2 : (algebraMap F (AF F) ((M : F)⁻¹)).2 = algebraMap F (Af F) ((M : F)⁻¹) := rfl
    rw [h2, ← mul_assoc, ← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM', map_one, one_mul]
  · rw [← mul_assoc, ← map_natCast (algebraMap F (AF F)) M, ← map_mul, mul_inv_cancel₀ hM', map_one, one_mul]

end GlobalTheory.HeckeExtend

theorem GlobalTheory.HeckeExtend.CE_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ), 0 < N → IsOpen (CE F E N : Set (AF F ⊗[F] E)) := by
  intro F E _ _ _ _ _ N hN
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b₀ := Module.finBasis F E
  have hint : ∀ i, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * b₀ i) := by
    intro i
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have : Algebra.IsAlgebraic ℤ E := Algebra.IsAlgebraic.trans ℤ ℚ E
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) (z := b₀ i) (Algebra.IsAlgebraic.isAlgebraic _)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h1 : (((y * y).natAbs : ℕ) : E) = (y : E) * (y : E) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y), Int.cast_mul]
    rw [h1, mul_assoc]
    rw [zsmul_eq_mul] at h
    exact (isIntegral_algebraMap (x := y)).mul h
  choose d hd hdint using hint
  let B := Algebra.TensorProduct.basis (AF F) b₀
  let U : Set (AF F ⊗[F] E) := ⋂ i, (fun z => B.repr z i) ⁻¹' intF F (N * d i)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => (intF_isOpen F _ (Nat.mul_pos hN (hd i))).preimage ?_
    exact IsModuleTopology.continuous_of_linearMap (B.coord i)
  have h0 : (0 : AF F ⊗[F] E) ∈ U := by
    refine Set.mem_iInter.2 fun i => ⟨0, fun v => zero_mem _, ?_⟩
    show (B.repr 0 i).2 = (N * d i) • 0
    rw [map_zero, smul_zero]
    rfl
  have hsub : U ⊆ (CE F E N : Set (AF F ⊗[F] E)) := by
    intro z hz
    have hz' : ∀ i, B.repr z i ∈ intF F (N * d i) := fun i => Set.mem_iInter.1 hz i
    choose s hs hsx using fun i => exists_intF_one_mul (N * d i) (Nat.mul_pos hN (hd i)) (hz' i)
    refine mem_CE.2 ⟨∑ i, algebraMap (AF F) (AF F ⊗[F] E) (s i) * incAF F E ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E),
      sum_mem fun i _ => AddSubgroup.subset_closure ⟨s i, hs i, ⟨(d i : E) * b₀ i, hdint i⟩, rfl⟩, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← B.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsx i, Algebra.TensorProduct.basis_apply, nsmul_eq_mul, Algebra.smul_def]
    have h1 : incAF F E ((d i : E) * b₀ i) = (d i : AF F ⊗[F] E) * (1 ⊗ₜ b₀ i) := by
      rw [map_mul, map_natCast]
      rfl
    have hc : ((⟨(d i : E) * b₀ i, hdint i⟩ : 𝓞 E) : E) = (d i : E) * b₀ i := rfl
    rw [hc, h1, map_mul, map_natCast]
    push_cast
    ring
  exact (CE F E N).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (hU.mem_nhds h0) hsub)
