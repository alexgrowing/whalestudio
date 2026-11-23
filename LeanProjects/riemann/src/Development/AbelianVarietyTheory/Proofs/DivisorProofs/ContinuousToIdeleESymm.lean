import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Adele.IntegersLattice
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeckeAbsArch

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem archUnitF_add (c d : ℝ) : archUnitF F (c + d) = archUnitF F c * archUnitF F d := by
  refine Units.ext (Prod.ext ?_ (mul_one _).symm)
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ =
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
  rw [← map_mul]
  congr 1
  refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
  · simp [Real.exp_add]
  · simp [Real.exp_add]

theorem archUnit_add (c d : ℝ) : archUnit F E (c + d) = archUnit F E c * archUnit F E d := by
  rw [archUnit, archUnitF_add, map_mul]
  rfl

theorem continuous_mixed_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = (homeomorphMixedSpace F).symm := funext fun p => by
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    rw [RingEquiv.apply_symm_apply, ← homeomorphMixedSpace_apply, Homeomorph.apply_symm_apply]
  rw [h]
  exact (homeomorphMixedSpace F).symm.continuous

theorem continuous_archUnitF : Continuous (archUnitF F) := by
  have hp : ∀ s : ℝ, Continuous fun c : ℝ => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (fun _ => Real.exp (s * c), fun _ => ((Real.exp (s * c) : ℝ) : ℂ)) := fun s =>
    continuous_mixed_symm.comp ((continuous_pi fun _ => by fun_prop).prodMk (continuous_pi fun _ => by fun_prop))
  rw [Units.continuous_iff]
  constructor
  · refine ((hp 1).prodMk (continuous_const (y := (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))).congr fun c => ?_
    simp only [one_mul]
    rfl
  · refine ((hp (-1)).prodMk (continuous_const (y := (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))).congr fun c => ?_
    simp only [neg_one_mul]
    rfl

theorem continuous_archUnit : Continuous (archUnit F E) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  exact (Continuous.units_map _ h).comp continuous_archUnitF

def toIdeleE : (AF F ⊗[F] E)ˣ ≃* IdeleGroup E :=
  Units.mapEquiv (adeleTensorAlgEquivLeft F E).toRingEquiv.toMulEquiv

theorem continuous_toIdeleE : Continuous (toIdeleE (F := F) (E := E)) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : Continuous (adeleTensorAlgEquivLeft F E) :=
    IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearEquiv.toLinearMap
  exact Continuous.units_map ((adeleTensorAlgEquivLeft F E).toRingEquiv.toMulEquiv.toMonoidHom) h

theorem continuous_toIdeleE_symm : Continuous (toIdeleE (F := F) (E := E)).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : Continuous (adeleTensorAlgEquivLeft F E).symm :=
    IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearEquiv.toLinearMap
  exact Continuous.units_map ((adeleTensorAlgEquivLeft F E).symm.toRingEquiv.toMulEquiv.toMonoidHom) h

theorem toIdeleE_inclR (e : Eˣ) :
    toIdeleE (Units.map (inclR (F := F) (AF F)).toMonoidHom e) = IdeleGroup.diagonal E e := by
  apply Units.ext
  change adeleTensorAlgEquivLeft F E ((1 : AF F) ⊗ₜ[F] (e : E)) = _
  rw [adeleTensorAlgEquivLeft_tmul, map_one, mul_one, IdeleGroup.coe_diagonal]

theorem eq_zero_of_normOne (g : (AF F ⊗[F] E)ˣ → ℝ) (hg : Continuous g) (hmul : ∀ a b, g (a * b) = g a + g b)
    (hprin : ∀ e : Eˣ, g (Units.map (inclR (F := F) (AF F)).toMonoidHom e) = 0) (y : (AF F ⊗[F] E)ˣ)
    (hy : toIdeleE y ∈ IdeleGroup.normOneSubgroup E) : g y = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn (hg.comp continuous_toIdeleE_symm).continuousOn
  have h1 : g 1 = 0 := by have := hmul 1 1; rw [mul_one] at this; linarith
  have hpow : ∀ n : ℕ, g (y ^ n) = n * g y := by
    intro n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ, hmul, ih]; push_cast; ring
  have key : ∀ n : ℕ, |(n : ℝ) * g y| ≤ B := by
    intro n
    obtain ⟨k, hk⟩ := hxD (toIdeleE (y ^ n)) (by rw [map_pow]; exact pow_mem hy n)
    have e1 : toIdeleE.symm (IdeleGroup.diagonal E k * toIdeleE (y ^ n)) =
        Units.map (inclR (F := F) (AF F)).toMonoidHom k * y ^ n := by
      rw [map_mul, MulEquiv.symm_apply_apply, ← toIdeleE_inclR (F := F) k, MulEquiv.symm_apply_apply]
    have := hB _ hk
    rw [Function.comp_apply, e1, hmul, hprin, zero_add, hpow, Real.norm_eq_abs] at this
    exact this
  by_contra hne
  have hpos : 0 < |g y| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (B / |g y|)
  have h2 := key n
  rw [abs_mul, Nat.abs_cast] at h2
  have h3 := (div_lt_iff₀ hpos).1 hn
  linarith

theorem absE_archUnit {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (c : ℝ) :
    (absE F E (archUnit F E c) : ℝ) = Real.exp (2 * Module.finrank ℚ F * c) := by
  haveI := hσ.1
  have hN : Algebra.norm (AF F) ((archUnit F E c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((archUnitF F c : (AF F)ˣ) : AF F) ^ 2 := by
    change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (archUnitF F c : AF F)) = _
    rw [Algebra.norm_algebraMap, Module.finrank_baseChange, hσ.2.2.1]
  have hinf : ∀ w : InfinitePlace F, ‖evInf F w ((archUnitF F c : (AF F)ˣ) : AF F)‖ = Real.exp c := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    have h := congrArg (fun p => p.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
      (fun _ => Real.exp c, fun _ => ((Real.exp c : ℝ) : ℂ)))
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
    change ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (fun _ => Real.exp c, fun _ => ((Real.exp c : ℝ) : ℂ)) w‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), h,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos c)]
  have hfin : ∀ v, evFin F v ((archUnitF F c : (AF F)ˣ) : AF F) = 1 := fun v => rfl
  rw [GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEw_unitInf, GlobalTheory.Doubling.absEv_unitFin, hN, map_pow, hfin, one_pow, nnnorm_one,
    finprod_one, mul_one, NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm, norm_pow, hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

end GlobalTheory.HeckeAbsArch
