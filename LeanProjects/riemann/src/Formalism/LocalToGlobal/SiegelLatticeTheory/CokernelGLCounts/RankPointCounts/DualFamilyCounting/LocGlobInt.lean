import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensAtGoodOf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt.DualityBasisChange

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_integer_iff_vle {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (v := valuation K)).symm

theorem mem_OF_of_loc (D : Formalism.BasicNotions.D7) (s : D.host.F)
    (hs : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E s) ∈ (D.s.atP p).O) :
    s ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F s fun p => ?_
  have h1 := hs p
  rw [(D.s.atP p).compat] at h1
  have hint := ((D.s.atP p).O_def _).1 h1
  have hnt : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hinj : Function.Injective (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) := by
    haveI := hnt; exact (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
  have h2 : (D.s.atP p).ιF s ∈ 𝒪[(D.s.atP p).Fp] :=
    PI.IntegralDiscriminantMembership.mem_integer_of_isIntegral ((isIntegral_algebraMap_iff hinj).1 hint)
  rw [mem_integer_iff_vle, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one] at h2
  exact h2

theorem locGlobIntE : LocGlobIntE := by
  intro D x hx
  have hcjO : ∀ p : PlF D, (D.s.atP p).ιE (star x) ∈ (D.s.atP p).O := fun p => by
    rw [PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, ← (D.s.atP p).cj_ιE, (D.s.atP p).O_def]
    exact ((D.s.atP p).O_def _).1 (hx p) |>.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])
  obtain ⟨t, ht⟩ := (D.sp.cm.fixed (x + star x)).1 (by rw [star_add, star_star, add_comm])
  obtain ⟨n, hn⟩ := (D.sp.cm.fixed (x * star x)).1 (by rw [star_mul, star_star, mul_comm])
  obtain ⟨t', ht'⟩ := mem_OF_of_loc D t fun p => by
    rw [ht, map_add]; exact (D.s.atP p).O.add_mem (hx p) (hcjO p)
  obtain ⟨n', hn'⟩ := mem_OF_of_loc D n fun p => by
    rw [hn, map_mul]; exact (D.s.atP p).O.mul_mem (hx p) (hcjO p)

  have hT : IsIntegral ℤ (x + star x) := by
    rw [← ht, ← ht']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral t'))
  have hN : IsIntegral ℤ (x * star x) := by
    rw [← hn, ← hn']
    exact map_isIntegral_int (algebraMap D.host.F D.host.E) (map_isIntegral_int _ (RingOfIntegers.isIntegral n'))
  set a : 𝓞 D.host.E := ⟨x + star x, hT⟩
  set b : 𝓞 D.host.E := ⟨x * star x, hN⟩
  have hx' : IsIntegral (𝓞 D.host.E) x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C b, by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    show x ^ 2 - (x + star x) * x + x * star x = 0
    ring
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  exact Submodule.mem_one.2 ⟨y, hy⟩

theorem not_integral_density_of_self_dual (h1 : LocSelfDual) (hF : FrameBasisL) : NotIntDens :=
  notIntDens_of_steps h1 hF locGlobIntE

end Formalism.L2.SG.Pf.Cnt.DualityBasisChange
