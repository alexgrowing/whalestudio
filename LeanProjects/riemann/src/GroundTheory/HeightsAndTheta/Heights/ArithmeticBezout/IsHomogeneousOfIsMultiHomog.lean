import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem squarefree_of_isChowForm {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) : Squarefree f := by
  rintro x ⟨h, rfl⟩
  have hxh : x * x * h ∣ x * h := by
    refine (hf.2 (x * h)).1 fun u hu => ?_
    have h0 := (hf.2 (x * x * h)).2 dvd_rfl u hu
    simp only [map_mul] at h0 ⊢
    have h2 : aeval u x * aeval u h * (aeval u x * aeval u h) = 0 := by
      calc _ = aeval u x * aeval u x * aeval u h * aeval u h := by ring
        _ = 0 := by rw [h0, zero_mul]
    exact mul_self_eq_zero.mp h2
  have hne : x * h ≠ 0 := fun h0 => hf.1 (by rw [mul_assoc, h0, mul_zero])
  have h1 : x * (x * h) ∣ 1 * (x * h) := by rwa [one_mul, ← mul_assoc]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).mp h1)

theorem isHomogeneous_of_isMultiHomog {n : ℕ} {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : s.IsHomogeneous (a ()) := by
  intro m hm
  rw [← hs m (mem_support_iff.mpr hm) ()]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sigma]

section Homog

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_genericIdeal {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hS, rfl⟩ := hP.2.1.2.1
  let E : MRing (PBlk n) ≃+* MvPolynomial (Fin n) ℤ :=
    (renameEquiv ℤ (Equiv.uniqueSigma (PBlk n))).toRingEquiv
  have hfin : IndefiniteRowSideFullHecke.ArithBezout.finIdeal (Ideal.span S) = (Ideal.span S).map E := by
    rw [← Ideal.comap_symm]
    rfl
  have hhom : IsHomogIdeal (IndefiniteRowSideFullHecke.ArithBezout.finIdeal (Ideal.span S)) := by
    rw [isHomogIdeal_iff, hfin, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr
      ((isHomogeneous_of_isMultiHomog ha).rename_isHomogeneous)⟩
  exact isHomogIdeal_map (Int.castRingHom ℚ) hhom

end Homog

theorem ChowFormToComplexChowForm.proof (hZ : IncidenceZeroLocus.Statement) : ChowFormToComplexChowForm.Statement := by
  intro n e δ P f hP hf hδ
  have hcast : Rat.castHom ℂ = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hC := ChowFormExtend.isChowForm_map (L := ℂ) RadicalBaseChange.proof (genericIdeal P) f hf
  rw [← hcast] at hC
  refine ⟨(isMultihomog_map_iff (Rat.castHom ℂ).injective f).mpr ((isMultiHomog_iff f).mp hδ),
    squarefree_of_isChowForm hC, fun u => ⟨fun hu => ?_, fun ⟨z, hz, hzu⟩ => ?_⟩⟩
  ·
    have hv : ∀ g ∈ incIdeal (genericIdeal P) (e + 1), aeval (fun p => u p.1 p.2) g = 0 := by
      intro g hg
      simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 fun w hw => hg w hw
      rw [map_mul, aeval_def, ← hcast, ← eval_map, hu, zero_mul]
    obtain ⟨y, hy0, hyQ, hyu⟩ := hZ ℚ n (e + 1) (genericIdeal P) (isHomogIdeal_genericIdeal hP) ℂ
      (fun p => u p.1 p.2) hv
    refine ⟨y, ⟨hy0, fun q hq => ?_⟩, fun j => hyu j⟩
    rw [eval_map, RingHom.ext_int (Int.castRingHom ℂ) ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)),
      ← eval₂_map, ← aeval_def]
    exact hyQ _ (Ideal.mem_map_of_mem _ hq)
  ·
    set ι := algebraMap ℂ (AlgebraicClosure ℂ)
    have hle : (genericIdeal P).map (map (Rat.castHom ℂ)) ≤
        RingHom.ker (aeval (ι ∘ z) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] AlgebraicClosure ℂ) := by
      rw [genericIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, map_map,
        RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
        aeval_algebraMap_apply]
      exact (congrArg ι (hz.2 q hq)).trans (map_zero ι)
    have h1 := (hC.2 (map (Rat.castHom ℂ) f)).2 dvd_rfl (ι ∘ fun p => u p.1 p.2)
      ⟨ι ∘ z, fun h0 => hz.1 (funext fun i => ι.injective (by simpa using congrFun h0 i)),
        fun g hg => hle hg, fun j => by simpa [map_sum, map_mul] using congrArg ι (hzu j)⟩
    rw [aeval_algebraMap_apply] at h1
    exact ι.injective (h1.trans (map_zero ι).symm)

end ObjectsChow

end GroundTheory.Heights₂.Heights
