import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PeriodLatticeIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem ClassMeanOverEmbeddings.proof (S : PrimeDiscriminant K) (F : CMFamily K)
    (hMean : MeanOverEmbeddings.Statement S F) (hScale : PhScale.Statement)
    (hConj : PhConj.Statement) : ClassMeanOverEmbeddings.Statement S F := by
  intro σ
  have := S.isTotallyComplex
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

  have hhom : ∀ (τ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : Submodule ℤ ℂ) (c : ℂ),
      c ≠ 0 → (Λ : Set ℂ) = (c * ·) '' idealLattice τ J →
        logPeriod Λ = logPeriod (idealLattice τ J) := by
    intro τ J Λ c hc h
    have e : Λ = scaleLattice c (idealPeriodPair τ hK J).lattice := by
      apply SetLike.coe_injective
      rw [h, scaleLattice, Submodule.map_coe, lattice_idealPeriodPair]
      rfl
    rw [e, hScale _ c hc, lattice_idealPeriodPair]

  have hcls : ∀ (τ : K →+* ℂ) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
      logPeriod (idealLattice τ 𝔟) = classLogPeriod τ (ClassGroup.mk K 𝔟) := by
    intro τ 𝔟
    have hJ : ClassGroup.mk K 𝔟 =
        ClassGroup.mk K (FractionalIdeal.mk0 K (classRep (ClassGroup.mk K 𝔟))) := by
      rw [ClassGroup.mk_mk0, mk0_classGroupRep]
    obtain ⟨c, hc, h⟩ := (classGroup_mk_eq_iff τ hK _ _).1 hJ
    rw [classLogPeriod, classLattice, ← FractionalIdeal.coe_mk0, hhom τ 𝔟 _ c hc h]

  have hconj : ∀ τ : K →+* ℂ, classMean τ = classMean σ := by
    intro τ
    rcases S.eq_or_eq_conjugate σ τ with rfl | rfl
    · rfl
    · unfold classMean
      congr 1
      refine Finset.sum_congr rfl fun C _ ↦ ?_
      rw [classLogPeriod, classLogPeriod, classLattice, classLattice, idealLattice_conjugate,
        ← FractionalIdeal.coe_mk0, ← lattice_idealPeriodPair σ hK, hConj]

  have hs : ∀ s : F.k →+* ℂ, (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K),
      logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
        F.periodLattice s) = classMean σ := by
    intro s
    obtain ⟨I, c, hc, h⟩ := F.exists_periodLattice_eq S s
    have e : ∀ C : ClassGroup (𝓞 K),
        logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
          F.periodLattice s) = classLogPeriod (F.restrict s) (C * ClassGroup.mk K I) := by
      intro C
      have h' := idealLattice_mul_homothetic (F.restrict s) (I : FractionalIdeal (𝓞 K)⁰ K)
        (↑(FractionalIdeal.mk0 K (classRep C))) h
      rw [← Units.val_mul] at h'
      rw [hhom _ _ _ c hc h', hcls, map_mul, ClassGroup.mk_mk0, mk0_classGroupRep]
    rw [Finset.sum_congr rfl fun C _ ↦ e C,
      Fintype.sum_equiv (Equiv.mulRight (ClassGroup.mk K I))
        (fun C ↦ classLogPeriod (F.restrict s) (C * ClassGroup.mk K I)) (classLogPeriod (F.restrict s))
        (fun C ↦ rfl)]
    exact hconj _
  have hN : (Fintype.card (F.k →+* ℂ) : ℝ) ≠ 0 := by
    have : Nonempty (F.k →+* ℂ) := ⟨(IsAlgClosed.lift : F.k →ₐ[ℚ] ℂ).toRingHom⟩
    exact_mod_cast Fintype.card_ne_zero
  have hh : (classNumber K : ℝ) ≠ 0 := by exact_mod_cast classNumber_ne_zero K

  calc embMean F.k (fun s ↦ logPeriod (F.periodLattice s))
      = (classNumber K : ℝ)⁻¹ * ∑ _C : ClassGroup (𝓞 K),
          embMean F.k (fun s ↦ logPeriod (F.periodLattice s)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact (inv_mul_cancel_left₀ hh _).symm
    _ = (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K), embMean F.k (fun s ↦
          logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
            F.periodLattice s)) := by
        congr 1
        exact Finset.sum_congr rfl fun C _ ↦ (hMean _).symm
    _ = embMean F.k (fun s ↦ (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K),
          logPeriod (idealLattice (F.restrict s) ↑(FractionalIdeal.mk0 K (classRep C)) *
            F.periodLattice s)) := by
        simp only [embMean, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = classMean σ := by
        simp only [hs, embMean, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
