import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.StTrdegAdjoinFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMinorsBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMinorsTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_flagMap_X (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    ((aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
      MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) = flagMap P B :=
  MvPolynomial.ringHom_ext (fun r => by
    rw [← RingHom.comp_apply _ C r, ← RingHom.comp_apply _ C r, eq_intCast, eq_intCast]) fun q => by
    simp

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem range_aeval_flagMap_X (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range =
      Algebra.adjoin ℤ
        (Set.range (fun d : MRing ι ⧸ P => algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))
            (algebraMap (MRing ι ⧸ P) (FnField P) d)) ∪
          Set.range fun q : Σ j, PluckerBlocks N1 n j => flagMinor (genMat (FnField P) n * B.map C) q.1 q.2) := by
  rw [← Algebra.adjoin_range_eq_range_aeval]
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k | j, i⟩, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨Ideal.Quotient.mk P (X ⟨k, i⟩), by simp [flagMap, genPt, algebraMap_eq]⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨⟨j, i⟩, by simp [flagMap]⟩)
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨d, rfl⟩ | ⟨⟨j, S⟩, rfl⟩)
    · obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
      have e := @aeval_comp_X _ _ _ _ _ inferInstance (Ideal.Quotient.mk P)
        ((algebraMap (FnField P) (MvPolynomial (Fin n × Fin n) (FnField P))).comp
          (algebraMap (MRing ι ⧸ P) (FnField P))) f
      have hm : aeval (fun p => flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p))) f ∈
          Algebra.adjoin ℤ (Set.range fun p => flagMap P B (X (inlV (ι₂ := PluckerBlocks N1 n) p))) := by
        rw [Algebra.adjoin_range_eq_range_aeval]
        exact ⟨f, rfl⟩
      simp_rw [flagMap_X_inl] at hm
      refine Algebra.adjoin_mono ?_ (e ▸ hm)
      · rintro _ ⟨p, rfl⟩
        exact ⟨_, flagMap_X_inl P B p⟩
    · exact Algebra.subset_adjoin ⟨⟨Sum.inr j, S⟩, by simp [flagMap]⟩

theorem FlagConeTrdeg.proof (h₁ : TrdegAdjoinFrac.Statement) (h₂ : FlagMinorsBaseChange.Statement)
    (h₃ : FlagMinorsTrdeg.Statement) : FlagConeTrdeg.Statement := by
  intro K _ ι _ N1 n P B hP hH hB
  have hinj : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : C a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [Ideal.Quotient.algebraMap_eq, algebraMap_eq] using ha
    have h2 : a ∈ P.comap (C : ℤ →+* MRing ι) := this
    rwa [hH, Ideal.mem_bot] at h2
  have e := Ideal.quotientKerEquivRange
    (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))
  have hk : RingHom.ker
      (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) =
        flagIdeal P B := by
    ext f
    have h : ((aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)) :
          MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P)) f = flagMap P B f := by
      rw [aeval_flagMap_X]
    rw [RingHom.mem_ker, flagIdeal, RingHom.mem_ker, ← h, RingHom.coe_coe]
  have ht : Algebra.trdeg ℤ (MRing (FlagBundleBlocks ι N1 n) ⧸ RingHom.ker
      (aeval fun q => flagMap P B (X q) : MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))) =
      Algebra.trdeg ℤ (aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range := by
    have e' : (MRing (FlagBundleBlocks ι N1 n) ⧸ RingHom.ker (aeval fun q => flagMap P B (X q) :
        MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P))) ≃ₐ[ℤ]
        (aeval fun q => flagMap P B (X q) :
          MRing (FlagBundleBlocks ι N1 n) →ₐ[ℤ] MvPolynomial (Fin n × Fin n) (FnField P)).range := e
    exact e'.trdeg_eq
  have e2 := h₂ (FnField P) n N1 B hB
  rw [← hk, ht, range_aeval_flagMap_X]
  exact (h₁ (MRing ι ⧸ P) (MvPolynomial (Fin n × Fin n) (FnField P)) _ hinj).trans (by rw [e2, h₃])

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
