import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogBasisAndVanishingAboveDimensionStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem omB_eq_bot {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (a : ℕ)
    (hv : ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], y = 0) : omB ℂ K B a = ⊥ := by
  unfold omB
  rw [Submodule.span_eq_bot]
  rintro y ⟨b, -, v, -, rfl⟩
  rw [hv _ (ExteriorAlgebra.ιMulti_range K a ⟨_, rfl⟩), smul_zero]

private theorem trace_eq_zero_of_bot {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (G : Finset ι → Submodule ℂ E) (hG : ∀ I, G I = ⊥) (p : ℤ)
    (f : (cech G).H p →ₗ[ℂ] (cech G).H p) : LinearMap.trace ℂ _ f = 0 := by
  have hZ : ∀ z ∈ (cech G).Z p, z = 0 := by
    intro z hz
    have hC : z ∈ cechC G p := (Submodule.mem_inf.1 hz).1
    rw [cechC, Submodule.mem_pi] at hC
    funext s
    have h1 := hC s (Set.mem_univ s)
    split_ifs at h1 <;> simpa [hG] using h1
  haveI : Subsingleton ((cech G).Z p) :=
    ⟨fun a b => Subtype.ext ((hZ a a.2).trans (hZ b b.2).symm)⟩
  haveI : Subsingleton ((cech G).H p) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  rw [Subsingleton.elim f 0, map_zero]

private theorem coeff_det_eq_zero {d a : ℕ} (hlt : d < a) (B : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)).coeff a = 0 := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_eq_empty.2 (by simpa using hlt), Finset.sum_empty]

private theorem val_div {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    (c g : L) (hc : c ∈ B) (hg : g ∈ B) (hne : e ⟨c, hc⟩ ≠ 0) (t : ℂ)
    (h : e ⟨g, hg⟩ = e ⟨c, hc⟩ * t) (hc0 : c ≠ 0) : Val B e (g / c) t := by
  have hcg : c * (g / c) = g := by
    rw [mul_comm]
    exact div_mul_cancel₀ g hc0
  have hmem : c * (g / c) ∈ B := by
    rw [hcg]
    exact hg
  refine ⟨c, hc, hmem, hne, ?_⟩
  have hsub : (⟨c * (g / c), hmem⟩ : B) = ⟨g, hg⟩ := Subtype.ext hcg
  rw [hsub, h]

theorem UpperTheory.Gal.productCup_of_system.field0_of :
    FieldLe → ValBasic → Field0 := by
  intro hLe _
  intro d a F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ x j2 hK hK' hred hnf hz hfix Fx hFx hgen A hA hdet u hu hfd
  by_cases had : a ≤ d
  · have hne : ∀ i, x i ≠ 0 := hK.pd.ne
    let xu : Fin (d + 1) → Fˣ := fun i => Units.mk0 (x i) (hne i)
    have hY : Y1 xu j2 Fx A :=
      { covZ := hK
        covY := hK'
        cov := by
          intro i e
          obtain ⟨j, hj⟩ := hred i e
          refine ⟨j, fun v hv => ?_⟩
          obtain ⟨b, hb, he, hbv⟩ := hj v hv
          exact ⟨⟨b, hb⟩, he, hbv⟩
        red := hnf
        off := hz
        orig := hfix
        fx := hFx
        tan := by
          intro e he m
          obtain ⟨c, hc, g, hg, hec, hsum, hgl⟩ := hA e he m
          have hc0 : c ≠ 0 := by
            rintro rfl
            apply hec
            have h0 : (⟨0, hc⟩ : rB ℂ K' x {0}) = 0 := rfl
            rw [h0, map_zero]
          refine ⟨fun l => g l / c, fun l => val_div _ _ c (g l) hc (hg l) hec _ (hgl l) hc0, ?_⟩
          show j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l / c * algebraMap F K' (x l.succ / x 0)
          apply mul_left_cancel₀ hc0
          rw [hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mul_assoc, mul_comm c, div_mul_cancel₀ _ hc0]
        det := hdet }
    exact hLe F K K' d xu j2 Fx A hY a had u hu
  · push_neg at had
    have hv := (GlobalTheory.T.dlog_basis_and_vanishing_above_dimension ℂ F K d x hK).2 a had
    refine (Finset.sum_eq_zero fun p _ => ?_).trans (Finset.sum_eq_zero fun e _ => ?_).symm
    · rw [trace_eq_zero_of_bot _ (fun I => omB_eq_bot _ a hv) _ (u p), mul_zero]
    · rw [coeff_det_eq_zero had, zero_div]
