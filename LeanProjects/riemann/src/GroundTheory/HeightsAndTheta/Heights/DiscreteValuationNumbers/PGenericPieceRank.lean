import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section GenericPiece

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem isWeightedHomogeneous_map_coeff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) {w : σ → M} {g : MvPolynomial σ R} {b : M}
    (h : IsWeightedHomogeneous w g b) : IsWeightedHomogeneous w (map f g) b := by
  intro d hd
  apply h
  intro h0
  rw [coeff_map, h0, map_zero] at hd
  exact hd rfl

theorem isWeightedHomogeneous_of_map_coeff {R S σ M : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid M] (f : R →+* S) (hf : Function.Injective f) {w : σ → M}
    {g : MvPolynomial σ R} {b : M} (h : IsWeightedHomogeneous w (map f g) b) :
    IsWeightedHomogeneous w g b := by
  intro d hd
  apply h
  rw [coeff_map]
  exact (map_ne_zero_iff f hf).mpr hd

def genFibQuot (P : Ideal (MRing ι O)) :
    (MRing ι O ⧸ P) →ₐ[O] (MRing ι (FractionRing O) ⧸ genFib P) :=
  Ideal.quotientMapₐ (genFib P) (mapAlgHom (Algebra.ofId O (FractionRing O)))
    (fun _ hx => Ideal.mem_comap.mpr (Ideal.mem_map_of_mem _ hx))

omit [IsDomain O] [DecidableEq K] in
theorem genFibQuot_mk (P : Ideal (MRing ι O)) (g : MRing ι O) :
    genFibQuot P (Ideal.Quotient.mk P g) =
      Ideal.Quotient.mk (genFib P) (map (algebraMap O (FractionRing O)) g) := rfl

def genFibPiece (P : Ideal (MRing ι O)) (m : K → ℕ) :
    gradedPieceR P m →ₗ[O] gradedPiece (genFib P) m where
  toFun x := ⟨genFibQuot P x.1, by
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.mp x.2
    refine Submodule.mem_map.mpr ⟨map (algebraMap O (FractionRing O)) g, ?_, ?_⟩
    · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_map_coeff _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hg))
    · rw [← hgx]
      rfl⟩
  map_add' x y := Subtype.ext (map_add (genFibQuot P) x.1 y.1)
  map_smul' c x := Subtype.ext ((genFibQuot P).toLinearMap.map_smul c x.1)

theorem isLocalizedModule_genFibPiece (P : Ideal (MRing ι O)) (m : K → ℕ) :
    IsLocalizedModule (nonZeroDivisors O) (genFibPiece P m) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx : algebraMap O (FractionRing O) x ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z h
      have h' : algebraMap O (FractionRing O) x • y = algebraMap O (FractionRing O) x • z := by
        simpa only [Module.algebraMap_end_apply, algebraMap_smul] using h
      exact smul_right_injective _ hx h'
    · intro y
      refine ⟨(algebraMap O (FractionRing O) x)⁻¹ • y, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (FractionRing O), smul_smul,
        mul_inv_cancel₀ hx, one_smul]
  surj y := by
    obtain ⟨q, hq⟩ := y
    obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hq
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := O) (S := FractionRing O)
    obtain ⟨⟨g, c⟩, hgc⟩ :=
      IsLocalization.surj ((nonZeroDivisors O).map (C (σ := Σ k, ι k))) F
    obtain ⟨b, hb, hbc⟩ := Submonoid.mem_map.mp c.2
    simp only [algebraMap_def, ← hbc, map_C] at hgc
    have hFh : IsWeightedHomogeneous (blockWeight ι) F m :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp hF
    have hmg : IsWeightedHomogeneous (blockWeight ι) (map (algebraMap O (FractionRing O)) g) m := by
      rw [← hgc]
      intro d hd
      rw [mul_comm, coeff_C_mul] at hd
      exact hFh (right_ne_zero_of_mul hd)
    have hg : IsWeightedHomogeneous (blockWeight ι) g m :=
      isWeightedHomogeneous_of_map_coeff _ (IsFractionRing.injective O (FractionRing O)) hmg
    refine ⟨(⟨Ideal.Quotient.mk P g, Submodule.mem_map.mpr
      ⟨g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg, rfl⟩⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    change b • (Ideal.Quotient.mkₐ (FractionRing O) (genFib P)) F =
      genFibQuot P (Ideal.Quotient.mk P g)
    rw [genFibQuot_mk, ← hgc, ← algebraMap_smul (FractionRing O), ← map_smul, smul_eq_C_mul,
      mul_comm, Ideal.Quotient.mkₐ_eq_mk]
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨q₁, hq₁⟩ := x₁
    obtain ⟨q₂, hq₂⟩ := x₂
    obtain ⟨g₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
    have h₀ : genFibQuot P (Ideal.Quotient.mk P g₁) = genFibQuot P (Ideal.Quotient.mk P g₂) :=
      congrArg Subtype.val h
    rw [genFibQuot_mk, genFibQuot_mk, Ideal.Quotient.eq, ← map_sub] at h₀
    let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := O) (S := FractionRing O)
    rw [genFib, ← algebraMap_def,
      IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors O).map (C (σ := Σ k, ι k)))
        (MRing ι (FractionRing O))] at h₀
    obtain ⟨⟨⟨p, hp⟩, ⟨c, hc⟩⟩, hpc⟩ := h₀
    obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hc
    simp only [algebraMap_def, ← map_mul] at hpc
    have hp' : (g₁ - g₂) * C b = p :=
      map_injective _ (IsFractionRing.injective O (FractionRing O)) hpc
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    change b • (Ideal.Quotient.mkₐ O P) g₁ = b • (Ideal.Quotient.mkₐ O P) g₂
    rw [← map_smul, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, ← smul_sub,
      smul_eq_C_mul, mul_comm, hp']
    exact hp

theorem GenericPieceRank.proof : GenericPieceRank.Statement := by
  intro O _ _ _ K _ _ ι _ P _ m
  have := isLocalizedModule_genFibPiece P m
  rw [IsFractionRing.finrank_right_eq O (FractionRing O),
    IsLocalizedModule.finrank_eq (p := nonZeroDivisors O) (f := genFibPiece P m) (hp := le_rfl)]

end GenericPiece

end

end GroundTheory.Heights₂.Heights.NumbersDVR
