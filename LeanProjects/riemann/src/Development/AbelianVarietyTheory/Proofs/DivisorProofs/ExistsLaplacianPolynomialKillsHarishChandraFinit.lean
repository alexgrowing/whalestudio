import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantLaplacianEqCasimirDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyAnnihilatesCommutingLinearCombination
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyMaximalCompactCasimirKillsKTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace GlobalTheory.GLPoly

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem commute_lieS' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (i j : Fin a) (x : Cinf E) :
    Commute z (lieS E a i j x) := by
  rw [lieS_apply]; exact hz _

theorem commute_casKOp' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) :
    Commute z (casKOp E a) := by
  unfold casKOp
  refine Commute.sum_right _ _ _ fun τ _ => Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  refine Commute.smul_right (Commute.add_right (Commute.pow_right ?_ 2) (Commute.pow_right ?_ 2)) _
  · exact (commute_lieS' hz _ _ _).sub_right (commute_lieS' hz _ _ _)
  · exact (commute_lieS' hz _ _ _).add_right (commute_lieS' hz _ _ _)

theorem commute_cas' {z : Module.End ℂ (Sm E a)} (hz : ∀ X, Commute z (lie E a X)) (τ : E →+* ℂ) :
    Commute z (Formalism.REAL.Cas (Eop (a := a) τ)) := by
  have hE : ∀ i j, Commute z (Eop τ i j) := fun i j =>
    Commute.smul_right ((commute_lieS' hz _ _ _).sub_right ((commute_lieS' hz _ _ _).smul_right _)) _
  unfold Formalism.REAL.Cas
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => (hE i j).mul_right (hE j i)

theorem foldr_replicate' (z : Module.End ℂ (Sm E a)) (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (φ : Sm E a) :
    (List.replicate N z).foldr (fun z f => z f - χ z • f) φ =
      Polynomial.aeval z ((Polynomial.X - Polynomial.C (χ z)) ^ N) φ := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.foldr_cons, ih, pow_succ', map_mul, Module.End.mul_apply]
    simp [sub_smul, Polynomial.aeval_X, Polynomial.aeval_C]

variable (E a) in

theorem exists_poly_one (W : Submodule ℂ (Kinf E a → ℂ)) (hW : FiniteDimensional ℂ W)
    (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ φ : Sm E a,
      (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ W) → GlobalTheory.HCF.CentralNilGL χ N φ →
        Polynomial.aeval (lapOp E a) p φ = 0 := by
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.T.exists_poly_maximalCompactCasimir_kills_KType E a W hW
  let A : Option (E →+* ℂ) → Module.End ℂ (Sm E a) := fun o => o.elim (casKOp E a) fun τ => Formalism.REAL.Cas (Eop τ)
  let c : Option (E →+* ℂ) → ℂ := fun o => o.elim 2 fun _ => 4
  let P : Option (E →+* ℂ) → Polynomial ℂ := fun o =>
    o.elim q fun τ => (Polynomial.X - Polynomial.C (χ (Formalism.REAL.Cas (Eop (a := a) τ)))) ^ N
  have hZ : ∀ τ : E →+* ℂ, ∀ X, Commute (Formalism.REAL.Cas (Eop (a := a) τ)) (lie E a X) := fun τ X =>
    GlobalTheory.CuspRep.Zalg_mul_lie E a X _ (GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
  have hc : ∀ i j, Commute (A i) (A j) := by
    rintro (_ | τ) (_ | τ')
    · exact Commute.refl _
    · exact (commute_casKOp' (hZ τ')).symm
    · exact commute_casKOp' (hZ τ)
    · exact commute_cas' (hZ τ) τ'
  have hP : ∀ i, P i ≠ 0 := by
    rintro (_ | τ)
    · exact hq0
    · exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination A hc c P hP
  refine ⟨p, hp0, fun φ hK hN => ?_⟩
  have e : ∑ i, c i • A i = lapOp E a := by
    rw [GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas E a, Fintype.sum_option]; rfl
  rw [← e]
  refine hp φ ?_
  rintro (_ | τ)
  · exact hq φ hK
  · have h := hN (List.replicate N (Formalism.REAL.Cas (Eop τ))) (List.length_replicate ..)
      (fun z hz => (List.eq_of_mem_replicate hz) ▸ GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
    rw [foldr_replicate'] at h
    exact h

theorem exists_poly_formsGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∀ (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W →
    ∀ X : Set (Module.End ℂ (Sm E a) → ℂ), X.Finite → ∀ N : ℕ, ∃ p : Polynomial ℂ, p ≠ 0 ∧
      ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, Polynomial.aeval (lapOp E a) p φ = 0 := by
  intro E _ _ _ a L W hW X hX N
  classical
  choose pχ hpχ0 hpχ using fun χ => exists_poly_one E a W hW χ N
  refine ⟨∏ χ ∈ hX.toFinset, pχ χ, Finset.prod_ne_zero_iff.mpr fun χ _ => hpχ0 χ, fun φ hφ => ?_⟩
  obtain ⟨χ, hχX, hN⟩ := hφ.2.2.2
  have hmem : χ ∈ hX.toFinset := hX.mem_toFinset.mpr hχX
  rw [← Finset.mul_prod_erase _ _ hmem, mul_comm, map_mul, Module.End.mul_apply, hpχ χ φ hφ.2.2.1 hN, map_zero]

end GlobalTheory.GLPoly

end
