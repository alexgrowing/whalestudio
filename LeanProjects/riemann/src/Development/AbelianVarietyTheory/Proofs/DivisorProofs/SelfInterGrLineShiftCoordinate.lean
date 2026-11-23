import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectiveLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique

open GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagZ

theorem sum_castSucc_sub_succ {G : Type*} [AddCommGroup G] :
    ∀ (N : ℕ) (f : Fin (N + 1) → G), ∑ i : Fin N, (f i.castSucc - f i.succ) = f 0 - f (Fin.last N)
  | 0, f => by simp
  | N + 1, f => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    rw [sum_castSucc_sub_succ N (fun i => f i.castSucc)]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    abel

theorem icls_flDet_eq_zero {ι : Type} [Fintype ι] {N : ℕ} (τ : ι) (l : Fin (N + 1)) (hl : plDim N l = 0) :
    (flDet (ι := ι) (N := N) τ l).icls = 0 :=
  (HermLB.icls_pull _ _ _).trans ((congrArg _ (HermLB.icls_eq_iff.2 (Plane.isometric_fubini_study_dim_zero hl))).trans
    (map_zero _))

theorem sum_icls_grLine {ι : Type} [Fintype ι] {N : ℕ} (τ : ι) :
    ∑ i : Fin N, (grLine (ι := ι) (N := N) (τ, i)).icls = 0 := by
  have e (i : Fin N) : (grLine (ι := ι) (N := N) (τ, i)).icls =
      (flDet (ι := ι) (N := N) τ i.castSucc).icls - (flDet (ι := ι) (N := N) τ i.succ).icls := by
    rw [grLine, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
  simp only [e]
  rw [sum_castSucc_sub_succ N (fun l => (flDet (ι := ι) (N := N) τ l).icls),
    icls_flDet_eq_zero τ 0 (by simp [plDim]), icls_flDet_eq_zero τ (Fin.last N) (by simp [plDim]), sub_zero]

theorem isSelfInter_comb_grLine_shift : Hypotheses2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (τ : ι)
    (n : ι × Fin N → ℤ) (t : ℤ) (a : ℝ), (comb (grLine (ι := ι) (N := N)) n).IsSelfInter a →
    (comb (grLine (ι := ι) (N := N)) fun x => n x + if x.1 = τ then t else 0).IsSelfInter a := by
  intro _ ι _ _ N τ n t a H
  refine HermLB.Isometric.isSelfInter (isArithVar_hasHh_unique ι N).1 (HermLB.icls_eq_iff.1 ?_) H
  rw [icls_comb, icls_comb]
  rw [Finset.sum_congr rfl fun x _ => add_zsmul (grLine (ι := ι) (N := N) x).icls (n x) _, Finset.sum_add_distrib]
  have hz : ∑ x : ι × Fin N, (if x.1 = τ then t else 0) • (grLine (ι := ι) (N := N) x).icls = 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun τ' _ => ?_
    show ∑ i : Fin N, (if τ' = τ then t else 0) • (grLine (ι := ι) (N := N) (τ', i)).icls = 0
    rw [← Finset.smul_sum, sum_icls_grLine, smul_zero]
  rw [hz, add_zero]

end GlobalTheory.FlagZ
