import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section
namespace GlobalTheory.CompanionTheory.RatProdFormula

theorem pri_eq_diagonal (α : ℚˣ) : pri α = IdeleGroup.diagonal ℚ α := rfl

def nf (α : ℚˣ) (v : Pl) : ℝ := ‖((pri α : Jd) : 𝔸[ℚ]).2 v‖

theorem nf_pos (α : ℚˣ) (v : Pl) : 0 < nf α v :=
  norm_pos_iff.2 (IdeleGroup.finite_ne_zero (pri α) v)

theorem mp_eq (α : ℚˣ) (v : Pl) (s : ℂ) :
    mp (Ad3.R.lc v (pri α)) s = ((nf α v : ℝ) : ℂ) ^ s := by
  have h := GroundTheory.Automorphic.GodementSection.modulus_adicCompletion (K := ℚ) v
    (((Ad3.R.lc v (pri α)) : (Qv v)ˣ) : Qv v)
  have h2 : ‖(((Ad3.R.lc v (pri α)) : (Qv v)ˣ) : Qv v)‖ = nf α v := rfl
  rw [h2] at h
  unfold mp
  rw [h]

theorem infinite_eq (α : ℚˣ) : IdeleGroup.infiniteModule (pri α) = |(α : ℝ)| := by
  rw [pri_eq_diagonal, IdeleGroup.infiniteModule_diagonal]
  simp [Rat.infinitePlace_apply]

theorem finite_support (α : ℚˣ) : (Function.mulSupport (nf α)).Finite :=
  IdeleGroup.finite_mulSupport_norm (pri α)

theorem finite_mul_abs (α : ℚˣ) : (∏ᶠ v : Pl, nf α v) * |(α : ℝ)| = 1 := by
  have h := congrArg (fun r : {r : ℝ // 0 < r} => (r : ℝ)) (IdeleGroup.ideleModule_diagonal (K := ℚ) α)
  simp only [Positive.val_one] at h
  rw [IdeleGroup.ideleModule_apply, ← pri_eq_diagonal, infinite_eq, mul_comm] at h
  exact h

theorem mulSupport_subset (α : ℚˣ) :
    (Function.mulSupport fun v : Pl => mp (Ad3.R.lc v (pri α)) (1 / 2)) ⊆
      Function.mulSupport (nf α) := by
  intro v hv h1
  apply hv
  have h1' : nf α v = 1 := h1
  simp only [mp_eq, h1', Complex.ofReal_one, Complex.one_cpow]

theorem mp_half (α : ℚˣ) (v : Pl) :
    mp (Ad3.R.lc v (pri α)) (1 / 2) = ((nf α v ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [mp_eq, Complex.ofReal_cpow (nf_pos α v).le]
  norm_num

theorem product_formula_half : ∀ α : ℚˣ,
    (Function.mulSupport fun v : Pl => mp (Ad3.R.lc v (pri α)) (1 / 2)).Finite ∧
    (∏ᶠ v : Pl, mp (Ad3.R.lc v (pri α)) (1 / 2)) * ((|(α : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 1 := by
  intro α
  refine ⟨(finite_support α).subset (mulSupport_subset α), ?_⟩
  have hfin := finite_support α
  have hsub : (Function.mulSupport fun v : Pl => mp (Ad3.R.lc v (pri α)) (1 / 2)) ⊆
      (hfin.toFinset : Set Pl) := by
    rw [Set.Finite.coe_toFinset]; exact mulSupport_subset α
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  have h1 : (∏ᶠ v : Pl, nf α v) = ∏ v ∈ hfin.toFinset, nf α v := finprod_eq_prod _ hfin
  have hab := finite_mul_abs α
  rw [h1] at hab
  have habs : (0 : ℝ) ≤ |(α : ℝ)| := abs_nonneg _
  have hP : (0 : ℝ) ≤ ∏ v ∈ hfin.toFinset, nf α v :=
    Finset.prod_nonneg fun v _ => (nf_pos α v).le
  have h2 : ((|(α : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((|(α : ℝ)| ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow habs]; norm_num
  rw [h2]
  simp only [mp_half]
  rw [← Complex.ofReal_prod, ← Complex.ofReal_mul,
    Real.finsetProd_rpow _ _ (fun v _ => (nf_pos α v).le), ← Real.mul_rpow hP habs, hab,
    Real.one_rpow, Complex.ofReal_one]

end GlobalTheory.CompanionTheory.RatProdFormula
