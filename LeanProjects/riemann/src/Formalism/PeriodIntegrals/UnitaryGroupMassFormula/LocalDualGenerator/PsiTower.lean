import Mathlib
import Formalism.PeriodIntegrals.LocDualGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.DualAtLMulUnit

noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen.Top

open PI.LocDualGen.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} [Fact (resChar p).Prime]

abbrev qAlg (A : LocAt F E sig p) : Algebra ℚ_[resChar p] A.Ep :=
  ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra

theorem trQ_eq (A : LocAt F E sig p) (z : A.Ep) :
    (letI := qAlg A; Algebra.trace ℚ_[resChar p] A.Ep z) =
      Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z) := by
  letI := qAlg A
  have : IsScalarTower ℚ_[resChar p] A.Fp A.Ep := IsScalarTower.of_algebraMap_eq' (R := ℚ_[resChar p]) (S := A.Fp) (A := A.Ep) rfl
  haveI := A.free
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  haveI := A.qlFin
  exact (Algebra.trace_trace (R := ℚ_[resChar p]) (S := A.Fp) z).symm

theorem psi_tower (hK : PsiKer) (A : LocAt F E sig p) (z : A.Ep) :
    A.psiE z = 1 ↔ ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z)‖ ≤ 1 := by
  obtain ⟨a, ha, hle, hpsi⟩ := A.psiE_def z
  have hle' : ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep z) - (a : ℚ_[resChar p])‖ ≤ 1 := by
    rw [← trQ_eq]; exact hle
  rw [hpsi]
  exact hK _ _ a ha hle'

theorem tr_smul (A : LocAt F E sig p) (z : A.Ep) (c : A.Fp) :
    Algebra.trace A.Fp A.Ep (z * algebraMap A.Fp A.Ep c) = Algebra.trace A.Fp A.Ep z * c := by
  rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

theorem assemble (hK : PsiKer) (A : LocAt F E sig p) (d : A.Fp)
    (hd : ∀ a : A.Fp, (∀ b : 𝒪[A.Fp],
      ‖Algebra.trace ℚ_[resChar p] A.Fp (a * (b : A.Fp) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[A.Fp])
    (hE : ∀ x : A.Ep, (∀ y ∈ A.O, Algebra.trace A.Fp A.Ep (x * y) ∈ 𝒪[A.Fp]) ↔ x ∈ A.O) :
    DualAtL A d := by
  have key : ∀ x y : A.Ep, A.psiE (-(x * y * algebraMap A.Fp A.Ep d⁻¹)) = 1 ↔
      ‖Algebra.trace ℚ_[resChar p] A.Fp (Algebra.trace A.Fp A.Ep (x * y) * d⁻¹)‖ ≤ 1 := by
    intro x y
    rw [psi_tower hK]
    simp only [map_neg, norm_neg]
    rw [tr_smul]
  unfold DualAtL
  intro x
  simp_rw [key]
  constructor
  · intro H
    rw [← hE]
    intro y hy
    rw [← hd]
    intro b
    have hyb : y * algebraMap A.Fp A.Ep (b : A.Fp) ∈ A.O :=
      A.O.mul_mem hy (Part2.alg_mem_O A b)
    have := H _ hyb
    rwa [← mul_assoc, tr_smul] at this
  · intro hx y hy
    have ha := (hE x).2 hx y hy
    have := (hd _).2 ha 1
    simpa using this

theorem stmt_of (hK : PsiKer) (h1 : FpDual) (h2 : FpDualUnram) (h3 : EpSelfDual) :
    PI.LocDualGen.Stmt := by
  intro F E _ _ _ _ _ sig p A
  haveI := A.ellPrime
  have hE : IsReduced A.Ep → UnramL A → ∀ x : A.Ep,
      (∀ y ∈ A.O, Algebra.trace A.Fp A.Ep (x * y) ∈ 𝒪[A.Fp]) ↔ x ∈ A.O :=
    fun hr hu => h3 A.Fp A.Ep A.lf A.char0 A.free A.rank hr A.O A.O_def hu
  refine ⟨fun hr hu => ?_, fun δ u hu h => Part2.dualAtL_mul_unit A δ u hu h, fun hr hu hl => ?_⟩
  · obtain ⟨d, hd0, hd⟩ := h1 A.Fp (resChar p) A.lf A.char0 A.qlCont A.qlFin
    exact ⟨d, hd0, assemble hK A d hd (hE hr hu)⟩
  · refine assemble hK A 1 (fun a => ?_) (hE hr hu)
    simpa [inv_one, mul_one] using h2 A.Fp (resChar p) A.lf A.char0 A.qlCont A.qlFin hl a

end PI.LocDualGen.Top
