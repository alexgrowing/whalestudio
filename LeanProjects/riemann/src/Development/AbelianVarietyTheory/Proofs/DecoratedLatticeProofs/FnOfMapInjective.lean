import Mathlib
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.TiedValNorm
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.Columns.CoefModAt
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SlopeStepG
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Core

theorem fnOf_map_injective {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ)
    (sh : ι → ℤ) (s : K →+* ℂ) {F F' : MvPolynomial (ι × Fin n × Fin n) K}
    (h : fnOf G sh 1 (MvPolynomial.map s F) = fnOf G sh 1 (MvPolynomial.map s F')) : F = F' :=
  MvPolynomial.map_injective s s.injective
    (Formalism.L2.Col.fnOf_injective G sh 1 (fun _ => by simp)
      (⟨fun _ => 1, fun _ => by simp⟩ : {y : ι → Matrix (Fin n) (Fin n) ℂ // ∀ τ, IsUnit (y τ).det}) h)

theorem exists_ptVal_at (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K) (x : (D.fm u).ptLat.V)
    (c : (D.fm u).clsP) : ∃ F : VV D.what₂.LL (sgT u),
      W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL F.1) := by
  obtain ⟨P, hP, hv⟩ := ((W.rat _).1 ⟨x, rfl⟩).2 c
  have e : Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) = Formalism.L2.Col.RatSpanG D.what₂.embLL (D.fm u).sg :=
    Formalism.L2.Col.RatSpanG_shW D.what₂.embLL (D.fm u).sg (fun _ => ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ))
  have hP' : P ∈ Formalism.L2.Col.RatSpanG D.what₂.embLL (sgT u) := by rw [e]; exact hP
  obtain ⟨F, hF, rfl⟩ := Formalism.L2.Col.exists_VV_of_mem_RatSpanG _ _ hP'
  exact ⟨⟨F, hF⟩, hv⟩

theorem exists_ptVal : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (W : ValPTied u K), ∃ val : (D.fm u).ptLat.V →ₗ[D.what₂.LL] ((D.fm u).clsP → VV D.what₂.LL (sgT u)), (∀ x c, W.eW ((D.fm u).ptEmb x) c = fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (val x c).1)) := by
  intro D u K W
  choose val hval using exists_ptVal_at D u K W
  refine ⟨{ toFun := val, map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, hval⟩
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    rw [← hval, Pi.add_apply, Submodule.coe_add, map_add, map_add, map_add, map_add, ← hval, ← hval, Pi.add_apply]
  · funext c
    apply Subtype.ext
    refine fnOf_map_injective (gramC (gramP D) (embT D)) (shiftOf (sgT u)) D.what₂.embLL ?_
    have e : MvPolynomial.map D.what₂.embLL (a • (val x c).1) =
        D.what₂.embLL a • MvPolynomial.map D.what₂.embLL (val x c).1 := by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    rw [← hval, RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul, e, LinearMap.map_smul, ← hval,
      LinearMap.map_smulₛₗ, LinearEquiv.map_smul, Pi.smul_apply]

end GlobalTheory.Core
