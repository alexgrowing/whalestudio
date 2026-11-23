import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory.AnPer

open GlobalTheory.CatCoh

attribute [local instance] Charts.Obj.cAlg

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {D : Type} [CommRing D] [Algebra ℂ D]

def Charts.Obj.tenContract (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) : T.ten D →ₗ[ℂ] T.C :=
  (TensorProduct.lid ℂ T.C).toLinearMap ∘ₗ LinearMap.rTensor T.C ℓ

theorem Charts.Obj.tenContract_tmul (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) (d : D) (c : T.C) :
    T.tenContract ℓ (d ⊗ₜ c) = ℓ d • c := rfl

theorem Charts.Hom.tenContract_ten (ℓ : D →ₗ[ℂ] ℂ) {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.tenContract ℓ (Charts.Hom.ten D f x) = f.φ (T.tenContract ℓ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul d c =>
    rw [Charts.Hom.ten_tmul, Charts.Obj.tenContract_tmul, Charts.Obj.tenContract_tmul]
    exact (map_smul (Charts.Hom.φc f) (ℓ d) c).symm

theorem Charts.tenZ_eq_zero (K : Charts F) (hK : K.Rich) (hz : ∃ z, z ∈ F.V) {D : Type} [CommRing D] [Algebra ℂ D]
    (p : Λ →+ D) (h : H1.mk _ (K.tenZ p) = 0) : p = 0 := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨G, hG⟩ := H1.mk_eq_zero.1 h
  refine AddMonoidHom.ext fun l ↦ (Module.forall_dual_apply_eq_zero_iff ℂ (p l)).1 fun ℓ ↦ ?_
  let q : Λ →+ Hol F.V := ((algebraMap ℂ (Hol F.V)).toAddMonoidHom.comp ℓ.toAddMonoidHom).comp p
  have h0 : K.perZ 0 = 0 := Subtype.ext (by
    funext T T' f
    exact map_zero (algebraMap (Hol F.V) T'.C))
  have hq : K.perCl q = K.perCl 0 := by
    unfold Charts.perCl
    rw [h0, map_zero]
    refine H1.mk_eq_zero.2 ⟨fun T ↦ T.tenContract ℓ (G T), ?_⟩
    funext T T' f
    have e : G T' - Charts.Hom.ten D f (G T) = (p f.deg ⊗ₜ[ℂ] (1 : T'.C) : T'.ten D) :=
      congrFun (congrFun (congrFun hG T) T') f
    have e' := congrArg (T'.tenContract ℓ) e
    rw [map_sub, Charts.Hom.tenContract_ten, Charts.Obj.tenContract_tmul, ← Algebra.algebraMap_eq_smul_one] at e'
    exact e'
  have h1 : algebraMap ℂ (Hol F.V) (ℓ (p l)) = 0 := DFunLike.congr_fun (GlobalTheory.T.periodClass_injective_of_rich_charts K hK q 0 hq) l
  have h2 := congrArg (Hol.ev z hz) h1
  rwa [AlgHom.commutes, map_zero] at h2

end GlobalTheory.AnPer
