import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.Model

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem latIndex_eq_one_of_mem (W : HSp D) (g : GA D W) (hg : g ∈ KsphC W ∅) (hg' : g⁻¹ ∈ KsphC W ∅) :
    latIndex W g = 1 := by
  unfold latIndex
  rw [AddSubgroup.relIndex_eq_one]
  intro y hy
  refine ⟨(finMat D.sp.cm.sig W.gram g⁻¹).mulVec y, (hg'.2.1 y).1 hy, ?_⟩
  have h : finMat D.sp.cm.sig W.gram g * finMat D.sp.cm.sig W.gram g⁻¹ = 1 := by
    have := congrArg (fun u : GL (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => u.val)
      (show finHom W g * finHom W g⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
    exact this
  show (finMat D.sp.cm.sig W.gram g).mulVec ((finMat D.sp.cm.sig W.gram g⁻¹).mulVec y) = y
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

theorem coef_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : VecNe R i t) (μ) (𝓕)
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) : coef R i t μ 𝓕 1 = 1 := by
  unfold coef
  have : R.ωP i t (1, 1) = 1 := map_one _
  rw [this]
  exact div_self (h μ 𝓕 hμ).1

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem coef_mul_lev (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : LevFix R i t) (μ) (𝓕) (g k : GA D (Wc D i))
    (hk : k ∈ levW R i) : coef R i t μ 𝓕 (g * k) = coef R i t μ 𝓕 g := by
  unfold coef
  have e : R.ωP i t (1, g * k) = R.ωP i t (1, g) * R.ωP i t (1, k) := by rw [← map_mul]; simp
  have hv := h k hk 1
  rw [pureTensor_one] at hv
  rw [e, Module.End.mul_apply, hv]

theorem goodMod_ne (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (h : GoodMod R i t) (μ) (𝓕)
    (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) (v f) (hf : IsFinIdem D v f)
    (hP : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) (k) (hk : SuppF (Wc D i) f k) :
    coef R i t μ 𝓕 k ≠ 0 := by
  intro h0
  have := h μ 𝓕 hμ v f hf hP k hk
  rw [h0] at this
  simp at this

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 ∧ SuppF V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  constructor <;> intro a b <;> simp [this]

theorem schur_hyp_scalar (ψ : AddChar (AF D.host.F) ℂ) (S T' : HSp D) (c : ℂ) (w : WO S T') (f : WO S T' → ℂ) :
    (c • (LinearMap.id : Module.End ℂ (WO S T' → ℂ))) (heisO ψ S T' w f) =
      heisO ψ S T' w ((c • (LinearMap.id : Module.End ℂ (WO S T' → ℂ))) f) := by
  funext x
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, heisO]
  ring

end GlobalTheory.RawLift.Model

end
