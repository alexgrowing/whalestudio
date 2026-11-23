import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.TwistHatMx

theorem homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (h : Matrix (Fin m) (Fin n) D.host.E) (hh : h ∈ homLat Λ Λ') : q * h * j ∈ homLat M M' := by
  intro y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hq _ (hh _ (hj _ hy))

theorem smul_homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Matrix (Fin m) (Fin n) D.host.E) (hx : x ∈ 𝔪 • homLat Λ Λ') : q * x * j ∈ 𝔪 • homLat M M' := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc h hh
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem_smul hc (homLat_conj j q hj hq h hh)
  · intro a b ha hb
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ ha hb

theorem gen_conj {D : D7} {m n m' n' : ℕ} (a : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) :
    rat q * (Matrix.of fun i k => a ⊗ₜ[D.host.F] x i k) * rat j = Matrix.of fun i k => a ⊗ₜ[D.host.F] (q * x * j) i k := by
  have e : ∀ {r s : ℕ} (y : Matrix (Fin r) (Fin s) D.host.E), (Matrix.of fun i k => a ⊗ₜ[D.host.F] y i k) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • rat y := by
    intro r s y
    ext i k
    simp [rat, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [rat, Matrix.map_mul]

theorem rat_conj_mem_hatMx {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Mx D m n) (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    rw [gen_conj]
    exact AddSubgroup.subset_closure ⟨α, hα, q * y * j, smul_homLat_conj 𝔪 j q hj hq y hy, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha =>
    rw [Matrix.mul_neg, Matrix.neg_mul]
    exact AddSubgroup.neg_mem _ ha

end GlobalTheory.TwistHatMx
