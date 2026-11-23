import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem trace_pow_rect {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (h : ∀ a b, E' a b = ∑ c, ∑ d, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c, (Matrix.of E' ^ k) c c = ∑ c, (Matrix.of E ^ k) c c := by
  first
  | exact @_root_.GlobalTheory.TracePowEq.trace_pow_eq
  | exact _root_.GlobalTheory.TracePowEq.trace_pow_eq
  | (apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TracePowEq.trace_pow_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TracePowEq.trace_pow_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TracePowEq.trace_pow_eq ..)

namespace IsoMat

variable {D : D7} {V V' : HSp D} (I : IsoMat V V') {θ : InfF D}

def trSm (hθ : IsInfFam θ) : GlobalTheory.Mem.AutSpace.SmFun θ V ≃ₗ[ℂ] GlobalTheory.Mem.AutSpace.SmFun θ V' where
  toFun φ := ⟨I.tr φ.1, I.tr_mem_SmFun hθ φ.2⟩
  invFun ψ := ⟨I.symm.tr ψ.1, I.symm.tr_mem_SmFun hθ ψ.2⟩
  left_inv φ := Subtype.ext (funext fun x => congrArg φ.1 (I.kapF_symm x))
  right_inv ψ := Subtype.ext (funext fun x => congrArg ψ.1 (I.symm.kapF_symm x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def conjSm (hθ : IsInfFam θ) :
    Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) →+* Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') where
  toFun f := (I.trSm hθ).toLinearMap ∘ₗ f ∘ₗ (I.trSm hθ).symm.toLinearMap
  map_one' := LinearMap.ext fun x => by simp
  map_mul' f g := LinearMap.ext fun x => by simp
  map_zero' := LinearMap.ext fun x => by simp
  map_add' f g := LinearMap.ext fun x => by simp

theorem conjSm_apply (hθ : IsInfFam θ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) (x : GlobalTheory.Mem.AutSpace.SmFun θ V) :
    I.conjSm hθ f (I.trSm hθ x) = I.trSm hθ (f x) := by
  show I.trSm hθ (f ((I.trSm hθ).symm (I.trSm hθ x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem conjSm_smul (hθ : IsInfFam θ) (c : ℂ) (f : Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V)) :
    I.conjSm hθ (c • f) = c • I.conjSm hθ f := LinearMap.ext fun x => by simp [conjSm]

theorem derEnd_tr (hθ : IsInfFam θ) (τ : D.what₂.Tau) (Z : Matrix (Fin V'.rank) (Fin V'.rank) ℂ) :
    GlobalTheory.Mem.RealTranslate.derEnd hθ τ Z = I.conjSm hθ (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (I.symm.adP τ Z)) := by
  refine LinearMap.ext fun ψ => ?_
  obtain ⟨φ, rfl⟩ := (I.trSm hθ).surjective ψ
  rw [conjSm_apply]
  exact Subtype.ext (I.RderC_tr hθ τ Z φ.1)

theorem symm_adP_single (τ : D.what₂.Tau) (a b : Fin V'.rank) :
    I.symm.adP τ (Matrix.single a b 1) = ∑ c, ∑ d, (I.qT τ c a * I.pT τ b d) • (Matrix.single c d 1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
  rw [matrix_eq_sum_single (I.symm.adP τ _)]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]
  congr 1
  simp [adP, pT, qT, symm, Matrix.mul_apply, Matrix.single, ite_and]

theorem gelf_tr : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ →
    ∀ (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ), φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V →
      gelf θ V' τ k (I.tr φ) = I.tr (gelf θ V τ k φ) := by
  intro D V V' I θ hθ τ k φ hφ
  let E0 : Fin V.rank → Fin V.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) :=
    fun c d => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single c d 1)
  let E' : Fin V'.rank → Fin V'.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V') :=
    fun a b => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (Matrix.single a b 1)
  have key := trace_pow_rect (fun c d => I.conjSm hθ (E0 c d)) E' (I.pT τ) (I.qT τ) (I.pT_qT τ) (I.qT_pT τ)
    (fun a b => by
      simp only [E', E0]
      rw [I.derEnd_tr hθ τ, I.symm_adP_single τ a b]
      simp only [map_sum, LinearMap.map_smul, conjSm_smul]) (k + 1)
  have hm : Matrix.of (fun c d => I.conjSm hθ (E0 c d)) = (I.conjSm hθ).mapMatrix (Matrix.of E0) := by
    ext c d; rfl
  have hs : ∑ c, (((I.conjSm hθ).mapMatrix (Matrix.of E0)) ^ (k + 1)) c c =
      I.conjSm hθ (∑ c, (Matrix.of E0 ^ (k + 1)) c c) := by
    rw [← RingHom.map_pow, map_sum]; rfl
  rw [hm, hs, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow, ← GlobalTheory.SmoothForms.gelfA_eq_sum_pow] at key
  have e1 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (I.trSm hθ ⟨φ, hφ⟩)
  have e2 := GlobalTheory.Mem.RealTranslate.gelf_eq hθ τ k (⟨φ, hφ⟩ : GlobalTheory.Mem.AutSpace.SmFun θ V)
  refine e1.trans ?_
  change (GlobalTheory.SmoothForms.gelfA E' k (I.trSm hθ ⟨φ, hφ⟩)).1 = _
  rw [key, conjSm_apply]
  show I.tr _ = I.tr _
  rw [e2]

end IsoMat
end GlobalTheory.Mem.Isom

end
