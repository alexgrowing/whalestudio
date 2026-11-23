import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.HeisLineDiffF

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local instance isModTopAEF : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩

theorem finiteDimensional_FE : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E

local instance : FiniteDimensional F E := finiteDimensional_FE

local instance topRingAEF : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_sigR_AF (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add a b ha hb => rw [map_add, LinearMap.map_add, ha, hb]
  rw [e]
  exact IsModuleTopology.continuous_of_linearMap _

theorem map_trace_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (p : R →ₐ[F] R')
    (y : R ⊗[F] E) :
    p (Algebra.trace R (R ⊗[F] E) y) =
      Algebra.trace R' (R' ⊗[F] E) (Algebra.TensorProduct.map p (AlgHom.id F E) y) := by
  have h1 : ∀ (S : Type) [CommRing S] [Algebra F S] (r : S) (x : E),
      Algebra.trace S (S ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F S (Algebra.trace F E x) := by
    intro S _ _ r x
    have h1 : Algebra.trace S (S ⊗[F] E) ((1 : S) ⊗ₜ[F] x) = algebraMap F S (Algebra.trace F E x) := by
      rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
    have h2 : r ⊗ₜ[F] x = r • ((1 : S) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2, LinearMap.map_smul, h1, smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h1, h1, map_mul, AlgHom.commutes]
  | add y y' hy hy' => simp only [map_add, hy, hy']

theorem finPartF_sigR (σ : E →ₐ[F] E) (z : AEF F E) :
    finPartF F E (sigR (AF F) σ z) = sigR (Af F) σ (finPartF F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)

theorem sndA_symplOHF (ξ₀ : E) (w y : WOF F E nS nT) (hy : y.map (finPartF F E) = 0) :
    sndA F (symplOHF σ JS JT ξ₀ w y) = 0 := by
  have hk : ∀ a b c d, finPartF F E (incAF F E (JS⁻¹ a b) * cAF σ (y c b) * incAF F E (JT c d) * w d a) = 0 := by
    intro a b c d
    have h0 : finPartF F E (y c b) = 0 := congrFun (congrFun hy c) b
    rw [map_mul, map_mul, map_mul, finPartF_sigR, h0, map_zero, mul_zero, zero_mul, zero_mul]
  have hh : finPartF F E (hOF σ JS JT w y) = 0 := by
    unfold hOF
    simp only [map_sum, hk, Finset.sum_const_zero]
  unfold symplOHF symplOF
  rw [map_mul, map_trace_tens]
  have e : (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (incAF F E ξ₀ * hOF σ JS JT w y) =
      finPartF F E (incAF F E ξ₀ * hOF σ JS JT w y) := rfl
  rw [e, map_mul, hh, mul_zero, map_zero, mul_zero]

theorem symplOHF_add_right (ξ₀ : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x (y + y') = symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y' := by
  unfold symplOHF symplOF hOF
  simp only [Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOHF_zero_right (ξ₀ : E) (x : WOF F E nS nT) : symplOHF σ JS JT ξ₀ x 0 = 0 := by
  have := symplOHF_add_right σ JS JT ξ₀ x 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem continuous_symplOHF (ξ₀ : E) (w : WOF F E nS nT) {X : Type} [TopologicalSpace X] {y : X → WOF F E nS nT}
    (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ₀ w (y t) := by
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_sigR_AF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hh : Continuous fun t => hOF σ JS JT w (y t) :=
    continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul continuous_const
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

theorem exists_log {Tau : Type} [Fintype Tau] {tauE : Tau → (E →+* ℂ)} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStdCharF tauE ψ (-1)) :
    ∃ lam : AF F →+ ℂ, Continuous lam ∧ ∀ a, sndA F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ ρ, θ ρ (fstA F a ⊗ₜ[F] (1 : E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA F a)
    have e : pairA F (fstA F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

end GlobalTheory.HeisLineDiffF

open Formalism.IndefR.DatumF in

theorem GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, DifferentiableAt ℝ (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log hψ
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun x y => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)
  let L' : (Fin 1 → ℝ) →+ WOF F E nS nT := L.comp (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℝ) 0)
  have hL' : Continuous L' := hL.comp (continuous_apply 0)
  have hsm := hf.smooth 1 L' hL' (fun x => hL0 (x 0)) w
  have hg : ContDiff ℝ ∞ fun t : ℝ => f (w + L' (fun _ => t)) :=
    hsm.comp (contDiff_pi.2 fun _ => contDiff_id)
  have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f w) =
      fun t : ℝ => Complex.exp (φ t) * f (w + L' (fun _ => t)) := by
    funext t
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w (L t) (hL0 t))]
    rfl
  rw [e]
  have hd1 : DifferentiableAt ℝ (fun t : ℝ => Complex.exp (φ t)) 0 :=
    ((φ.toRealLinearMap hφ).differentiableAt).cexp
  exact hd1.mul ((hg.differentiable (by simp)) 0)
