import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ArchUniq
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

def trPairL {κ : Type} [Fintype κ] (z : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
    (∑ i, (LinearMap.mulLeft ℝ (z i)).comp (LinearMap.proj i))

theorem trPairL_apply {κ : Type} [Fintype κ] (z w : κ → mixedEmbedding.mixedSpace F) :
    trPairL z w = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * w i) := by
  simp [trPairL, LinearMap.sum_apply]

theorem fderiv_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ)
    (z v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (⇑f) z v = ∑ j, (b.repr v j : ℂ) * fderiv ℝ (⇑f) z (b j) := by
  calc fderiv ℝ (⇑f) z v = fderiv ℝ (⇑f) z (∑ j, b.repr v j • b j) := by rw [b.sum_repr]
    _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]

theorem mult_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (y : κ → AF F)
    (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) * mult F (liftV (b j)) z := by
  have h1 : ∀ w : κ → AF F, trForm F w z = trPairL z (fun i => evI F (w i)) := by
    intro w
    rw [trForm_apply, trPairL_apply]
  have h2 : trPairL z (fun i => evI F (y i)) =
      ∑ j, b.repr (fun i => evI F (y i)) j * trPairL z (b j) := by
    calc trPairL z (fun i => evI F (y i))
        = trPairL z (∑ j, b.repr (fun i => evI F (y i)) j • b j) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
  have h3 : ∀ j, (fun i => evI F (liftV (F := F) (b j) i)) = b j := fun j => Coord.loc_lift (b j)
  simp only [mult_apply, h1, h3, h2]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.HeisDerivSpan

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_eq {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f g : SInf F (Fin n × Fin d))
    (hg : ActsD (evI F) (M.heisLine ψ u) f g) :
    g = heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f := by
  ext y
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hr := hR f
  set x : Fin n × Fin d → AF F := liftV y with hx
  have hd1 := hg R hr x
  have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
  have huniq := hd1.unique hd2
  have hRx : R x = R 0 := by
    have := hr.1 0 x (at_liftV y)
    rwa [zero_add] at this
  have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
  simp only [tens, hlx, hRx] at huniq
  exact mul_right_cancel₀ hR0 huniq

theorem heisLine_deriv_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ
  let b := Module.finBasis ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  set N := Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  let A : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (LineDeriv.lineDerivOpCLM ℂ (SInf F (Fin n × Fin d)) (b j)).toLinearMap
  let B : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (SchwartzMap.smulLeftCLM ℂ (⇑(mult F (liftV (b j))))).toLinearMap
  refine ⟨N + N, fun i => Sum.elim A B (finSumFinEquiv.symm i), fun u _ => ?_⟩
  refine ⟨heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2, fun f f₁ =>
    ⟨actsD_heisLine_eq M ψ hψ u f f₁, fun h => by subst h; exact actsD_heisLine_heisD M ψ hψ u f⟩, fun f => ?_⟩
  set S := Submodule.span ℂ (Set.range fun i => Sum.elim A B (finSumFinEquiv.symm i) f) with hS
  have hA : ∀ j, A j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inl j), by simp only [Equiv.symm_apply_apply, Sum.elim_inl]⟩
  have hB : ∀ j, B j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inr j), by simp only [Equiv.symm_apply_apply, Sum.elim_inr]⟩
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hv
  set y := (M.co.e u).2 with hy
  have key : heisD F v y f = ∑ j, (b.repr v j : ℂ) • A j f +
      ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) • B j f := by
    ext z
    rw [heisD_apply, fderiv_basis b f z v, mult_basis b y z, Finset.sum_mul]
    simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, A, B,
      ContinuousLinearMap.coe_coe, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.smulLeftCLM_apply_apply (mult F (liftV (F := F) (b j))).hasTemperateGrowth]
    simp only [smul_eq_mul]
    ring
  rw [key]
  exact add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hA j))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB j))

end GlobalTheory.HeisDerivSpan
