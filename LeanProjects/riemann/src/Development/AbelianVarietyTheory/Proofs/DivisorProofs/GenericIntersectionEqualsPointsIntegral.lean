import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import GroundTheory.Brauer.TensorSimple
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

theorem real_comb_integralBasis_eq_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (r : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ)
    (h : ∀ w : InfinitePlace K, ∑ i, (r i : ℂ) * w.embedding (integralBasis K i) = 0) : r = 0 := by
  have hli := (mixedEmbedding.latticeBasis K).linearIndependent
  funext i
  refine Fintype.linearIndependent_iff.mp hli r ?_ i
  refine Prod.ext ?_ ?_
  · funext w
    exact ((InfinitePlace.not_isComplex_iff_isReal.mpr w.2) (IsTotallyComplex.isComplex w.1)).elim
  · funext w
    have := h w.1
    simpa [Prod.snd_sum, Finset.sum_apply, mixedEmbedding.latticeBasis_apply,
      mixedEmbedding.mixedEmbedding_apply_isComplex, Complex.real_smul] using this

theorem psi_smul_F (G : HTGroup p) (w : InfinitePlace G.F) (x : G.F) (c : G.C) :
    G.psi w (x • c) = w.embedding x • G.psi w c := by
  rw [Algebra.smul_def, map_mul, G.psi_F]
  ext i j
  simp [Matrix.scalar_apply]

theorem psi_finBasis_linearIndependent (G : HTGroup p) (w : InfinitePlace G.F) :
    LinearIndependent ℂ (fun s => G.psi w (Module.finBasis G.F G.C s)) := by
  letI alg : Algebra G.F ℂ := w.embedding.toAlgebra
  have halg : ∀ a : G.F, algebraMap G.F ℂ a = w.embedding a := fun a => rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi w with
      commutes' := fun a => by
        change G.psi w (algebraMap G.F G.C a) = _
        rw [G.psi_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply, halg] }
  let Θ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  have hinj : Function.Injective Θ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Θ.toRingHom).resolve_right
      (by haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩; exact not_subsingleton _)
  have hΘ : ∀ c : G.C, Θ ((1 : ℂ) ⊗ₜ[G.F] c) = G.psi w c := by
    intro c
    erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hb := (Algebra.TensorProduct.basis ℂ (Module.finBasis G.F G.C)).linearIndependent
  have h2 := hb.map' Θ.toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  have e : (fun s => G.psi w (Module.finBasis G.F G.C s)) =
      Θ.toLinearMap ∘ (Algebra.TensorProduct.basis ℂ (Module.finBasis G.F G.C)) := by
    funext s
    simp only [Function.comp_apply, Algebra.TensorProduct.basis_apply, AlgHom.toLinearMap_apply, hΘ]
  rw [e]
  exact h2

def psiAll (G : HTGroup p) : G.C →ₗ[ℚ] (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) where
  toFun c := fun w i l => G.psi w c i l
  map_add' a b := by
    funext w i l
    simp
  map_smul' q c := by
    funext w i l
    rw [← algebraMap_smul G.F q c, psi_smul_F]
    simp [Rat.smul_def]

end GlobalTheory.LKCx

noncomputable section
namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

def towerBasis (G : HTGroup p) :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 G.F) × Fin (Module.finrank G.F G.C)) ℚ G.C :=
  (integralBasis G.F).smulTower (Module.finBasis G.F G.C)

theorem psiAll_towerBasis_linearIndependent (G : HTGroup p) :
    LinearIndependent ℝ (fun b => psiAll G (towerBasis G b)) := by
  haveI : IsTotallyComplex G.F := IsCMField.to_isTotallyComplex
  rw [Fintype.linearIndependent_iff]
  intro r hr
  have hw : ∀ w : InfinitePlace G.F, ∑ s, (∑ i, (r (i, s) : ℂ) * w.embedding (integralBasis G.F i)) •
      G.psi w (Module.finBasis G.F G.C s) = 0 := by
    intro w
    ext a c
    have h := congrFun (congrFun (congrFun hr w) a) c
    simp only [towerBasis, Module.Basis.smulTower_apply, psiAll, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_apply, Pi.smul_apply, psi_smul_F, Pi.zero_apply, Complex.real_smul] at h
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Finset.sum_mul, mul_assoc]
    rw [Fintype.sum_prod_type] at h
    rw [Finset.sum_comm]
    simpa [Matrix.smul_apply, mul_assoc] using h
  have hs : ∀ s, (fun i => r (i, s)) = 0 := by
    intro s
    apply real_comb_integralBasis_eq_zero
    intro w
    exact Fintype.linearIndependent_iff.mp (psi_finBasis_linearIndependent G w) _ (hw w) s
  intro b
  exact congrFun (hs b.2) b.1

theorem psiAll_liftBaseChange_injective (G : HTGroup p) :
    Function.Injective ((psiAll G).liftBaseChange ℝ) := by
  set Ψ := (psiAll G).liftBaseChange ℝ
  set bR := Algebra.TensorProduct.basis ℝ (towerBasis G)
  have hbR : ∀ b, Ψ (bR b) = psiAll G (towerBasis G b) := by
    intro b
    simp [Ψ, bR, Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← bR.sum_repr x] at hx ⊢
  simp only [map_sum, map_smul, hbR] at hx
  have h0 := Fintype.linearIndependent_iff.mp (psiAll_towerBasis_linearIndependent G) _ hx
  simp [h0]

theorem psi_linearIndependent_real : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) (e : Fin k → G.C),
    LinearIndependent ℚ e → LinearIndependent ℝ (fun j => (fun w i l => G.psi w (e j) i l :
      InfinitePlace G.F → Fin G.n → Fin G.n → ℂ)) := by
  intro p _ G k e he
  have h1 := Module.Flat.linearIndependent_one_tmul (S := ℝ) he
  have h2 := h1.map' ((psiAll G).liftBaseChange ℝ)
    (LinearMap.ker_eq_bot.mpr (psiAll_liftBaseChange_injective G))
  have e2 : (fun j => (fun w i l => G.psi w (e j) i l : InfinitePlace G.F → Fin G.n → Fin G.n → ℂ)) =
      (psiAll G).liftBaseChange ℝ ∘ (fun j => (1 : ℝ) ⊗ₜ[ℚ] e j) := by
    funext j
    simp [LinearMap.liftBaseChange_tmul, psiAll]
  rw [e2]
  exact h2

end GlobalTheory.LKCx
