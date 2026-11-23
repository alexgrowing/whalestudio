import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

def polMapD (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (Σ w, Λ w) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Sigma.mk w)).toLinearMap)

theorem polMapD_tprod (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (q : ∀ w, MvPolynomial (Λ w) ℂ) :
    polMapD W Λ (PiTensorProduct.tprod ℂ q) = ∏ v, MvPolynomial.rename (Sigma.mk v) (q v) := by
  simp [polMapD]

theorem polMapD_index_injective (W : Type) [Fintype W] (Λ : W → Type) :
    Function.Injective (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
  have key : ∀ (f : ∀ w, (Λ w →₀ ℕ)) (w : W) (l : Λ w),
      (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) ⟨w, l⟩ = f w l := by
    intro f w l
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply sigma_mk_injective _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Sigma.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (Σ w, Λ w) →₀ ℕ => F ⟨w, l⟩) h

theorem polMapD_tprod_monomial (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (f : ∀ w, (Λ w →₀ ℕ)) :
    polMapD W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial (Λ w) ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMapD, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMapD_injective (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    Function.Injective (polMapD W Λ) := by
  let B := Basis.piTensorProduct (fun w : W => basisMonomials (Λ w) ℂ)
  have hli : LinearIndependent ℂ (polMapD W Λ ∘ B) := by
    have h := (basisMonomials (Σ w, Λ w) ℂ).linearIndependent.comp _ (polMapD_index_injective W Λ)
    have e : polMapD W Λ ∘ B = (basisMonomials (Σ w, Λ w) ℂ) ∘
        (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMapD_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMapD W Λ ∘ₗ Finsupp.linearCombination ℂ B =
      Finsupp.linearCombination ℂ (polMapD W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

theorem atPl_tprod_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W)
    (L : Module.End ℂ (MvPolynomial (Λ w) ℂ)) (p : ∀ v, MvPolynomial (Λ v) ℂ) :
    atPl (V := fun w => MvPolynomial (Λ w) ℂ) w L (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (L (p w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext v
  by_cases hv : v = w
  · subst hv; simp
  · simp [Function.update_of_ne hv]

theorem polMapD_atPl_mulLeft_X (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X ⟨w, l⟩) ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Sigma.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

theorem pderiv_rename_sigmaMk_of_ne {W : Type} {Λ : W → Type} {v w : W} (h : v ≠ w) (l : Λ w)
    (r : MvPolynomial (Λ v) ℂ) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (MvPolynomial.rename (Sigma.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Sigma.fst e)

theorem pderiv_prod_rename_sigma_of_notMem {W : Type} {Λ : W → Type} {w : W} (l : Λ w)
    (q : ∀ v, MvPolynomial (Λ v) ℂ) (s : Finset W) (hs : w ∉ s) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (∏ v ∈ s, MvPolynomial.rename (Sigma.mk v) (q v)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_sigmaMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMapD_atPl_pderiv (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w)).toLinearMap ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i)
      (Function.update q w ((MvPolynomial.pderiv l).toLinearMap (q w)) i) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_sigma_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename sigma_mk_injective l (q w)]
  simp [mul_comm]

theorem exists_polMapD : ∀ (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type),
    ∃ θ : (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ, Function.Injective θ ∧
      ∀ (w : W) (l : Λ w) (T : ⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ),
        θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T) =
            MvPolynomial.X ⟨w, l⟩ * θ T ∧
          θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap T) =
            MvPolynomial.pderiv ⟨w, l⟩ (θ T) := by
  intro W _ _ Λ
  refine ⟨polMapD W Λ, polMapD_injective W Λ, fun w l T => ⟨?_, ?_⟩⟩
  · exact LinearMap.congr_fun (polMapD_atPl_mulLeft_X W Λ w l) T
  · exact LinearMap.congr_fun (polMapD_atPl_pderiv W Λ w l) T

end GlobalTheory.CCRFock

end
