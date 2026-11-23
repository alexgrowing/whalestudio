import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

namespace FlagIntMuProd

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def sliceEmb (τ : Ψ) (i : Fin N) : Ψ × Fin N := (τ, i)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem sliceEmb_injective (τ : Ψ) : Function.Injective (sliceEmb (N := N) τ) := by
  intro a b h
  simpa [sliceEmb] using h

def glue (d : Ψ → (Fin N →₀ ℕ)) : Ψ × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => d p.1 p.2

omit [DecidableEq Ψ] in
theorem glue_injective : Function.Injective (glue (Ψ := Ψ) (N := N)) := by
  intro d e h
  funext τ
  ext i
  have := congrArg (fun g : Ψ × Fin N →₀ ℕ => g (τ, i)) h
  simpa [glue] using this

theorem sum_mapDomain_sliceEmb (A : Ψ → (Fin N →₀ ℕ)) :
    ∑ τ, Finsupp.mapDomain (sliceEmb τ) (A τ) = glue A := by
  ext ⟨σ, i⟩
  rw [Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single σ]
  · rw [show ((σ, i) : Ψ × Fin N) = sliceEmb σ i from rfl, Finsupp.mapDomain_apply (sliceEmb_injective σ)]
    rfl
  · intro τ _ hτ
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact hτ (congrArg Prod.fst ha)
  · intro h
    exact absurd (Finset.mem_univ σ) h

theorem coeff_glue_prod (r : Ψ → MvPolynomial (Fin N) ℚ) (d : Ψ → (Fin N →₀ ℕ)) :
    coeff (glue d) (∏ τ, rename (sliceEmb τ) (r τ)) = ∏ τ, coeff (d τ) (r τ) := by
  have h : ∀ τ, rename (sliceEmb τ) (r τ) =
      ∑ a ∈ (r τ).support, monomial (Finsupp.mapDomain (sliceEmb τ) a) (coeff a (r τ)) := by
    intro τ
    conv_lhs => rw [as_sum (r τ)]
    rw [map_sum]
    simp only [rename_monomial]
  simp_rw [h]
  rw [Finset.prod_univ_sum]
  simp_rw [← monomial_sum_prod, sum_mapDomain_sliceEmb, coeff_sum, coeff_monomial,
    glue_injective.eq_iff]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [Fintype.mem_piFinset] at hd
    push Not at hd
    obtain ⟨τ, hτ⟩ := hd
    exact (Finset.prod_eq_zero (Finset.mem_univ τ) (notMem_support_iff.mp hτ)).symm

variable (N) in

def rhoOne : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => N - 1 - (i : ℕ)

variable (N) in

def flagIntOne (q : MvPolynomial (Fin N) ℚ) : ℚ :=
  ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℚ) * coeff (rhoOne N) (rename σ q)

omit [DecidableEq Ψ] in
theorem rhoMono_eq_glue : rhoMono Ψ N = glue fun _ => rhoOne N := by
  ext p
  rfl

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rename_weylAct_sliceEmb (w : Ψ → Equiv.Perm (Fin N)) (τ : Ψ) (q : MvPolynomial (Fin N) ℚ) :
    rename (weylAct Ψ N w) (rename (sliceEmb τ) q) = rename (sliceEmb τ) (rename (w τ) q) := by
  rw [rename_rename, rename_rename]
  rfl

theorem flagInt_prod (q : Ψ → MvPolynomial (Fin N) ℚ) :
    flagInt Ψ N (∏ τ, rename (sliceEmb τ) (q τ)) = ∏ τ, flagIntOne N (q τ) := by
  unfold flagInt antisym flagIntOne
  rw [coeff_sum, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [coeff_smul, map_prod, rhoMono_eq_glue]
  simp_rw [rename_weylAct_sliceEmb]
  rw [coeff_glue_prod, weylSign, smul_eq_mul, ← Finset.prod_mul_distrib]

theorem flagIntOne_eq_zero_of_isHomogeneous {q : MvPolynomial (Fin N) ℚ} {D : ℕ} (hq : q.IsHomogeneous D)
    (hD : (rhoOne N).degree ≠ D) : flagIntOne N q = 0 := by
  unfold flagIntOne
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [(hq.rename_isHomogeneous).coeff_eq_zero hD, mul_zero]

end FlagIntMuProd

end GroundTheory.Heights₂.Heights.LowerBoundFree
