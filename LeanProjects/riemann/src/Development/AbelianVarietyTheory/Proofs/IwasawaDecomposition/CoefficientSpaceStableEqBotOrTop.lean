import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorIrr

open Formalism.L2.DIV

section General

variable {K : Type} [Field K] {n : ℕ}

def bSq (lam : DomWeight n) : Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) K (nablaSq K n lam) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW).choose_spec.1.2.1)

theorem bSq_coe (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ((bSq (K := K) lam k : nablaSq K n lam) : MvPolynomial (Fin n × Fin n) K) = ssB K lam.natW k := by
  simp [bSq, Module.Basis.span_apply, ssB]
  rfl

theorem ssB_mem (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ssB K lam.natW k ∈ nablaSq K n lam :=
  bSq_coe (K := K) lam k ▸ (bSq (K := K) lam k).2

theorem sqAct_one_of_mem (lam : DomWeight n) {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ nablaSq K n lam) :
    sqAct K n lam 1 f = f :=
  congrArg Subtype.val (LinearMap.congr_fun (GlobalTheory.Branching.sqRep K n lam).map_one ⟨f, hf⟩)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tenAt (f : ι → MvPolynomial (Fin n × Fin n) K) (τ₀ : ι) : MvPolynomial (Fin n × Fin n) K →ₗ[K] Pol K ι n :=
  LinearMap.mulLeft K (∏ τ ∈ Finset.univ.erase τ₀, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∘ₗ
    (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ₀).toLinearMap

theorem tenAt_apply (f : ι → MvPolynomial (Fin n × Fin n) K) (τ₀ : ι) (x : MvPolynomial (Fin n × Fin n) K) :
    tenAt f τ₀ x = ten (Function.update f τ₀ x) := by
  simp only [tenAt, ten, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem ten_update_ssB (lam : ι → DomWeight n) (τ₀ : ι) (k : VVIdx lam) (l : Formalism.GradedWeylDivisibility.ssIdx n n (lam τ₀).natW) :
    ten (Function.update (fun τ => ssB K (lam τ).natW (k τ)) τ₀ (ssB K (lam τ₀).natW l)) =
      ((bVV K lam (Function.update k τ₀ l) : VV K lam) : Pol K ι n) := by
  rw [bVV_coe, bVVfun]
  congr 1
  funext τ
  exact (Function.apply_update (fun τ k => ssB K (lam τ).natW k) k τ₀ l τ).symm

theorem exists_op (lam : ι → DomWeight n) (τ₀ : ι) (φ : nablaSq K n (lam τ₀) →ₗ[K] nablaSq K n (lam τ₀))
    (hφ : ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K), ∀ f : nablaSq K n (lam τ₀),
      (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ₀) g f)
    (W : Submodule K (VV K lam)) (hW : ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, rhoK lam g w ∈ W) :
    ∃ T : VV K lam →ₗ[K] VV K lam, (∀ w ∈ W, T w ∈ W) ∧ ∀ k : VVIdx lam,
      ((T (bVV K lam k) : VV K lam) : Pol K ι n) =
        ten (Function.update (fun τ => ssB K (lam τ).natW (k τ)) τ₀
          (φ (bSq (lam τ₀) (k τ₀)) : MvPolynomial (Fin n × Fin n) K)) := by
  obtain ⟨s, c, hc⟩ := hφ
  refine ⟨∑ g ∈ s, c g • rhoK lam (Function.update 1 τ₀ g), ?_, ?_⟩
  · intro w hw
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun g _ => by
      rw [LinearMap.smul_apply]
      exact W.smul_mem _ (hW _ _ hw)
  · intro k
    rw [hc, bSq_coe, ← tenAt_apply, map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, map_smul]
    congr 1
    rw [rhoK_coe, bVV_coe, bVVfun, actTen K ι n lam _ _, tenAt_apply]
    congr 1
    funext τ
    by_cases h : τ = τ₀
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, Pi.one_apply, sqAct_one_of_mem _ (ssB_mem _ _)]

def elemOp (lam : DomWeight n) (a b : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : nablaSq K n lam →ₗ[K] nablaSq K n lam :=
  ((bSq lam).coord a).smulRight (bSq lam b)

theorem exists_elem (lam : ι → DomWeight n)
    (H : ∀ τ, ∀ φ : nablaSq K n (lam τ) →ₗ[K] nablaSq K n (lam τ), ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K),
      ∀ f : nablaSq K n (lam τ), (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ) g f)
    (W : Submodule K (VV K lam)) (hW : ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, rhoK lam g w ∈ W)
    (τ₀ : ι) (a b : Formalism.GradedWeylDivisibility.ssIdx n n (lam τ₀).natW) :
    ∃ T : VV K lam →ₗ[K] VV K lam, (∀ w ∈ W, T w ∈ W) ∧ ∀ k : VVIdx lam,
      T (bVV K lam k) = if k τ₀ = a then bVV K lam (Function.update k τ₀ b) else 0 := by
  obtain ⟨T, hTW, hT⟩ := exists_op lam τ₀ (elemOp (lam τ₀) a b) (H τ₀ _) W hW
  refine ⟨T, hTW, fun k => Subtype.ext ?_⟩
  rw [hT k]
  have e : (elemOp (K := K) (lam τ₀) a b (bSq (lam τ₀) (k τ₀)) : MvPolynomial (Fin n × Fin n) K) =
      (if k τ₀ = a then (1 : K) else 0) • ssB K (lam τ₀).natW b := by
    simp only [elemOp, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, Submodule.coe_smul, bSq_coe]
  rw [e, ← tenAt_apply, map_smul, tenAt_apply, ten_update_ssB]
  split_ifs <;> simp

end General

theorem eq_bot_or_eq_top : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ τ, ∀ φ : nablaSq K n (lam τ) →ₗ[K] nablaSq K n (lam τ), ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K),
      ∀ f : nablaSq K n (lam τ), (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ) g f) →
    ∀ W : Submodule K (Formalism.L2.DIV.VV K lam), (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro K _ ι _ n lam H W hW
  classical
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i, hi⟩ : ∃ i, (bVV K lam).repr w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((bVV K lam).ext_elem fun k => by simp [h k])
  have hproj : ∀ S : Finset ι, (∑ k ∈ Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ S, k τ = i τ),
      (bVV K lam).repr w k • bVV K lam k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · have hf : Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ (∅ : Finset ι), k τ = i τ) = Finset.univ := by
        ext k; simp
      rw [hf, (bVV K lam).sum_repr w]
      exact hw
    · intro a S ha ih
      obtain ⟨T, hTW, hT⟩ := exists_elem lam H W hW a (i a) (i a)
      have h1 := hTW _ ih
      rw [map_sum] at h1
      convert h1 using 1
      simp only [map_smul, hT]
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k a = i a
      · have hu : Function.update k a (i a) = k := by rw [← hk, Function.update_eq_self]
        simp [hk, hu, Finset.forall_mem_insert]
      · simp [hk, Finset.forall_mem_insert]
  have hi' : bVV K lam i ∈ W := by
    have h := hproj Finset.univ
    have hf : Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ (Finset.univ : Finset ι), k τ = i τ) = {i} := by
      ext k; simp [funext_iff]
    rw [hf, Finset.sum_singleton] at h
    have := W.smul_mem ((bVV K lam).repr w i)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this
  have hall : ∀ j, bVV K lam j ∈ W := by
    intro j
    have key : ∀ S : Finset ι, bVV K lam (fun τ => if τ ∈ S then j τ else i τ) ∈ W := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · simpa using hi'
      · intro a S ha ih
        obtain ⟨T, hTW, hT⟩ := exists_elem lam H W hW a (i a) (j a)
        have h1 := hTW _ ih
        rw [hT, if_pos (by simp [ha])] at h1
        convert h1 using 2
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · simp [h, Function.update_of_ne h]
    simpa using key Finset.univ
  rw [eq_top_iff]
  intro x _
  rw [← (bVV K lam).sum_repr x]
  exact W.sum_mem fun k _ => W.smul_mem _ (hall k)

end GlobalTheory.TensorIrr
