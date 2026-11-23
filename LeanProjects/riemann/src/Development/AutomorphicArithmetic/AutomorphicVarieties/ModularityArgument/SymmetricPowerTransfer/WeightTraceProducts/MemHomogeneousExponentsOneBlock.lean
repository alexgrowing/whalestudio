import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.CoeffScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.WeightDeterminantTwists.FinMH

noncomputable section

open MvPolynomial

namespace UpperTheory.V.Z.Sym.Wt

theorem trace_eq_sum_coeff {σ : Type} (V : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ V]
    (S : Finset (σ →₀ ℕ)) (hV : ∀ P, P ∈ V ↔ ∀ m ∈ P.support, m ∈ S)
    (f : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ) (F : Module.End ℂ V) (hF : ∀ P, (F P).1 = f P.1) :
    LinearMap.trace ℂ V F = ∑ m ∈ S, coeff m (f (monomial m 1)) := by
  classical
  have mem : ∀ c : S → ℂ, (∑ m : S, monomial (m : σ →₀ ℕ) (c m)) ∈ V := by
    intro c
    rw [hV]
    intro m hm
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
    have h := MvPolynomial.support_monomial_subset hi
    rw [Finset.mem_singleton] at h
    rw [h]
    exact i.2
  let e : V ≃ₗ[ℂ] (S → ℂ) :=
    { toFun := fun P m => coeff (m : σ →₀ ℕ) P.1
      map_add' := fun P Q => by
        ext m
        simp
      map_smul' := fun a P => by
        ext m
        simp
      invFun := fun c => ⟨∑ m : S, monomial (m : σ →₀ ℕ) (c m), mem c⟩
      left_inv := fun P => by
        apply Subtype.ext
        dsimp only
        conv_rhs => rw [P.1.as_sum]
        rw [Finset.sum_coe_sort S (fun m => monomial m (coeff m P.1))]
        symm
        refine Finset.sum_subset (fun m hm => (hV P.1).1 P.2 m hm) ?_
        intro m _ hm
        rw [MvPolynomial.notMem_support_iff.1 hm, map_zero]
      right_inv := fun c => by
        ext m
        simp [coeff_sum, coeff_monomial] }
  let b := Module.Basis.ofEquivFun e
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply]
  show coeff (m : σ →₀ ℕ) (F (b m)).1 = _
  rw [hF]
  have hb : (b m).1 = monomial (m : σ →₀ ℕ) 1 := by
    rw [Module.Basis.coe_ofEquivFun]
    show ∑ i : S, monomial (i : σ →₀ ℕ) (Pi.single m 1 i) = _
    rw [Finset.sum_eq_single m]
    · simp
    · intro i _ hi
      simp [Pi.single_eq_of_ne hi]
    · simp
  rw [hb]

variable {K : Type} [Fintype K] {d : ℕ}

def glue (μ : K → (Unit × Fin d →₀ ℕ)) : K × Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => μ p.1 ((), p.2)

theorem glue_apply (μ : K → (Unit × Fin d →₀ ℕ)) (k : K) (i : Fin d) : glue μ (k, i) = μ k ((), i) := rfl

theorem glue_injective : Function.Injective (glue : (K → (Unit × Fin d →₀ ℕ)) → _) := by
  intro μ ν h
  funext k
  ext ⟨⟨⟩, i⟩
  have h' := congrArg (fun m => m (k, i)) h
  simpa [glue_apply] using h'

def inB (k : K) (p : Unit × Fin d) : K × Fin d := (k, p.2)

private theorem glue_eq_sum_mapDomain_inB (ν : K → (Unit × Fin d →₀ ℕ)) :
    glue ν = ∑ k, (ν k).mapDomain (inB k) := by
  ext ⟨k, i⟩
  rw [glue_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single k]
  · have hinj : Function.Injective (inB (d := d) k) := by
      rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      simp only [inB, Prod.mk.injEq] at h
      rw [h.2]
    exact (Finsupp.mapDomain_apply hinj (ν k) ((), i)).symm
  · intro k' _ hk
    apply Finsupp.mapDomain_notin_range
    rintro ⟨p, hp⟩
    simp only [inB, Prod.mk.injEq] at hp
    exact hk hp.1
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem prod_rename_monomial (ν : K → (Unit × Fin d →₀ ℕ)) (c : K → ℂ) :
    ∏ k, rename (inB k) (monomial (ν k) (c k)) = monomial (glue ν) (∏ k, c k) := by
  simp_rw [rename_monomial]
  rw [← monomial_sum_prod, glue_eq_sum_mapDomain_inB]

theorem coeff_glue_prod (μ : K → (Unit × Fin d →₀ ℕ)) (P : K → MvPolynomial (Unit × Fin d) ℂ) :
    coeff (glue μ) (∏ k, rename (inB k) (P k)) = ∏ k, coeff (μ k) (P k) := by
  classical
  have hP : ∀ k, rename (inB k) (P k) =
      ∑ m ∈ (P k).support, rename (inB k) (monomial m (coeff m (P k))) := by
    intro k
    conv_lhs => rw [(P k).as_sum]
    rw [map_sum]
  simp_rw [hP]
  rw [Finset.prod_univ_sum]
  simp_rw [prod_rename_monomial]
  rw [coeff_sum]
  simp_rw [coeff_monomial, glue_injective.eq_iff]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Fintype.mem_piFinset] at h
    push_neg at h
    obtain ⟨k, hk⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact MvPolynomial.notMem_support_iff.1 hk

omit [Fintype K] in
theorem sbs_rename (g : K → GL (Fin d) ℂ) (k : K) (P : MvPolynomial (Unit × Fin d) ℂ) :
    sbs g (rename (inB k) P) = rename (inB k) (sbs (fun _ : Unit => g k) P) := by
  have h : (sbs g).comp (rename (inB k)) =
      (rename (inB k)).comp (sbs fun _ : Unit => g k) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨⟨⟩, i⟩
    simp [sbs, inB, map_sum]
  exact congrArg (fun φ => φ P) h

theorem coeff_sbs_glue (g : K → GL (Fin d) ℂ) (μ ν : K → (Unit × Fin d →₀ ℕ)) :
    coeff (glue μ) (sbs g (monomial (glue ν) 1)) =
      ∏ k, coeff (μ k) (sbs (fun _ : Unit => g k) (monomial (ν k) 1)) := by
  have h : monomial (glue ν) (1 : ℂ) = ∏ k, rename (inB k) (monomial (ν k) 1) := by
    rw [prod_rename_monomial]
    simp
  rw [h, map_prod]
  simp_rw [sbs_rename]
  exact coeff_glue_prod _ _

def deg1 (d n : ℕ) : Finset (Unit × Fin d →₀ ℕ) := Finset.finsuppAntidiag Finset.univ n

theorem mem_homogeneousExponentsOneBlock {n : ℕ} {m : Unit × Fin d →₀ ℕ} : m ∈ deg1 d n ↔ ∑ i, m ((), i) = n := by
  simp [deg1, Finset.mem_finsuppAntidiag, Fintype.sum_prod_type]

theorem trace_one_block (n : ℕ) (f : MvPolynomial (Unit × Fin d) ℂ →ₗ[ℂ] MvPolynomial (Unit × Fin d) ℂ)
    (F : Module.End ℂ (MH d fun _ : Unit => n)) (hF : ∀ P, (F P).1 = f P.1) :
    LinearMap.trace ℂ _ F = ∑ m ∈ deg1 d n, coeff m (f (monomial m 1)) := by
  haveI := finMH Unit d (fun _ : Unit => n)
  refine trace_eq_sum_coeff _ _ (fun P => ?_) f F hF
  refine (memMH Unit d (fun _ => n) P).trans ?_
  simp only [mem_homogeneousExponentsOneBlock]
  constructor
  · intro h m hm
    exact h m hm ()
  · rintro h m hm ⟨⟩
    exact h m hm

theorem symPowTrace_eq_sum_coeff (n : ℕ) (g : GL (Fin d) ℂ) :
    tr1 d n g = ∑ m ∈ deg1 d n, coeff m (sbs (fun _ : Unit => g) (monomial m 1)) :=
  trace_one_block n (sbs fun _ : Unit => g).toLinearMap _ fun _ => rfl

theorem trace_blocks [DecidableEq K] (n : K → ℕ)
    (f : MvPolynomial (K × Fin d) ℂ →ₗ[ℂ] MvPolynomial (K × Fin d) ℂ)
    (F : Module.End ℂ (MH d n)) (hF : ∀ P, (F P).1 = f P.1) :
    LinearMap.trace ℂ _ F = ∑ μ ∈ Fintype.piFinset (fun k => deg1 d (n k)),
      coeff (glue μ) (f (monomial (glue μ) 1)) := by
  classical
  haveI := finMH K d n
  have hV : ∀ P, P ∈ MH d n ↔ ∀ m ∈ P.support,
      m ∈ (Fintype.piFinset fun k => deg1 d (n k)).image glue := by
    intro P
    refine (memMH K d n P).trans ?_
    refine forall₂_congr fun m _ => ?_
    constructor
    · intro h
      refine Finset.mem_image.2 ⟨fun k => Finsupp.equivFunOnFinite.symm fun p => m (k, p.2), ?_, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro k
        rw [mem_homogeneousExponentsOneBlock]
        simpa using h k
      · ext ⟨k, i⟩
        simp [glue_apply]
    · intro hm k
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hm
      rw [Fintype.mem_piFinset] at hμ
      simp only [glue_apply]
      exact mem_homogeneousExponentsOneBlock.1 (hμ k)
  rw [trace_eq_sum_coeff (MH d n) _ hV f F hF,
    Finset.sum_image (fun x _ y _ h => glue_injective h)]

end UpperTheory.V.Z.Sym.Wt

end
