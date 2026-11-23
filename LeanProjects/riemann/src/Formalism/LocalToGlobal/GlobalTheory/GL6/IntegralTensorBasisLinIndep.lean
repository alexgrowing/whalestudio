import Formalism.LocalToGlobal.GlobalTheory.GL6.LocalBasisChangeDecompCompatible
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial

variable (D : D7)

theorem tensor_sum_expand {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (y : ∀ τ, κ τ → MvPolynomial (Fin N × Fin N) ℂ) (c : ∀ τ, κ τ → ℂ) :
    Formalism.L2.Forms.ten (fun τ => ∑ i, c τ i • y τ i) =
      ∑ g : (∀ τ, κ τ), (∏ τ, c τ (g τ)) • Formalism.L2.Forms.ten (fun τ => y τ (g τ)) := by
  simp only [Formalism.L2.Forms.ten, map_sum, smul_eq_C_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [map_mul, rename_C, Finset.prod_mul_distrib, map_prod]

theorem integral_span_eq_tensor_span (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    [∀ τ, Fintype (κ τ)] (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    ((Formalism.L2.Forms.IntSpan D w lam : AddSubgroup _) : Set (MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ)) =
      (Submodule.span (bwA_Ow D w) (Set.range fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ =>
        MvPolynomial.map (Int.castRingHom ℂ) ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ))) : Set _) := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    induction hp using AddSubgroup.closure_induction with
    | mem p hp =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hp
      have hfe : ∀ τ, MvPolynomial.map (Int.castRingHom ℂ) (f τ) =
          ∑ i, (((b τ).repr ⟨f τ, hf τ⟩ i : ℤ) : ℂ) • MvPolynomial.map (Int.castRingHom ℂ)
            ((b τ i : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ) := by
        intro τ
        have h1 := congrArg (fun x : delSq ℤ N (lam τ) => MvPolynomial.map (Int.castRingHom ℂ)
          (x : MvPolynomial (Fin N × Fin N) ℤ)) ((b τ).sum_repr ⟨f τ, hf τ⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_zsmul] at h1
        rw [← h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Int.cast_smul_eq_zsmul]
      have hx : Formalism.L2.Forms.ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) =
          ∑ g : (∀ τ, κ τ), (∏ τ, (((b τ).repr ⟨f τ, hf τ⟩ (g τ) : ℤ) : ℂ)) • Formalism.L2.Forms.ten (fun τ =>
            MvPolynomial.map (Int.castRingHom ℂ) ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) := by
        rw [show (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ)) = fun τ => ∑ i,
          (((b τ).repr ⟨f τ, hf τ⟩ i : ℤ) : ℂ) • MvPolynomial.map (Int.castRingHom ℂ)
            ((b τ i : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ) from funext hfe]
        exact tensor_sum_expand κ _ _
      rw [SetLike.mem_coe, hx, Finset.smul_sum]
      refine Submodule.sum_mem _ fun g _ => ?_
      rw [smul_smul]
      have hmem : D.what₂.embLL r * ∏ τ, (((b τ).repr ⟨f τ, hf τ⟩ (g τ) : ℤ) : ℂ) ∈ bwA_Ow D w :=
        (bwA_Ow D w).mul_mem ⟨r, hr, rfl⟩ ((bwA_Ow D w).prod_mem fun τ _ => intCast_mem _ _)
      exact Submodule.smul_mem _ (⟨_, hmem⟩ : bwA_Ow D w) (Submodule.subset_span ⟨g, rfl⟩)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => exact Submodule.neg_mem _ hx
  · intro p hp
    replace hp : p ∈ Submodule.span (bwA_Ow D w) _ := hp
    rw [SetLike.mem_coe]
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨1, fun τ => ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ),
        (intW D.what₂.places w).one_mem, fun τ => (b τ (g τ)).2, ?_⟩
      rw [map_one, one_smul]
    | zero => exact (Formalism.L2.Forms.IntSpan D w lam).zero_mem
    | add x y _ _ hx hy => exact (Formalism.L2.Forms.IntSpan D w lam).add_mem hx hy
    | smul o x _ hx =>
      obtain ⟨o, ⟨r, hr, rfl⟩⟩ := o
      exact bwG_intSpan_smul D w lam r hr hx

theorem integral_tensor_basis_lin_indep (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    LinearIndependent (bwA_Ow D w) (fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ =>
      MvPolynomial.map (Int.castRingHom ℂ) ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ))) := by
  classical
  have hinj : Function.Injective fun c : bwA_Ow D w => c • (1 : ℂ) := by
    intro x y h; simpa using h
  exact (tensor_weyl_basis_lin_indep lam κ b).restrict_scalars hinj

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
