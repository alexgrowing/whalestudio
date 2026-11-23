import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalRingCardinality.DataBu
import Formalism.QuotientMetricDivisors.FinalW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRangeInfKerEqSpanRationalKer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem perCol_base_smul_form (D : D7) (u : D.what₂.Word) (φ : D.what₂.Mu u) (c : ℂ)
    (F : D.what₂.Amb D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ (c • F) = c * D.what₂.perCol u D.what₂.mu0 φ F := by
  simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, smul_eq_mul]

theorem perCol_eq_pairing_of_kills (D : D7) (h : Formalism.BasicNotions.Rows.BuDefQ D.what₂) (u : D.what₂.Word)
    (φ : D.what₂.Mu u)
    (hK : ∀ F ∈ D.what₂.Usp D.what₂.mu0, D.what₂.perCol u D.what₂.mu0 φ F = 0)
    (F : D.what₂.Amb D.what₂.mu0) (hF : F ∈ D.what₂.V0 D.what₂.mu0) :
    D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F) := by
  set n : D.what₂.Amb D.what₂.mu0 := (D.what₂.Usp D.what₂.mu0).starProjection F with hn
  have hnU : n ∈ D.what₂.Usp D.what₂.mu0 := Submodule.starProjection_apply_mem _ _
  have hq : F - n ∈ D.what₂.Qsp D.what₂.mu0 :=
    ⟨Submodule.sub_mem _ hF hnU.1, Submodule.sub_starProjection_mem_orthogonal F⟩
  have hι : D.what₂.iota D.what₂.mu0 F = D.what₂.iota D.what₂.mu0 (F - n) := by
    have : D.what₂.iota D.what₂.mu0 n = 0 := hnU.2
    rw [map_sub, this, sub_zero]
  have hF' : F = (F - n) + n := by abel
  rw [h u φ, hι, D.what₂.sec_iota _ _ hq]
  conv_lhs => rw [hF']
  rw [D.perCol_add, hK n hnU, add_zero]

theorem span_range_inf_ker_le_of_basis {K : Type} [Field K] (σ : K →+* ℂ) {W E A I : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] [AddCommGroup A] [Module K A]
    [Finite I] {n : ℕ} (b : Module.Basis I K A)
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : A →ₛₗ[σ] E) (f : W →ₗ[ℂ] E) (g : (Fin n → K) →ₗ[K] A)
    (hli : LinearIndependent ℂ (fun i => j' (b i))) (hf : ∀ x, f (j x) = j' (g x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f = Submodule.span ℂ (j '' {x | g x = 0}) := by
  classical
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  let b' := b.reindex e
  let M := LinearMap.toMatrix' (b'.equivFun.toLinearMap ∘ₗ g)
  have hM : ∀ x, M.mulVec x = b'.equivFun (g x) := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  have key := span_range_inf_ker_eq_span_rational_ker σ j
    (j'.comp b'.equivFun.symm.toLinearMap) f M ?_ ?_
  · rw [key]
    congr 2
    ext x
    simp only [Set.mem_setOf_eq, hM, EmbeddingLike.map_eq_zero_iff]
  · have h1 : (fun l => (j'.comp b'.equivFun.symm.toLinearMap) (Pi.single l 1))
        = (fun i => j' (b i)) ∘ e.symm := by
      funext l
      simp [b', Pi.single_apply]
    rw [h1]
    exact hli.comp _ e.symm.injective
  · intro x
    rw [hf, hM]
    simp

end GlobalTheory
