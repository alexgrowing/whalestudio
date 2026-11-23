import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAdjointOrthogonalInjective

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair GlobalTheory.FockAlg

namespace GlobalTheory.FockProj

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

theorem inner_homog_eq (hι : IsFockIP ι) {n : ℕ} {h : MvPolynomial σ ℂ} (hh : h.IsHomogeneous n)
    (g : MvPolynomial σ ℂ) :
    inner ℂ (ι h) (ι g) = inner ℂ (ι h) (ι (homogeneousComponent n g)) := by
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [map_sum, inner_sum]
  by_cases hn : n ∈ Finset.range (g.totalDegree + 1)
  · rw [Finset.sum_eq_single_of_mem n hn]
    intro m _ hmn
    exact GlobalTheory.FockAdj.inner_eq_zero_of_isHomogeneous hι (Ne.symm hmn) hh
      (homogeneousComponent_isHomogeneous m g)
  · have hlt : g.totalDegree < n := by simp at hn; omega
    rw [homogeneousComponent_eq_zero n g hlt, map_zero, inner_zero_right]
    refine Finset.sum_eq_zero fun m hm => ?_
    have : m ≠ n := by simp at hm; omega
    exact GlobalTheory.FockAdj.inner_eq_zero_of_isHomogeneous hι (Ne.symm this) hh
      (homogeneousComponent_isHomogeneous m g)

theorem isCompl_orth [Finite σ] (hι : IsFockIP ι) (hinj : Function.Injective ι)
    (W : Submodule ℂ (MvPolynomial σ ℂ)) (hW : ∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) :
    IsCompl W ((W.map ι)ᗮ.comap ι) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxC
    have h0 : inner ℂ (ι x) (ι x) = 0 :=
      (Submodule.mem_orthogonal _ _).1 (Submodule.mem_comap.1 hxC) (ι x) (Submodule.mem_map_of_mem hx)
    rw [inner_self_eq_zero] at h0
    exact hinj (by rw [h0, map_zero])
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro f
    rw [← sum_homogeneousComponent f]
    refine Submodule.sum_mem _ fun n _ => ?_
    set h := homogeneousComponent n f
    have hh : h.IsHomogeneous n := homogeneousComponent_isHomogeneous n f
    let Wn : Submodule ℂ (MvPolynomial σ ℂ) := W ⊓ homogeneousSubmodule σ ℂ n
    haveI : FiniteDimensional ℂ (homogeneousSubmodule σ ℂ n) :=
      Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ ℂ n)
    haveI : FiniteDimensional ℂ Wn := Submodule.finiteDimensional_of_le inf_le_right
    let K : Submodule ℂ H := Wn.map ι
    haveI : FiniteDimensional ℂ K := inferInstance
    obtain ⟨w, hwWn, hwk⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem (ι h))
    have hwn : w.IsHomogeneous n := (mem_homogeneousSubmodule n w).1 hwWn.2
    refine Submodule.mem_sup.2 ⟨w, hwWn.1, h - w, ?_, add_sub_cancel _ _⟩
    rw [Submodule.mem_comap, Submodule.mem_orthogonal]
    rintro v ⟨w', hw', rfl⟩
    rw [inner_eq_zero_symm, inner_homog_eq hι (hh.sub hwn), map_sub, hwk]
    refine Submodule.starProjection_inner_eq_zero (K := K) _ _ ?_
    exact Submodule.mem_map_of_mem ⟨hW w' hw' n, homogeneousComponent_mem n w'⟩

theorem exists_equivariant_proj : ∀ (p q r s : ℕ) (W : Submodule ℂ (Pol p q r s)),
    (∀ Z, ∀ f ∈ W, fockAct1 p q r s Z f ∈ W) → (∀ f ∈ W, ∀ n, homogeneousComponent n f ∈ W) →
    ∃ π : Pol p q r s →ₗ[ℂ] Pol p q r s, (∀ f, π f ∈ W) ∧ (∀ f ∈ W, π f = f) ∧
      ∀ Z f, π (fockAct1 p q r s Z f) = fockAct1 p q r s Z (π f) := by
  intro p q r s W hst hgr
  obtain ⟨ι, hι, hinj⟩ := GlobalTheory.FischerParts.exists_fockIP (Ln p q r s)
  set C : Submodule ℂ (Pol p q r s) := (W.map ι)ᗮ.comap ι with hCdef
  have hc : IsCompl W C := isCompl_orth hι hinj W hgr
  have hCst : ∀ Z, ∀ u ∈ C, fockAct1 p q r s Z u ∈ C := by
    intro Z u hu
    rw [hCdef, Submodule.mem_comap, Submodule.mem_orthogonal] at hu ⊢
    rintro v ⟨w, hw, rfl⟩
    rw [inner_eq_zero_symm,
      (GlobalTheory.FockAdj.fock_adjoints p q r s _ ι hι).2.1 Z u w, inner_eq_zero_symm]
    exact hu _ (Submodule.mem_map_of_mem (hst _ w hw))
  let π : Pol p q r s →ₗ[ℂ] Pol p q r s := W.subtype ∘ₗ W.linearProjOfIsCompl C hc
  have hmem : ∀ f, π f ∈ W := fun f => (W.linearProjOfIsCompl C hc f).2
  have hπW : ∀ f ∈ W, π f = f := fun f hf =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨f, hf⟩)
  have hπC : ∀ u ∈ C, π u = 0 := fun u hu => by
    have h0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 hu
    exact (congrArg Subtype.val h0).trans rfl
  have hsub : ∀ f, f - π f ∈ C := fun f => by
    have key : W.linearProjOfIsCompl C hc (π f) = W.linearProjOfIsCompl C hc f :=
      Submodule.linearProjOfIsCompl_apply_left hc (W.linearProjOfIsCompl C hc f)
    have h1 := (W.linearProjOfIsCompl C hc).map_sub f (π f)
    rw [key, sub_self] at h1
    exact (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).1 h1
  refine ⟨π, hmem, hπW, fun Z f => ?_⟩
  have hf : f = π f + (f - π f) := (add_sub_cancel _ _).symm
  conv_lhs => rw [hf]
  rw [map_add, map_add, hπW _ (hst Z _ (hmem f)), hπC _ (hCst Z _ (hsub f)), add_zero]

end GlobalTheory.FockProj
