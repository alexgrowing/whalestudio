import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmax

theorem tensor_decomp {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (z : M ⊗[K] N) :
    ∃ a c : N, z = b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c := by
  have h := TensorProduct.equivFinsuppOfBasisLeft_symm_apply b
    (TensorProduct.equivFinsuppOfBasisLeft b z)
  rw [LinearEquiv.symm_apply_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at h
  exact ⟨_, _, h⟩

theorem tensor_decomp_zero {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (b : Module.Basis (Fin 2) K M) (a c : N)
    (h : b 0 ⊗ₜ[K] a + b 1 ⊗ₜ[K] c = 0) : a = 0 ∧ c = 0 := by
  have h' := congrArg (TensorProduct.equivFinsuppOfBasisLeft b) h
  have h0 := DFunLike.congr_fun h' 0
  have h1 := DFunLike.congr_fun h' 1
  simp [map_add, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] at h0 h1
  exact ⟨h0, h1⟩

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

omit [IsCMField L] in
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : L) (a : AFplus L) :
    compAt L v (x ⊗ₜ[maximalRealSubfield L] a) = x ⊗ₜ[maximalRealSubfield L] (a v) := by
  simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul]
  rfl

theorem eq_zero_of_compAt (z : AL L) (hz : ∀ v, compAt L v z = 0) : z = 0 := by
  let b : Module.Basis (Fin 2) (maximalRealSubfield L) L := Module.finBasisOfFinrankEq _ _
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨A, B, hAB⟩ := tensor_decomp b z
  have hoff : ∀ w, A w = 0 ∧ B w = 0 := by
    intro w
    have h := hz w
    rw [hAB, map_add, compAt_tmul, compAt_tmul] at h
    exact tensor_decomp_zero b _ _ h
  have hA : A = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).1
  have hB : B = 0 := by
    apply DFunLike.ext; intro w; exact (hoff w).2
  rw [hAB, hA, hB]; simp

open Classical in

def sgl (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : AFplus L :=
  ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r, by
    refine Filter.mem_of_superset (Set.finite_singleton v).compl_mem_cofinite ?_
    intro w hw
    have hw' : w ≠ v := hw
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hw']
    exact zero_mem _⟩

omit [IsCMField L] in
theorem sgl_same (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) : sgl L v r v = r := by
  classical
  exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) v r

omit [IsCMField L] in
theorem sgl_ne (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L)) {w} (hw : w ≠ v) : sgl L v r w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) =>
      w.adicCompletion (maximalRealSubfield L)) hw r

omit [IsCMField L] in
theorem one_tmul_sgl_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (r : v.adicCompletion (maximalRealSubfield L))
    (hr : r ∈ v.adicCompletionIntegers (maximalRealSubfield L)) :
    ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v r : AL L) ∈ ALint L := by
  refine Subring.subset_closure (Or.inr ⟨sgl L v r, fun w => ?_, rfl⟩)
  rcases eq_or_ne w v with rfl | hw
  · rw [sgl_same]; exact hr
  · rw [sgl_ne L v r hw]; exact zero_mem _

omit [IsCMField L] in

theorem exists_lift (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
    (hy : y ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    ∃ Y ∈ ALint L, compAt L v Y = y := by
  have key : tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ≤ (ALint L).map (compAt L v) := by
    rw [tensInt, Subring.closure_le]
    rintro _ (⟨⟨_, s, rfl⟩, rfl⟩ | ⟨r, rfl⟩)
    · refine ⟨(s : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L),
        Subring.subset_closure (Or.inl ⟨s, rfl⟩), ?_⟩
      rw [compAt_tmul]; rfl
    · refine ⟨_, one_tmul_sgl_mem L v r r.2, ?_⟩
      rw [compAt_tmul, sgl_same]
  exact key hy

theorem mem_ALint_of_supported (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : AL L)
    (hoff : ∀ w, w ≠ v → compAt L w x = 0)
    (hv : compAt L v x ∈ tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)) :
    x ∈ ALint L := by
  obtain ⟨Y, hY, hYv⟩ := exists_lift L v _ hv
  have h : x - Y * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, compAt_tmul]
    rcases eq_or_ne w v with rfl | hw
    · rw [sgl_same, hYv, ← Algebra.TensorProduct.one_def, mul_one, sub_self]
    · rw [sgl_ne L v 1 hw, hoff w hw, tmul_zero, mul_zero, sub_self]
  rw [sub_eq_zero.1 h]
  exact Subring.mul_mem _ hY (one_tmul_sgl_mem L v 1 (one_mem _))

theorem entries_mem_of_range {K : Type} [Field K] (S : Subring K) {n : ℕ} (P : GL (Fin n) K)
    (hP : P ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range) (i j : Fin n) :
    (P : Matrix (Fin n) (Fin n) K) i j ∈ S := by
  obtain ⟨Q, rfl⟩ := hP
  exact ((Q : Matrix (Fin n) (Fin n) S) i j).2

theorem mem_Umax_of_trivOutside_of_loc_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (z : GAf L n), TrivOutside {v} z → (∀ i j, ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L)) → z ∈ Umax L n := by
  intro L _ _ _ n v w Dv z hz hint i j
  have hP := entries_mem_of_range _ _ Dv.Pint
  have hP' := entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hg : Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) =
      Dv.P * Dv.loc z * Dv.P⁻¹ := by
    unfold InertDatum.loc
    group
  have he : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) ∈
      intL (w.adicCompletion L) := by
    have h1 : Dv.e (compAt L v ((z.1 : Matrix (Fin n) (Fin n) (AL L)) i j)) =
        ((Dv.P * Dv.loc z * Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j := by
      rw [← hg]; rfl
    rw [h1]
    simp only [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
      (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP i l) (hint l k)) (hP' k j)
  have hv := (Dv.integ _).2 he
  have hone : ∀ {R : Type} [CommRing R] (S : Subring R), (1 : Matrix (Fin n) (Fin n) R) i j ∈ S := by
    intro R _ S
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hc : ∀ u, compAt L u ((1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro u
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hd : (z.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈
      ALint L := by
    apply mem_ALint_of_supported L v
    · intro u hu
      have h := congrFun (congrFun (hz u hu) i) j
      rw [map_sub, hc, ← h, Matrix.map_apply, sub_self]
    · rw [map_sub, hc]
      exact Subring.sub_mem _ hv (hone _)
  have := Subring.add_mem _ hd (hone (ALint L))
  rwa [sub_add_cancel] at this

end GlobalTheory.InertUmax
