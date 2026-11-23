import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem coord_lTensor {K V B B' ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup B]
    [Module K B] [AddCommGroup B'] [Module K B'] [DecidableEq ι] (b : Basis ι K V) (f : B →ₗ[K] B')
    (x : V ⊗[K] B) (i : ι) :
    equivFinsuppOfBasisLeft b (LinearMap.lTensor V f x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]

private theorem line_abs {K V B B' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup B]
    [Module K B] [AddCommGroup B'] [Module K B'] (φ : B →ₗ[K] B) (j : B →ₗ[K] B') (F : Submodule K B')
    (e : B) (he : e ≠ 0) (fund : ∀ y : B, φ y = y → j y ∈ F → ∃ c : K, c • e = y) (x : V ⊗[K] B)
    (h1 : LinearMap.lTensor V φ x = x)
    (h2 : ∃ z, LinearMap.lTensor V F.subtype z = LinearMap.lTensor V j x) :
    ∃! v : V, x = v ⊗ₜ[K] e := by
  classical
  let b := Basis.ofVectorSpace K V
  obtain ⟨z, hz⟩ := h2
  have hc : ∀ i, ∃ c : K, c • e = equivFinsuppOfBasisLeft b x i := fun i =>
    fund _ (by rw [← coord_lTensor, h1]) (by
      rw [← coord_lTensor, ← hz, coord_lTensor]; exact Submodule.coe_mem _)
  choose c hc using hc
  let c' := Finsupp.onFinset (equivFinsuppOfBasisLeft b x).support c (fun i hi => by
    rw [Finsupp.mem_support_iff, ← hc]; exact smul_ne_zero hi he)
  refine ⟨b.repr.symm c', ?_, ?_⟩
  · apply (equivFinsuppOfBasisLeft b).injective
    ext i
    rw [equivFinsuppOfBasisLeft_apply_tmul_apply, LinearEquiv.apply_symm_apply, ← hc]
    rfl
  · intro v hv
    rw [LinearEquiv.eq_symm_apply]
    ext i
    have h := hc i
    rw [hv, equivFinsuppOfBasisLeft_apply_tmul_apply] at h
    exact (smul_left_injective K he h).symm

theorem UpperTheory.V.Loc.lineInv :
    ∀ {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (x : V ⊗[ℚ_[l]] Bcr l), LinearMap.lTensor V (PP l).φB.toLinearMap x = x → LinearMap.lTensor V (PP l).ιB.toLinearMap x ∈ FilT A V 0 → ∃! v : V, x = v ⊗ₜ[ℚ_[l]] (1 : Bcr l) := by
  intro l _ A _ _ V _ _ _ _ x h1 h2
  refine line_abs (PP l).φB.toLinearMap (PP l).ιB.toLinearMap
    ((((PP l).PD (botExt l)).Fil 0).restrictScalars ℚ_[l]) 1 ?_ ?_ x h1 ?_
  · intro h
    apply ((PP l).PD (botExt l)).not_mem_filtration_two
    rw [← mul_one ((PP l).PD (botExt l)).t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  · intro y hy hF
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund y (by rw [(PP l).PD_φ]; exact hy)
      (by rw [(PP l).PD_ι]; exact hF)
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  · obtain ⟨z, hz⟩ := h2
    exact ⟨z, hz⟩
