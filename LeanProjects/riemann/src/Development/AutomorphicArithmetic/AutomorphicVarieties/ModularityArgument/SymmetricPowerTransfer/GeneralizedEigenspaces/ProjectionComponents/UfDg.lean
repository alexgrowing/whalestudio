import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.NoKappa
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.BadClosed

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym

namespace UpperTheory.V.Z.Sym.U

private def dg {Γ k : Type} [Group Γ] [Field k] (χ : Γ →* kˣ) : Γ →* GL (Fin 2) k where
  toFun g := Matrix.GeneralLinearGroup.mkOfDetNeZero !![(χ g : k), 0; 0, 1] (by simp)
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  map_mul' g h := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

private theorem uf_dg {Γ k : Type} [Group Γ] [Field k] (χ : Γ →* kˣ) (g : Γ) : Ga.uf (dg χ g) = (χ g : k) + (χ g : k)⁻¹ := by
  have h0 : (χ g : k) ≠ 0 := (χ g).ne_zero
  simp only [Ga.uf, Ga.tr, dg, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.trace_fin_two, Matrix.det_fin_two]
  simp
  field_simp
  ring

theorem xiOne (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime]
    (r : G L Ω →* GL (Fin 2) (Qbar l)) (hc : Continuous r) (h4 : IrrOpen (Ga.sym4 r)) (ξ : G L Ω →* (Qbar l)ˣ)
    (hξ : IsOpen (ξ.ker : Set (G L Ω))) (h : ∀ g ∉ Ga.Bad r, (ξ g : Qbar l) * (Ga.uf (r g) + 1) = Ga.uf (r g) + 1) : ξ = 1 := by
  by_contra hne
  obtain ⟨g0, hg0⟩ : ∃ g0, ξ g0 ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hne (MonoidHom.ext hall)
  obtain ⟨huf, hep, hbad⟩ := Ga.badClosed L Ω l r hc
  set U : Set (G L Ω) := (fun g => g0⁻¹ * g) ⁻¹' (ξ.ker : Set (G L Ω)) with hU
  have hUo : IsOpen U := hξ.preimage (continuous_const.mul continuous_id)
  have hg0U : g0 ∈ U := by
    show g0⁻¹ * g0 ∈ ξ.ker
    rw [inv_mul_cancel]
    exact ξ.ker.one_mem
  have hUξ : ∀ g ∈ U, ξ g = ξ g0 := by
    intro g hg
    have h1 : ξ (g0⁻¹ * g) = 1 := MonoidHom.mem_ker.mp hg
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1.symm
  by_cases hcase : (U ∩ (Ga.Bad r)ᶜ).Nonempty
  · apply Ga.noKappa l (G L Ω) r r h4 (U ∩ (Ga.Bad r)ᶜ) (hUo.inter hbad.isOpen_compl) hcase
    intro g hg
    have h1 := h g hg.2
    rw [hUξ g hg.1] at h1
    have h2 : Ga.uf (r g) + 1 = 0 := by
      have h3 : ((ξ g0 : Qbar l) - 1) * (Ga.uf (r g) + 1) = 0 := by
        rw [sub_mul, h1]
        ring
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd (Units.val_eq_one.mp (sub_eq_zero.mp h4)) hg0
      · exact h4
    have h5 : Ga.uf (r g) = -1 := by linear_combination h2
    rw [h5]
    norm_num
  · have hsub : U ⊆ Ga.Bad r := by
      intro g hg
      by_contra hgb
      exact hcase ⟨g, hg, hgb⟩
    set B : ℤ → Set (G L Ω) := fun m =>
      {g | Ga.uf (r g) ^ 2 - 2 = Ga.ep l (g ^ m) + Ga.ep l (g ^ (-m))} with hB
    have hBc : ∀ m, IsClosed (B m) := fun m =>
      isClosed_eq ((huf.pow 2).sub continuous_const)
        ((hep.comp (continuous_zpow m)).add (hep.comp (continuous_zpow (-m))))
    have hepz : ∀ g : G L Ω, ∀ m : ℤ, Ga.ep l (g ^ m) = Ga.ep l g ^ m := by
      intro g m
      simp only [Ga.ep, map_zpow, Units.val_zpow_eq_zpow_val]
    have hBad : Ga.Bad r ⊆ ⋃ m ∈ Finset.Icc (-2 : ℤ) 2, B m := by
      intro g hg
      obtain ⟨m, hm, he⟩ := hg
      simp only [Set.mem_iUnion, Finset.mem_Icc]
      refine ⟨m, ⟨(abs_le.mp hm).1, (abs_le.mp hm).2⟩, ?_⟩
      show _ = _
      rw [hepz, hepz]
      exact he
    have claim : ∀ (s : Finset ℤ) (W : Set (G L Ω)), IsOpen W → W.Nonempty → W ⊆ ⋃ m ∈ s, B m →
        ∃ m, ∃ V : Set (G L Ω), IsOpen V ∧ V.Nonempty ∧ V ⊆ B m := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · intro W _ hW hsW
        obtain ⟨w, hw⟩ := hW
        simpa using hsW hw
      · intro a s _ ih W hWo hW hsW
        by_cases hd : (W ∩ (B a)ᶜ).Nonempty
        · refine ih _ (hWo.inter (hBc a).isOpen_compl) hd ?_
          intro g hg
          have h6 := hsW hg.1
          simp only [Finset.set_biUnion_insert, Set.mem_union] at h6
          exact h6.resolve_left hg.2
        · refine ⟨a, W, hWo, hW, fun g hg => ?_⟩
          by_contra hga
          exact hd ⟨g, hg, hga⟩
    obtain ⟨m, V, hVo, hVn, hVB⟩ := claim _ U hUo ⟨g0, hg0U⟩ (hsub.trans hBad)
    apply Ga.noKappa l (G L Ω) r (dg ((cycBar L Ω l) ^ m)) h4 V hVo hVn
    intro g hg
    have h7 : Ga.uf (r g) ^ 2 - 2 = Ga.ep l (g ^ m) + Ga.ep l (g ^ (-m)) := hVB hg
    rw [uf_dg, h7, hepz, hepz]
    simp [Ga.ep, zpow_neg]

end UpperTheory.V.Z.Sym.U
