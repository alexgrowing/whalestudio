import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.IsGenEig

namespace UpperTheory.V.Z.Sym.Tf

theorem finD {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (hB : B.Fin) (s : B.Tw)
    (f : G → ℂ) (hf : s.IsTest f) (g g' : G) :
    ∃ D : Finset Γ, ∀ δ, f (g⁻¹ * B.ι δ * s.θ g') ≠ 0 → ∃ d ∈ D, ∃ z ∈ B.Γ₀, δ = d * z := by
  classical
  set L : Subgroup Γ :=
    Subgroup.comap B.ι (Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g')) B.U) with hL
  haveI hfi : (B.Γ₀.subgroupOf L).FiniteIndex := ⟨hB.stab g'⟩
  haveI : Finite (L ⧸ B.Γ₀.subgroupOf L) := Subgroup.finite_quotient_of_finiteIndex
  have hcomm' : ∀ γ, s.θ.symm (B.ι γ) = B.ι (s.θΓ.symm γ) := by
    intro γ
    apply s.θ.injective
    rw [MulEquiv.apply_symm_apply, s.comm, MulEquiv.apply_symm_apply]
  let T : Set Γ := {δ | f (g⁻¹ * B.ι δ * s.θ g') ≠ 0}
  let key : Γ → G ⧸ B.U := fun δ => (QuotientGroup.mk (s.θ.symm (g⁻¹ * B.ι δ * s.θ g')) : G ⧸ B.U)
  have hkey : ∀ δ ∈ T, key δ ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0} := by
    intro δ hδ
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U (s.θ.symm (g⁻¹ * B.ι δ * s.θ g'))
    show f (s.θ (Quotient.out (key δ))) ≠ 0
    have hu' : Quotient.out (key δ) = s.θ.symm (g⁻¹ * B.ι δ * s.θ g') * u := hu
    rw [hu', map_mul, MulEquiv.apply_symm_apply, hf.right]
    exact mul_ne_zero (Units.ne_zero _) hδ
  have himg : ((QuotientGroup.mk : Γ → Γ ⧸ B.Γ₀) '' T).Finite := by
    have hsub : T ⊆ ⋃ c ∈ {x : G ⧸ B.U | f (s.θ (Quotient.out x)) ≠ 0}, {δ | key δ = c} :=
      fun δ hδ => Set.mem_biUnion (hkey δ hδ) rfl
    refine Set.Finite.subset ?_ (Set.image_mono hsub)
    rw [Set.image_iUnion₂]
    refine hf.fin.biUnion fun c _ => ?_
    by_cases hne : ∃ δ₁, key δ₁ = c
    · obtain ⟨δ₁, hδ₁⟩ := hne
      let φ : L ⧸ B.Γ₀.subgroupOf L → Γ ⧸ B.Γ₀ :=
        fun q => ((δ₁ * s.θΓ ((Quotient.out q : L) : Γ) : Γ) : Γ ⧸ B.Γ₀)
      refine (Set.finite_range φ).subset ?_
      rintro _ ⟨δ, hδ, rfl⟩
      have hab := QuotientGroup.eq.mp (hδ₁.trans hδ.symm)
      have hl : s.θΓ.symm (δ₁⁻¹ * δ) ∈ L := by
        rw [hL, Subgroup.mem_comap, Subgroup.mem_map]
        refine ⟨_, hab, ?_⟩
        rw [← hcomm']
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
          MulEquiv.symm_apply_apply, mul_inv_rev, inv_inv]
        group
      obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (B.Γ₀.subgroupOf L)
        (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L)
      refine ⟨(QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) : L ⧸ B.Γ₀.subgroupOf L), ?_⟩
      have hz0 : ((z : L) : Γ) ∈ B.Γ₀ := Subgroup.mem_subgroupOf.mp z.2
      show ((δ₁ * s.θΓ ((Quotient.out _ : L) : Γ) : Γ) : Γ ⧸ B.Γ₀) = _
      rw [show Quotient.out (QuotientGroup.mk (⟨s.θΓ.symm (δ₁⁻¹ * δ), hl⟩ : L) :
          L ⧸ B.Γ₀.subgroupOf L) = _ from hz]
      rw [Subgroup.coe_mul, map_mul, MulEquiv.apply_symm_apply, s.fix _ hz0, ← mul_assoc,
        mul_inv_cancel_left]
      apply QuotientGroup.eq.mpr
      simpa using B.Γ₀.inv_mem hz0
    · refine Set.finite_empty.subset ?_
      rintro _ ⟨δ, hδ, rfl⟩
      exact (hne ⟨δ, hδ⟩).elim
  refine ⟨himg.toFinset.image (fun q => Quotient.out q), fun δ hδ => ?_⟩
  refine ⟨Quotient.out ((δ : Γ ⧸ B.Γ₀)), Finset.mem_image.mpr ⟨_, himg.mem_toFinset.mpr ⟨δ, hδ, rfl⟩, rfl⟩,
    (Quotient.out ((δ : Γ ⧸ B.Γ₀)))⁻¹ * δ, ?_, by group⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' _)

end UpperTheory.V.Z.Sym.Tf
