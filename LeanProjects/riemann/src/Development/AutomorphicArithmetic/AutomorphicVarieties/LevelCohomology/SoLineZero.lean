import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobIndex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.lineZero :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (G Γ ι : Type) [Group G] [Group Γ] [TopologicalSpace G] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G Γ ι) [Finite (ResidueField O)], F.Cl1 → ∀ s : ℕ, LineVan F 0 (lineChar F 0 s) := by
  intro O _ _ _ _ G Γ ι _ _ _ _ F _ hCl s z hz hcont hN hI _
  have hθ : ∀ u ∈ F.η.ker, lineChar F 0 s u = 1 := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    simp [lineChar, etaO, hu]
  have hz1 : z 1 = 0 := by
    have e := hz 1 1
    simp at e
    exact e
  have hadd : ∀ u w, u ∈ F.η.ker → z (u * w) = z u + z w := by
    intro u w hu
    simp [hz u w, hθ u hu]
  have hpow : ∀ u ∈ F.η.ker, ∀ n : ℕ, z (u ^ n) = n * z u := by
    intro u hu n
    induction n with
    | zero => simp [hz1]
    | succ n ih =>
      rw [pow_succ, hadd _ _ (F.η.ker.pow_mem hu n), ih]
      push_cast
      ring
  have hvan : ∀ v (t : F.D v), t ∈ F.Iv v → F.η (F.loc v t) = 1 → z (F.loc v t) = 0 := by
    intro v t ht hηt
    by_cases hv : v ∈ F.Tb
    · exact hI rfl v hv t ht
    · have hmem : t ^ Nat.card (ResidueField O)ˣ ∈ F.Nv v := by
        simp only [UnitaryThreeInertia.Frame.Nv, UnitaryThreeInertia.kerBar, Subgroup.mem_inf, MonoidHom.mem_ker, map_pow]
        refine ⟨⟨Subgroup.pow_mem _ ht _, ?_⟩, pow_card_eq_one'⟩
        simp only [UnitaryThreeInertia.Frame.ηv, MonoidHom.comp_apply]
        rw [hηt, one_pow]
      have h0 := hN v hv _ hmem
      rw [map_pow, hpow _ (MonoidHom.mem_ker.mpr hηt)] at h0
      have hn : ((Nat.card (ResidueField O)ˣ : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      exact (mul_eq_zero.mp h0).resolve_left hn
  have hall : ∀ N : ℕ, ∀ u ∈ F.η.ker, z u ∈ (maximalIdeal O) ^ N := by
    intro N
    let χ : F.η.ker →* Multiplicative (O ⧸ (maximalIdeal O) ^ N) :=
      { toFun := fun u => Multiplicative.ofAdd (Ideal.Quotient.mk _ (z u))
        map_one' := by simp [hz1]
        map_mul' := by
          intro u w
          simp [hadd u.1 w.1 u.2, ofAdd_add] }
    have hlc : IsLocallyConstant χ := by
      exact ((hcont N).comp_continuous (continuous_subtype_val (p := fun x => x ∈ F.η.ker))).comp
        Multiplicative.ofAdd
    have hχ : χ = 1 := by
      refine hCl _ χ hlc ?_
      intro v t g h ht
      have hηt : F.η (F.loc v t) = 1 := by
        have h' := MonoidHom.mem_ker.mp h
        rw [map_mul, map_mul, map_inv, mul_comm (F.η g), mul_assoc, mul_inv_cancel, mul_one] at h'
        exact h'
      have hz0 := hvan v t ht hηt
      have e1 := hz (g * F.loc v t) g⁻¹
      have e2 := hz g (F.loc v t)
      have e3 := hz g g⁻¹
      rw [mul_inv_cancel, hz1] at e3
      rw [map_mul, hθ _ (MonoidHom.mem_ker.mpr hηt), mul_one] at e1
      have hc : z (g * F.loc v t * g⁻¹) = 0 := by
        linear_combination e1 + e2 - e3 + ((lineChar F 0 s g : Oˣ) : O) * hz0
      show Multiplicative.ofAdd (Ideal.Quotient.mk _ (z (g * F.loc v t * g⁻¹))) = 1
      rw [hc]
      simp
    intro u hu
    have e := congrArg (fun f => f ⟨u, hu⟩) hχ
    simp only [MonoidHom.one_apply] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp (Multiplicative.ofAdd.injective e)
  have hker : ∀ u ∈ F.η.ker, z u = 0 := by
    intro u hu
    have hm : z u ∈ ⨅ N : ℕ, (maximalIdeal O) ^ N := Submodule.mem_iInf _ |>.mpr fun N => hall N u hu
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hm
    simpa using hm
  have hU : CobOn (lineChar F 0 s) z (F.η.ker ⊓ ⊤) :=
    cobOn_of_eq_zero _ (fun g hg => hker g hg.1)
  have hrel : F.η.ker.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_ker]
    exact Nat.card_pos.ne'
  exact So.cobIndex O Γ (lineChar F 0 s) z hz F.η.ker ⊤ hrel hU
