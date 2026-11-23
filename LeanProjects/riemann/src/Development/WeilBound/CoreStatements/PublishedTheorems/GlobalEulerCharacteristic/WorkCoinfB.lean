import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.WorkKilledC
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroCoind

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.W_coinf_b

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem uliftInt_smul {A : Type} [AddCommGroup A] (inst : Module (ULift.{0} ℤ) A) (c : ULift.{0} ℤ) (a : A) :
    inst.smul c a = c.down • a := by
  obtain ⟨n⟩ := c
  have h := Int.cast_smul_eq_zsmul (R := ULift.{0} ℤ) (M := A) n a
  have hn : ((n : ℤ) : ULift.{0} ℤ) = ⟨n⟩ := by ext; simp
  rw [hn] at h
  exact h

section Equiv

variable {G Γ : Type} [Group G] [Group Γ] (π : G →* Γ) (hπ : Function.Surjective π) (D : Subgroup Γ)
  (W : Subgroup G) (hW : W = D.comap π)

noncomputable def cosetEquiv : G ⧸ W ≃ Γ ⧸ D :=
  (Subgroup.quotientEquivOfEq hW).trans (quotientComapEquiv D hπ)

theorem cosetEquiv_mk (g : G) :
    cosetEquiv π hπ D W hW (QuotientGroup.mk g) = QuotientGroup.mk (π g) := rfl

theorem cosetEquiv_smul (g : G) (x : G ⧸ W) :
    cosetEquiv π hπ D W hW (g • x) = π g • cosetEquiv π hπ D W hW x := by
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [MulAction.Quotient.smul_mk, cosetEquiv_mk, cosetEquiv_mk, MulAction.Quotient.smul_mk,
      smul_eq_mul, smul_eq_mul, map_mul]

theorem cosetEquiv_symm_smul (g : G) (y : Γ ⧸ D) :
    (cosetEquiv π hπ D W hW).symm (π g • y) = g • (cosetEquiv π hπ D W hW).symm y := by
  apply (cosetEquiv π hπ D W hW).injective
  rw [cosetEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Equiv

set_option maxHeartbeats 1000000 in

theorem coind_eq_infl_funRep (ℓ : ℕ) [Fact ℓ.Prime] (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (L : FiniteSubfield) [Fact (K ≤ L)]
    (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    [hN : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal]
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module (ZMod ℓ) M]
    (ρ : Representation (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M)
    (hρ : ∀ (g : galUnramifiedOutside K.1 ℚ̄ S) (m : M), ρ (QuotientGroup.mk g) m = M.ρ g m)
    (D : Subgroup (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))))
    (L' : FiniteSubfield) [Fact (K ≤ L')]
    (hL' : ∀ x : L'.1, algebraMap L'.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hW : (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) = D.comap (QuotientGroup.mk' _)) :
    gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (Rep.res (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype M)) ιr =
      (haveI := W_killed_c.isDiscreteRep_infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ); gsEulerRatio S (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)) ιr) := by
  have hπ : Function.Surjective (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) :=
    QuotientGroup.mk'_surjective _
  let E := cosetEquiv _ hπ D _ hW
  letI i1 : Module (ULift.{0} ℤ) ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) → M) :=
    (funDiagRep (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M).hV2
  letI i2 : Module (ULift.{0} ℤ) (((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) → M) :=
    (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)).hV2
  let eqv : (funDiagRep (galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) M).ρ.Equiv
      (W_killed_c.infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)).ρ :=
    { toLinearEquiv :=
        { toFun := fun F y => F (E.symm y)
          invFun := fun F x => F (E x)
          map_add' := fun F F' => rfl
          map_smul' := fun c F => by
            funext y
            exact uliftInt_smul _ c (F (E.symm y))
          left_inv := fun F => by funext x; simp
          right_inv := fun F => by funext y; simp }
      isIntertwining' := fun g => by
        refine LinearMap.ext fun F => funext fun y => ?_
        change M.ρ g (F (g⁻¹ • E.symm y)) = ρ (QuotientGroup.mk g) (F (E.symm ((QuotientGroup.mk g : galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))⁻¹ • y)))
        rw [hρ]
        congr 2
        have := cosetEquiv_symm_smul _ hπ D _ hW g⁻¹ y
        exact this.symm }
  haveI := W_killed_c.isDiscreteRep_infl (gsOpenSubgroup S hL) (funRep ((galUnramifiedOutside K.1 ℚ̄ S ⧸ (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) ⧸ D) ρ)
  exact gsEulerRatio_eq_of_iso S _ ιr (coindResIsoFunDiagRep (gsOpenSubgroup S hL' : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) M ≪≫ Rep.mkIso eqv)

end PositivityTheory.Lit1.GEN.W_coinf_b
