import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem coe_mem_orbit (U : Subgroup G) (a g : G) :
    (g : G ⧸ U) ∈ MulAction.orbit U (a : G ⧸ U) ↔ g ∈ DC U a := by
  constructor
  · rintro ⟨u, hu⟩
    have h : ((u.1 * a : G) : G ⧸ U) = g := by rw [← hu]; rfl
    rw [QuotientGroup.eq] at h
    exact ⟨u.1, u.2, (u.1 * a)⁻¹ * g, h, by group⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    show ((u * a : G) : G ⧸ U) = ((u * a * u' : G) : G ⧸ U)
    rw [QuotientGroup.eq, show (u * a)⁻¹ * (u * a * u') = u' by group]
    exact hu'

private theorem out_mem_orbit (U : Subgroup G) (a : G) (y : G ⧸ U) :
    y ∈ MulAction.orbit U (a : G ⧸ U) ↔ y.out ∈ DC U a := by
  rw [← coe_mem_orbit, QuotientGroup.out_eq']

private theorem val_out (U : Subgroup G) {φ : G → V} (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g)
    (g y : G) (q : G ⧸ U) (h : (y : G ⧸ U) = q) : φ (g * q.out) = φ (g * y) := by
  have hm : y⁻¹ * q.out ∈ U := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact h
  have e := hφ _ hm (g * y)
  rw [show g * y * (y⁻¹ * q.out) = g * q.out by group] at e
  exact e

private theorem dcF_eq_mem (U : Subgroup G) (a : G) (φ : G → V) :
    dcF U a φ = (∑ᶠ q ∈ MulAction.orbit U (a : G ⧸ U), rightReg ℂ G V q.out) φ := by
  show (∑ᶠ q : ↑(MulAction.orbit U (a : G ⧸ U)), rightReg ℂ G V (Quotient.out (q : G ⧸ U))) φ = _
  rw [finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ U => rightReg ℂ G V q.out)]

private theorem dcF_apply (U : Subgroup G) (a : G) (h : (MulAction.orbit U (a : G ⧸ U)).Finite)
    (φ : G → V) (g : G) :
    dcF U a φ g = ∑ y ∈ Set.Finite.toFinset h, φ (g * y.out) := by
  rw [dcF_eq_mem, finsum_mem_eq_finite_toFinset_sum _ h]
  simp [LinearMap.sum_apply, Finset.sum_apply, rightReg, LinearMap.funLeft]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.dcBasic :
    UpperTheory.V.Z.Sym.So.DcBasic := by
  intro G V _ _ _ U a hfin0 φ hφ
  classical
  have hfin : (MulAction.orbit U (a : G ⧸ U)).Finite := hfin0
  have hO : ∀ (v : U) (y : G ⧸ U), y ∈ MulAction.orbit U (a : G ⧸ U) →
      v • y ∈ MulAction.orbit U (a : G ⧸ U) := by
    rintro v y ⟨w, rfl⟩
    exact ⟨v * w, mul_smul v w _⟩
  have h5 : ∀ (R : Finset G), (∀ y ∈ R, y ∈ DC U a) →
      (∀ y ∈ DC U a, ∃! r, r ∈ R ∧ r⁻¹ * y ∈ U) → ∀ g, dcF U a φ g = ∑ r ∈ R, φ (g * r) := by
    intro R hR hu g
    rw [dcF_apply U a hfin φ g]
    symm
    refine Finset.sum_bij (fun r _ => (r : G ⧸ U)) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Set.Finite.mem_toFinset]
      exact (coe_mem_orbit U a r).mpr (hR r hr)
    · intro r1 hr1 r2 hr2 he
      have h12 : r1⁻¹ * r2 ∈ U := QuotientGroup.eq.mp he
      have h22 : r2⁻¹ * r2 ∈ U := by rw [inv_mul_cancel]; exact U.one_mem
      exact (hu r2 (hR r2 hr2)).unique ⟨hr1, h12⟩ ⟨hr2, h22⟩
    · intro y hy
      rw [Set.Finite.mem_toFinset] at hy
      obtain ⟨r, ⟨hr, hry⟩, -⟩ := hu _ ((out_mem_orbit U a y).mp hy)
      refine ⟨r, hr, ?_⟩
      show (r : G ⧸ U) = y
      rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
      exact hry
    · intro r hr
      exact (val_out U hφ g r (r : G ⧸ U) rfl).symm
  refine ⟨?_, ?_, ?_, ?_, h5⟩
  · intro u hu g
    rw [dcF_apply U a hfin φ, dcF_apply U a hfin φ]
    let u' : U := ⟨u, hu⟩
    refine Finset.sum_nbij' (fun y => u' • y) (fun y => u'⁻¹ • y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u' y hy
    · intro y hy
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hy ⊢
      exact hO u'⁻¹ y hy
    · intro y _
      exact inv_smul_smul u' y
    · intro y _
      exact smul_inv_smul u' y
    · intro y _
      have hq : ((u * y.out : G) : G ⧸ U) = u' • y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [mul_assoc]
      exact (val_out U hφ g (u * y.out) (u' • y) hq).symm
  · intro g
    rw [dcF_apply U a hfin φ g, ← finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp only [out_mem_orbit]
  · intro b hb
    rw [dcF_eq_mem, dcF_eq_mem, MulAction.orbit_eq_iff.mpr ((coe_mem_orbit U a b).mpr hb)]
  · intro ha
    funext g
    rw [h5 {1} ?_ ?_ g, Finset.sum_singleton, mul_one]
    · intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      exact ⟨a⁻¹, U.inv_mem ha, 1, U.one_mem, by group⟩
    · rintro y ⟨v, hv, v', hv', rfl⟩
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
      · rw [inv_one, one_mul]
        exact U.mul_mem (U.mul_mem hv ha) hv'
      · rintro r ⟨hr, -⟩
        exact Finset.mem_singleton.mp hr

end
