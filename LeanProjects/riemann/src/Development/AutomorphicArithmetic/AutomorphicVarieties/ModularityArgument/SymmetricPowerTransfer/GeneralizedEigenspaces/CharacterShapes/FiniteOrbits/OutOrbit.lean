import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section SlopeTestRemainingChoices

variable {G : Type} [Group G]

private theorem dc_left (U : Subgroup G) (a : G) {u : G} (hu : u ∈ U) (y : G) :
    u * y ∈ DC U a ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨v, hv, w, hw, h⟩
    refine ⟨u⁻¹ * v, U.mul_mem (U.inv_mem hu) hv, w, hw, ?_⟩
    rw [mul_assoc u⁻¹ v a, mul_assoc u⁻¹, ← h]
    group
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨u * v, U.mul_mem hu hv, w, hw, by group⟩

private theorem dc_right (U : Subgroup G) (a : G) {u : G} (hu : u ∈ U) (y : G) :
    y * u ∈ DC U a ↔ y ∈ DC U a := by
  constructor
  · rintro ⟨b, hb, c, hc, h⟩
    exact ⟨b, hb, c * u⁻¹, U.mul_mem hc (U.inv_mem hu), by
      rw [← mul_assoc, ← h]; group⟩
  · rintro ⟨b, hb, c, hc, rfl⟩
    exact ⟨b, hb, c * u, U.mul_mem hc hu, by group⟩

private theorem out_orbit (U : Subgroup G) (a : G) (x : G ⧸ U) (h : x.out ∈ DC U a) :
    x ∈ MulAction.orbit U (a : G ⧸ U) := by
  obtain ⟨v, hv, w, hw, h⟩ := h
  refine ⟨⟨v, hv⟩, ?_⟩
  rw [← QuotientGroup.out_eq' x, h]
  show (v : G) • ((a : G ⧸ U)) = QuotientGroup.mk (v * a * w)
  rw [QuotientGroup.mk_mul_of_mem _ hw]
  rfl

private theorem one_neg {p : Prop} (h : ¬p) : one p = 0 := by
  classical
  simp [one, h]

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.opDc :
    UpperTheory.V.Z.Sym.So.OpDc := by
  intro Γ G V _ _ _ _ B hω g hfin
  have hω1 : ∀ u : B.U, (B.ω u : ℂ) = 1 := by
    intro u
    rw [hω]
    rfl
  have htest : (Base.Tw.one B).IsTest fun y ↦ one (y ∈ DC B.U g) := by
    refine ⟨?_, ?_, ?_⟩
    · intro u y
      simp only [hω, MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
      show one (↑u * y ∈ DC B.U g) = one (y ∈ DC B.U g)
      rw [dc_left B.U g u.2 y]
    · intro u y
      simp only [hω, MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
      show one (y * ↑u ∈ DC B.U g) = one (y ∈ DC B.U g)
      rw [dc_right B.U g u.2 y]
    · refine Set.Finite.subset hfin ?_
      intro x hx
      apply out_orbit B.U g x
      by_contra h
      exact hx (one_neg h)
  refine ⟨htest, ?_⟩
  intro φ
  rw [Tf.rSpec Γ G V B _ _ htest φ]
  funext y
  have hinv : ∀ u ∈ B.U, ∀ z : G, (φ : G → V) (z * u) = (φ : G → V) z := by
    intro u hu z
    rw [φ.2.2 z ⟨u, hu⟩, hω1, one_smul]
  rw [(dcBasic G V B.U g hfin φ hinv).2.1 y]
  show ∑ᶠ x : G ⧸ B.U, one (x.out ∈ DC B.U g) • (φ : G → V) (y * x.out) = _
  refine finsum_congr ?_
  intro x
  by_cases h : x.out ∈ DC B.U g
  · simp [one, h]
  · simp [one, h]

end
