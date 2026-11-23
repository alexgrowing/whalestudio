import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNatAbsEqMinpolyCoeffZeroPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.OActDeg

def endHom {k : Type} [Field k] (X : GlobalTheory.AV.AbVar k) (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) X.X) :
    𝓞 F →+* CategoryTheory.End X where
  toFun c := GlobalTheory.AV.AbVar.Hom.mk (A := X) (B := X) (ρ.act c) (h := ρ.hom c)
  map_one' := by
    apply GlobalTheory.AV.AbVar.hom_ext
    simp [ρ.one]
  map_mul' a b := by
    apply GlobalTheory.AV.AbVar.hom_ext
    change ρ.act (a * b) = ρ.act b ≫ ρ.act a
    rw [mul_comm, ρ.mul]
  map_zero' := by
    apply GlobalTheory.AV.AbVar.hom_ext
    rw [GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.zero_hom]
    have h := ρ.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  map_add' a b := by
    apply GlobalTheory.AV.AbVar.hom_ext
    rw [GlobalTheory.AV.AbVar.add_hom, GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.mk_hom, GlobalTheory.AV.AbVar.mk_hom, ρ.add]

theorem isFinite_and_finrank_eq_norm_pow : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F] (ρ : OAct (𝓞 F) A) (l d : ℕ), l.Prime → (l : k) ≠ 0 →
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ A // x ^ l = 1} = l ^ (d * Module.finrank ℚ F) →
    ∀ c : 𝓞 F, c ≠ 0 → IsFinite (ρ.act c).left ∧
      (ρ.act c).left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) =
        (Algebra.norm ℤ c).natAbs ^ d := by
  intro k _ _ A _ hA F _ _ ρ l d hl hl0 hcard c hc
  let X : GlobalTheory.AV.AbVar k := GlobalTheory.TateHondaBridge.toAbVar A hA
  have h2 := GlobalTheory.abMulN_holds k A X.dim l hA X.smooth hl0
  rw [hcard] at h2
  have hdim : 2 * X.dim = d * Module.finrank ℚ F :=
    (Nat.pow_right_injective hl.two_le h2).symm
  obtain ⟨hiso, hdeg⟩ := GlobalTheory.AV.AbVar.isIsogeny_and_deg_eq_norm_pow k X F (endHom X F ρ) d hdim c hc
  refine ⟨hiso.1, ?_⟩
  classical
  rw [← hdeg]
  unfold GlobalTheory.AV.AbVar.deg
  rw [if_pos hiso]
  rfl

end GlobalTheory.AV.OActDeg

end
