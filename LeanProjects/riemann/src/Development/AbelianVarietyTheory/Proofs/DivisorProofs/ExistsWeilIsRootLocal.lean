import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilRootLocal

theorem exists_weilIs_root_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → ∀ (PP : RigLB A), CubicalStr A PP → ∀ (R : Type) [CommRing R] [IsLocalRing R]
    (t : Sp R ⟶ S) (n : ℕ) (g h : Over.mk t ⟶ A), g ^ n = 1 → h ^ n = 1 →
    ∃ u : Rˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) := by
  intro S A _ _ hA PP cub R _ _ t n g h hg hh
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have loc : ∀ z : Over.mk t ⟶ A, z ^ n = 1 → ∀ p : (Over.mk t).left, ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp A PP.L (n : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨θ, hθ⟩ := TorsionThetaLocal.exists_theta_of_pow_eq_one S A PP cub R t n z hz
    obtain ⟨θ', hθ'⟩ := CommutatorPairing.exists_pull PP.isLB θ (Out.overResι ⊤)
    exact ⟨⊤, trivial, θ', by rw [hθ', hθ]⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG hA PP.isLB (loc g hg) (loc h hh)
  have pw : ∀ m : ℕ, Out.WeilIs A PP.L (n : ℤ) (g ^ (m + 1)) h (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih =>
      rw [pow_succ g (m + 1), pow_succ c (m + 1)]
      exact DiagPairing.weilIs_mul_left hG hA PP.isLB ih hc
  have e := pw n
  rw [pow_succ g, hg, _root_.one_mul] at e
  have hcn := CommutatorPairing.weilIs_unique hG hA PP.isLB e hc
  rw [pow_succ, mul_eq_right] at hcn
  obtain ⟨u, rfl⟩ : ∃ u : Rˣ, unitOn u = c :=
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).surjective c
  refine ⟨u, unitOn_injective_of_commRing ?_, hc⟩
  show unitOn (u ^ n) = unitOn 1
  rw [unitOn, unitOn, map_pow, map_one]
  exact hcn

end GlobalTheory.WeilRootLocal
