import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.ProdLin

theorem exists_linearisation_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  intro X L hL Ga Gb _ _ ρ₁ ρ₂ ρ hρ hcomm hρ₁ hρ₂ v₁ v₂ hv₁ hv₂ hc₁ hc₂ hc
  have hex : ∀ p : Ga × Gb, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val u r z J = val (LB.mulGen L _ _ _ _ (v₁ p.1) (LB.pullGen L _ _ (v₂ p.2) (ρ₁ p.1))) r z J := by
    intro p
    refine exists_gen hL ?_ _ (DVR.mulGen_isGen_of_isGen _ (hv₁ _) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hv₂ _) _))
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two, hρ p]
  choose u hu hval using hex
  refine ⟨u, hu, fun p q => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  refine corr_of_val hL fun y J hJ => ?_
  have e0 := hval (a * c, b * d) X (𝟙 X) y J hJ
  have e1 := hval (a, b) X (𝟙 X) y J hJ
  have e2 := hval (c, d) X (𝟙 X ≫ ρ (a, b)) y J hJ
  have f1 := val_corr hJ (hc₁ a c) (𝟙 X)
  have f2 := val_corr hJ (hc₂ b d) (ρ₁ (a * c))
  have g := val_corr hJ (hc c b) (ρ₁ a)
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e0
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at g
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁]
  rw [e0, e1, e2, f1, f2, ← hcomm c b, _root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (val (v₁ c) (ρ₁ a) y J), g]
  simp only [_root_.mul_assoc]
end GlobalTheory.ProdLin
