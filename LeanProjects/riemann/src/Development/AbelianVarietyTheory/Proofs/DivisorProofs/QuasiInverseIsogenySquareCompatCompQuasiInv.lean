import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.QCompat

theorem comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ B₁ _ _ _ _ φ θ ψ₁ ψ₁' hB hk hq hq₁ hφ hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow T B₁ hB k hk
  haveI : Epi ((𝟙 B₁) ^ k).left := Flat.epi_of_flat_of_surjective _
  have e₁ : ψ₁'.left ≫ ψ₁.left = ((𝟙 B₁) ^ k).left := by rw [← Over.comp_left, hq₁.2.2.2]
  haveI : Epi (ψ₁'.left ≫ ψ₁.left) := by rw [e₁]; infer_instance
  haveI : Epi ψ₁.left := epi_of_epi ψ₁'.left ψ₁.left
  rw [← cancel_epi ψ₁.left, ← Category.assoc, ← hsq, Category.assoc, ← Over.comp_left, hq.2.2.1,
    ← Category.assoc, ← Over.comp_left, hq₁.2.2.1]
  exact (GlobalTheory.LamF.IsGrpPullback.id_pow_left hφ k).symm

end GlobalTheory.UPel.HT.ES.QCompat
