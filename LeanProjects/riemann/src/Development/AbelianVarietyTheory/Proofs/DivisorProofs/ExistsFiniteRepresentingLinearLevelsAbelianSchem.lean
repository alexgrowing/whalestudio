import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAgreementLocusSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearOfBasisProductsAdditivePointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OLinearLevelPullbackUniversalFactorisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_finite_rep_linLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH], IsAbelianScheme AH → IsUnit ((N : ℕ) : Γ(H, ⊤)) → ∀ (actH : OActN D.O AH), ∃ (E : Scheme.{0}) (πE : E ⟶ H) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsFinite πE ∧ IsGrpPullback AE AH πE φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ H) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ AH.left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT AH g φ → (∀ a : D.O, (act.act a).left ≫ φ = φ ≫ (actH.act a).left) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D N H AH _ _ hab hN actH
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  haveI : IsSeparated AH.hom := by haveI := hab.proper; infer_instance
  obtain ⟨Z, et, hZf, -, eadd, epow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom H AH N D.La hab hN
  let bO := Module.Free.chooseBasis ℤ D.O
  let bL := Module.Free.chooseBasis ℤ D.La
  obtain ⟨Y, i, hYf, hieq, hiu⟩ := GlobalTheory.T.exists_finite_agreementLocus_separated H Z AH hZf inferInstance
    (Module.Free.ChooseBasisIndex ℤ D.O × Module.Free.ChooseBasisIndex ℤ D.La)
    (fun k => et (bO k.1 • bL k.2)) (fun k => et (bL k.2) ≫ actH.act (bO k.1))
  let u : D.La → (Y ⟶ AH) := fun x => i ≫ et x
  have uadd : ∀ x y, u (x + y) = u x * u y := fun x y => by
    simp only [u, eadd, MonObj.comp_mul]
  have ulin : ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c :=
    GlobalTheory.T.oLinear_of_basis_products_additive_points p D H Y AH actH u uadd _ _ bO bL fun j k => by
      have := hieq (j, k)
      simp only [u]
      rw [this, Category.assoc]
  have ukill : ∀ x, u (N • x) = 1 := fun x => by
    simp only [u]
    rw [GlobalTheory.LevCover.add_map_nsmul eadd, epow, MonObj.comp_one]
  have uuniv : ∀ (T : Over H) (u' : D.La → (T ⟶ AH)), (∀ x y, u' (x + y) = u' x * u' y) →
      (∀ (c : D.O) x, u' (c • x) = u' x ≫ actH.act c) → (∀ x, u' (N • x) = 1) →
      ∃! h : T ⟶ Y, ∀ x, h ≫ u x = u' x := by
    intro T u' hadd hlin hkill
    have hpow : ∀ x, u' x ^ N = 1 := fun x => by rw [← GlobalTheory.LevCover.add_map_nsmul hadd, hkill]
    obtain ⟨h₀, hh₀, hu₀⟩ := huniv T u' hadd hpow
    have heq : ∀ k, h₀ ≫ (fun k : _ × _ => et (bO k.1 • bL k.2)) k =
        h₀ ≫ (fun k : _ × _ => et (bL k.2) ≫ actH.act (bO k.1)) k := by
      rintro ⟨j, k⟩
      simp only
      rw [hh₀, hlin, ← Category.assoc, hh₀]
    obtain ⟨h, hh, hu⟩ := hiu T h₀ heq
    refine ⟨h, fun x => by simp only [u]; rw [← Category.assoc, hh, hh₀], fun h' hh' => hu h' ?_⟩
    exact hu₀ _ fun x => by rw [Category.assoc]; exact hh' x
  obtain ⟨AE, _, _, φE, actE, ηE, hE, hact, heta, hηu⟩ := GlobalTheory.T.exists_pullback_group_oLinear_torsion_level p D N H AH actH Y u uadd ulin ukill
  exact ⟨Y.left, Y.hom, AE, inferInstance, inferInstance, φE, actE, ηE, hYf, hE, hact, heta,
    fun T g AT _ φ act eta hT hTact hTeta =>
      GlobalTheory.T.oLinearLevel_pullback_universal_factorisation p D N H AH actH Y u AE φE ηE hE hηu uuniv T g AT φ act eta hT hTact hTeta⟩

end GlobalTheory.UPel.HT
