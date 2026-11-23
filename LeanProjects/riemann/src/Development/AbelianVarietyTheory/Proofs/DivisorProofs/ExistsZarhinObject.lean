import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductRelationAlgebraicClausesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleIsomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem exists_zarhin_object : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  intro h M d h1 hM hodd hd hcop
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_zarhinSymplecticTransfer h M d h1 hM hodd hd hcop
  refine ⟨GlobalTheory.ZarhinFam.jlMap h, 8, GlobalTheory.ZarhinFam.oMat d, κ, fun S t c hdu hk => ?_⟩
  obtain ⟨B, _, _, Q, la, mu, hZ⟩ := GlobalTheory.T.exists_zarhin_data h M d S t c h1 hM hodd hd hcop hdu hk
  obtain ⟨r1, r2, sy⟩ := GlobalTheory.T.zarhinBundle_rigidified_symmetric h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk
  obtain ⟨la1, la2⟩ := GlobalTheory.T.zarhinLevel_additive_killed_by_level h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  have hab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
  let z : SiegPre (8 * h) M (zetaAway M) t :=
    { A := GlobalTheory.ZarhinFam.Zob c.A B
      ab := hab
      P := GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu
      isLB := GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
      rig₁ := r1
      rig₂ := r2
      symm := sy
      lev := GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ
      lev_add := la1
      lev_tors := la2
      geom := GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ }
  obtain ⟨i1, i2, i3, i4, i5⟩ := GlobalTheory.T.zarhinProduct_relation_algebraic_clauses h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  refine ⟨z, GlobalTheory.ZarhinFam.actZ c.A B d la mu, GlobalTheory.T.zarhinBundle_principal h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.T.zarhinOrder_isRingAction_on_product h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, GlobalTheory.T.zarhinOrderAction_rosati_adjoint h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.ZarhinFam.incZ c.A B, GlobalTheory.ZarhinFam.prZ c.A B, i1, i2, i3, i4,
    GlobalTheory.T.zarhin_bundle_isomorphism h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, i5, fun a => rfl⟩

end GlobalTheory.ZarhinFam
