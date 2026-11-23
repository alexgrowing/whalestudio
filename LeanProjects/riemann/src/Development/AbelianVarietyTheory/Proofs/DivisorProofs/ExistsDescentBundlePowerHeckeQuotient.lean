import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarisatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingLinearMapStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∃ P₀ : LB (G2 A').left, P₀.IsLB ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o A' _ _ ψ hA' hψ hGal
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ (k ^ 2 / c)
    (GlobalTheory.UPel.HT.Hecke.heckeSub o g N)
    (fun h hh => (GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh).1)
    (fun h hh => (GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh).2)
    (GlobalTheory.T.heckeSections_isotropic_commutatorPairing_linearMap p D R b g c k N hc hk hN hNp hEF hg hck S s o)
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ψ hψ hGal
  obtain ⟨M, hM, hiso⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (GlobalTheory.UPel.HT.Hecke.sq2 ψ) _ _
    (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) hGC (DVR.linComb_isLB _ o.isLB _ _) u hu hcoc
  exact ⟨M, hM, hiso⟩
