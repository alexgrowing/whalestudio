import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonUnramifiedExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueLiftIrreducibleStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.TraitLift

theorem exists_ringHom_lift_of_isEtaleCompletion : ∀ {A R W : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W] (φ : A →+* R) (ψ : A →+* W), IsCN R → IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → CDvr W → IsLocalHom ψ → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (ι : W →+* W') (g : R →+* W'), CDvr W' ∧ (∀ ϖ : W, Irreducible ϖ → Irreducible (ι ϖ)) ∧ g.comp φ = ι.comp ψ := by
  intro A R W _ _ _ _ _ _ _ _ φ α hR hφ hur hW hα
  obtain ⟨-, -, hRc, -⟩ := hR
  haveI := hRc
  obtain ⟨hflat, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : φ a ∈ maximalIdeal R := hmax ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← ResidueField.map_comp_residue] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_unramified φ hfin hur
  obtain ⟨M, _, u, v, huv, hvf, hvu⟩ := GlobalTheory.T.exists_common_unramified_extension (ResidueField.map φ) (ResidueField.map α) hfin' hur'
  obtain ⟨V, _, _, _, f, τ, hV, -, hfloc, hirr, hτ⟩ := GlobalTheory.T.exists_dvr_residue_lift_irreducible W hW v hvf hvu
  haveI := hV.2.1
  let σ : ResidueField R →+* ResidueField V := τ.comp u
  have hσ : ∀ a, σ (residue R (φ a)) = residue V ((f.comp α) a) := by
    intro a
    have h1 := congrArg (fun g => g (residue _ a)) huv
    simp only [RingHom.comp_apply, ResidueField.map_residue] at h1
    simp only [σ, RingHom.comp_apply, h1, hτ]
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ hσ θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨g, hg, -⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  exact ⟨V, inferInstance, inferInstance, inferInstance, f, g, hV, hirr, hg⟩

end GlobalTheory.TraitLift
