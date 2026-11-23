import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatAtTrivAtOfSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdentityClassLatticeEqSelfDualFrameLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixBoundedDenominatorPrimeToOfIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedDenomRationalMatrixOfFinitePartStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

open GlobalTheory.StdAtPrime

namespace GlobalTheory.MoveDenom

set_option maxHeartbeats 1600000 in

theorem denomAt_of_move : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ l : ℕ, l.Prime → ∀ s : GA D V, ∃ c : ℕ, ∀ z : GA D V, OneAt V l z → ∀ (γ h : GA D V) (γ' : GL (Fin V.rank) D.host.E) (k : Bridge.Gf V) (bad : ℕ), GlobalTheory.Member.IsRat V γ γ' → l ∣ bad → SplitOffBad V bad h → Bridge.hLat V k = Formalism.L2.Pj.stdLat D.host.E V.rank → Bridge.hLat V k⁻¹ = Formalism.L2.Pj.stdLat D.host.E V.rank → fin V (s * z) = fin V γ * fin V h * k → DenomAt l c γ' := by
  intro D V hstd l hl s
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  set M := Matrix.GeneralLinearGroup.map (n := Fin V.rank) ι.toRingHom with hM
  obtain ⟨c1, hc1⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1).1
  obtain ⟨c2, hc2⟩ := GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over l hl V.rank (M (fin V s).1)⁻¹.1
  refine ⟨max c1 c2, ?_⟩
  intro z hz γ h γ' k bad hrat hlb hsob hk hk' heq
  set C : FiniteAdeleRing (𝓞 D.host.E) D.host.E := ((l ^ max c1 c2 : ℕ) : FiniteAdeleRing (𝓞 D.host.E) D.host.E) with hC
  have bs : Bnd l (C • (M (fin V s).1).1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc1 _ (le_max_left _ _) Q hQ i j
  have bs' : Bnd l (C • (M (fin V s).1)⁻¹.1) := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 _ (le_max_right _ _) Q hQ i j
  have ez := GlobalTheory.T.finiteMatrix_apply_eq_one_at_places_over_of_oneAt D ι h1 h2 h3 V l z hz
  have bz : Bnd l (M (fin V z).1).1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [ez Q hQ i j]; exact one_entry_v_le_one _ Q i j
  have bz' : Bnd l (M (fin V z).1)⁻¹.1 := GlobalTheory.T.adelicMatrix_boundedDenominator_primeTo_of_integral l hl _ _ fun Q hQ i j => by
    rw [inv_eq_one_off _ _ Q (ez Q hQ) i j]; exact one_entry_v_le_one _ Q i j
  have bk' : Bnd l (M k.1)⁻¹.1 := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k hk
  have bk : Bnd l (M k.1).1 := by
    have := bnd_inv_of_hLat_std D ι h1 h2 V hstd l k⁻¹ hk'
    rwa [Subgroup.coe_inv, map_inv, inv_inv] at this
  have h4 := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3
  obtain ⟨hid, hcj⟩ := GlobalTheory.T.placeIdempotent_components_conj_valuation D ι h1 h2 h4
  obtain ⟨-, e', P', he', hb', hs'⟩ := hsob
  have hp' : ∀ PP ∈ P', (l : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hpP
    obtain ⟨c, rfl⟩ := hlb
    exact hb' PP hPP (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hpP)
  obtain ⟨S, hSf, hSp, hS0⟩ := GlobalTheory.T.idempotent_add_conj_support_finite_prime_to_p D ι hid hcj l e' P' he' hp'
  obtain ⟨bh, bh'⟩ := GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite l hl _ (M (fin V h).1) S hSf hSp fun Q hQ i j =>
    GlobalTheory.T.supported_adelic_point_eq_one_where_idempotent_vanishes D ι V e' h hs' Q (hS0 Q hQ) i j
  have eγ : fin V γ = fin V s * fin V z * k⁻¹ * (fin V h)⁻¹ := by
    have e1 : fin V (s * z) = fin V s * fin V z := map_mul _ _ _
    rw [e1] at heq
    rw [heq]; group
  have eMγ : M (fin V γ).1 = M (fin V s).1 * M (fin V z).1 * (M k.1)⁻¹ * (M (fin V h).1)⁻¹ := by
    rw [eγ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
      map_mul, map_mul, map_mul, map_inv, map_inv]
  apply GlobalTheory.T.boundedDenom_rationalMatrix_of_finitePart D ι h1 V l (max c1 c2) γ γ' hrat
  · rw [eMγ, Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul]
    exact bnd_mul l _ _ _ (bnd_mul l _ _ _ (bnd_mul l _ _ _ bs bz) bk') bh'
  · rw [eMγ, _root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv,
      Units.val_mul, Units.val_mul, Units.val_mul, ← Matrix.mul_smul, ← Matrix.mul_smul, ← Matrix.mul_smul]
    exact bnd_mul l _ _ _ bh (bnd_mul l _ _ _ bk (bnd_mul l _ _ _ bz' bs'))

end GlobalTheory.MoveDenom
