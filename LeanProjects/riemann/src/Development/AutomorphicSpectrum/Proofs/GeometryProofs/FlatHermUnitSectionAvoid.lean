import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionAvoidPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariantStatement

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_blockNonzero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem PtOver.eventually_ptOver {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {F : Type} [Field F] [NumberField F] {y : (Σ k, ι k) → Ω} {φ : F →+* Ω} (hO : OverInt y φ)
    {σ : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : PtOver y φ σ z) :
    ∀ᶠ w in nhds z, w ∈ mcPts (mCoordIdeal y) → PtOver y φ σ w := by
  classical
  let e := Finite.equivFin (F →+* ℂ)
  let t : (F →+* ℂ) → ℝ := fun τ => ((e τ : ℕ) : ℝ)
  have ht : Function.Injective t := fun a b hab => by
    have h0 : ((e a : ℕ) : ℝ) = ((e b : ℕ) : ℝ) := hab
    have : ((e a : ℕ)) = (e b : ℕ) := by exact_mod_cast h0
    exact e.injective (Fin.ext this)
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ t hO
  filter_upwards [hu.near σ z hz] with w hw hwP
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hO w hwP
  have h1 : u w = t τ := (hu.near τ w hτ).self_of_nhds
  have h2 : τ = σ := ht (h1.symm.trans hw)
  exact h2 ▸ hτ

theorem FlatHerm.exists_rep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (W : Ideal (MRing ι)), OverInt y φ → IsArithVar (mCoordIdeal y) d → IsSmoothHerm A → IsMultiProjPrime W → mCoordIdeal y ≤ W → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = S.M * A.a k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * S.g - g' * S.f ∈ mCoordIdeal y ∧ IsUnitSec (mCoordIdeal y) f' g' ∧ ∀ σ z, PtOver y φ σ z → ‖evC z f'‖ = (S.κ σ * A.h z) ^ S.M * ‖evC z g'‖ := by
  intro K _ ι _ Ω _ F _ _ y φ A S d W hO hV hA hW hPW
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, hrel, hunit⟩ :=
    GlobalTheory.T.unit_section_avoid_prime K ι (mCoordIdeal y) W S.f S.g S.df S.dg hV.2.1 hW hPW S.hf S.hg S.g_ne S.unit
  refine ⟨f', g', df', dg', hf', hg', fun k => (hdeg k).trans (S.deg k), hfW, hgW, hrel, hunit, ?_⟩
  intro σ z hz
  have hcl := GlobalTheory.T.complex_points_dense_nonvanishing K ι (mCoordIdeal y) d S.g hV S.g_ne hz.1
  have hfreq := mem_closure_iff_frequently.mp hcl
  have hnear := PtOver.eventually_ptOver hO hz
  have hcontA : ContinuousAt A.h z :=
    (hA.continuousOn).continuousAt (isOpen_blockNonzero.mem_nhds hz.1.1)
  have hcf : Continuous fun w : (Σ k, ι k) → ℂ => evC w f' := MvPolynomial.continuous_eval _
  have hcg : Continuous fun w : (Σ k, ι k) → ℂ => evC w g' := MvPolynomial.continuous_eval _
  have hL : Filter.Tendsto (fun w => ‖evC w f'‖) (nhds z) (nhds ‖evC z f'‖) :=
    hcf.norm.continuousAt
  have hR : Filter.Tendsto (fun w => (S.κ σ * A.h w) ^ S.M * ‖evC w g'‖) (nhds z)
      (nhds ((S.κ σ * A.h z) ^ S.M * ‖evC z g'‖)) :=
    (((continuousAt_const.mul hcontA).pow S.M).mul hcg.norm.continuousAt)
  refine tendsto_nhds_unique_of_frequently_eq hL hR ?_
  refine (hfreq.and_eventually hnear).mono ?_
  rintro w ⟨⟨hwP, hgw⟩, hwσ⟩
  have hover := hwσ hwP
  have hn := S.norm σ w hover
  have h0 : evC w f' * evC w S.g - evC w g' * evC w S.f = 0 := by
    have := hwP.2 _ hrel
    simpa [evC, map_sub, map_mul] using this
  have h1 : ‖evC w f'‖ * ‖evC w S.g‖ = ‖evC w g'‖ * ‖evC w S.f‖ := by
    rw [← norm_mul, ← norm_mul, sub_eq_zero.mp h0]
  have hg0 : ‖evC w S.g‖ ≠ 0 := norm_ne_zero_iff.mpr hgw
  apply mul_right_cancel₀ hg0
  rw [h1, hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
