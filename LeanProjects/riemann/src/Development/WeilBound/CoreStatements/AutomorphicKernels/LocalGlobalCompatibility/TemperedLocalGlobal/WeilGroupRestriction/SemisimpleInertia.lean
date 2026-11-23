import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankEquivariantFunctionalsCongr
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace SemisimpleInertia

theorem eq_one_of_semisimple {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hs : T.IsSemisimple) {m : ℕ} (hd : T.charpoly ∣ (X - 1 : ℂ[X]) ^ m) : T = 1 := by
  have hX : (X - 1 : ℂ[X]) = X - C 1 := by simp
  have h1 : minpoly ℂ T ∣ (X - C (1 : ℂ)) ^ m := by
    rw [← hX]; exact (LinearMap.minpoly_dvd_charpoly T).trans hd
  have hp : Prime (X - C (1 : ℂ)) := prime_X_sub_C 1
  obtain ⟨i, -, hass⟩ := (_root_.dvd_prime_pow hp m).1 h1
  have hsq : Squarefree (minpoly ℂ T) := hs.minpoly_squarefree
  have hi1 : i ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h2 : (X - C (1 : ℂ)) * (X - C 1) ∣ minpoly ℂ T := by
      rw [← sq]
      exact (pow_dvd_pow _ hlt).trans hass.symm.dvd
    exact hp.not_isUnit (hsq _ h2)
  have h3 : minpoly ℂ T ∣ X - C (1 : ℂ) :=
    hass.dvd.trans (by simpa using pow_dvd_pow (X - C (1 : ℂ)) hi1)
  have h4 : aeval T (X - C (1 : ℂ)) = 0 := by
    obtain ⟨q, hq⟩ := h3
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTw_of_deg (x : WD h) (s : ℝ) {t : Weil h} (ht : deg t = 0) :
    (x.lpTw s).charPol t = x.charPol t := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ, ht, zpow_zero, one_smul]

end SemisimpleInertia

open SemisimpleInertia in

theorem iwahori_fixed_vector_unipotent : K7 := by
  intro E Ω _ _ _ _ _ A w h rc hrc a σ hσ
  have hG : GlobalTheory.Published.GeometricLemma := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  have hSeg : GlobalTheory.Published.SegmentRepresentation := GlobalTheory.CompanionTheory.StdSubTop.segmentRepresentation
  have hZ : GlobalTheory.Published.ZelevinskyPolynomialRing :=
    GlobalTheory.zelevinskyPolynomialRing_of_parts hBZ hSeg (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg hSeg)
  obtain ⟨art, ha, ε, -, L⟩ := id hrc
  refine GlobalTheory.LocGL.UnramSupport.fixed_iwahori_ne_bot hG hZ hBZ (w.adicCompletion E) a σ.V σ.ρ σ.smooth σ.irred ?_
  intro s hs y hy
  have hs' : HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep s := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hcusp : y.IsCusp := hs'.isCusp hy
  have hdiv : ∀ t : Weil h, deg t = 0 → (rc y).charPol t ∣ (X - 1 : ℂ[X]) ^ a := by
    intro t ht
    have h1 := L.supp _ s hs' t
    have h2 := hσ t ht
    rw [rec_algNorm hrc σ, charPol_lpTw_of_deg _ _ ht] at h2
    rw [← h2, h1]
    exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
  have hirr := (L.cusp y).1 hcusp
  obtain ⟨n, b, hb, -⟩ := id hirr
  have hN : b.N = 0 := by
    have h0 := GlobalTheory.LocLanglands.TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h (rc y) hirr
    rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  have hI : ∀ τ : Ine (F := E) A, b.ρ (ineIncl h τ) = 1 := by
    intro τ
    have h0 := hdiv (ineIncl h τ) (by simp)
    rw [← hb, WD.charPol_mk] at h0
    exact eq_one_of_semisimple _ (b.semisimple _) h0
  have hunr : (rc y).unr := by
    rw [← hb, WD.unr_mk]
    exact ⟨hN, hI⟩
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact isUnramChar_of_isCusp_of_isSpherical hG hBZ hZ _ y hcusp ((hrc.isSpherical_iff y).2 hunr)

end PositivityTheory.Pf1.CLGD.K

end
