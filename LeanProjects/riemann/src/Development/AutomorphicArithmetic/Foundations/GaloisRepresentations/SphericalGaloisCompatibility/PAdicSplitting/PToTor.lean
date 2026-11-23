import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.InfLifts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.GoodLiftAlt
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.SuppOfTypeOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobenius
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOver
import Development.DiscreteGroups.GlobalIrreducibility.DzGalW
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InePolLpTwOfMemIne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IneInclOntoUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL GlobalTheory.DeRhamOfPlainTorus ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.ToralGalois.R2 GlobalTheory.UnitaryBC UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem split_of_padic {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E))
    (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : normV w = g ∧ IsSplitAt w := by
  have hq : normV w = g := DiscreteGroups.sglob.DzType.normV_eq_of_padic w g i hi
  refine ⟨hq, GlobalTheory.DenseInvFrob.isSplitAt_of_inertiaDeg_eq_one w ?_ ?_⟩
  · have hp : (Ideal.absNorm w.asIdeal).Prime := by
      have : Ideal.absNorm w.asIdeal = g := hq
      rw [this]
      exact Fact.out
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).1 hp
  · have hmem : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := by
      apply DiscreteGroups.sglob.DzType.mem_of_val_lt_one w
      have := DiscreteGroups.sglob.DzType.val_lt_one_of_norm_lt_one w g i hi (g : ℚ_[g]) Padic.norm_p_lt_one
      rw [map_natCast] at this
      rw [DiscreteGroups.sglob.DzType.alg_natCast]
      exact this
    have hsq := DiscreteGroups.sglob.DzType.g_not_mem_sq w g i hi
    have hl : g.Prime := Fact.out
    have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hl
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) = Ideal.span {((g : ℕ) : 𝓞 E)} := by
      rw [Ideal.map_span]; simp
    have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(g : ℤ)}) ≤ w.asIdeal := by
      rw [hmap, Ideal.span_le]; simpa using hmem
    have := w.isPrime
    have : w.asIdeal.LiesOver (Ideal.span {(g : ℤ)}) :=
      ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
    have hb : Ideal.span {(g : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(g : ℤ)}) w.asIdeal hb]
    by_contra hne
    rw [← ne_eq, Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le] at hne
    exact hsq (by simpa using hne)

private theorem dvd_of_support {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V) (s : Multiset (IrrGL k))
    (hs : HasSupport ρ s) (y : IrrGL k) (hy : y ∈ s) : y.1 ∣ N.factorial := by
  have h1 : 0 < y.1 := (hs.isCusp hy).1
  have h2 := hs.sum_fst
  have h3 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.single_le_sum (by simp) _ (Multiset.mem_map_of_mem _ hy)
  rw [h2, Fintype.card_fin] at h3
  exact Nat.dvd_factorial h1 h3

theorem UpperTheory.Gal.ToralGalois.R2.toTor :
    UpperTheory.Gal.InertialTypesAlt.SuppBC → UpperTheory.Gal.NearKilling.UnrField → UpperTheory.Gal.NearKilling.AllLift → UpperTheory.Gal.NearKilling.IneNorm → InfLifts → RecChars → UpperTheory.Zero.LLC.RecTExists → ToTor := by
  intro hSupp hUnr hLift hIne hInf hChars hRec E Ω _ _ _ _ _ _ l _ ι n hn π χ hs r hr w σ hσ hQ hM A h rc hrc
  obtain ⟨p, hp, i, hi⟩ := hQ
  haveI := hp
  obtain ⟨hq, hsp⟩ := split_of_padic w p i hi
  have hf : 0 < n.factorial := Nat.factorial_pos n
  have hSfin : {u : HeightOneSpectrum (𝓞 E) | ¬ ∃ B, (CG.mk π).HasSat u B}.Finite := by
    have h := Filter.eventually_cofinite.1
      (GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E n π)
    simpa only [CG.hasSat_mk] using h
  obtain ⟨Xf, hXT, hXw, -⟩ := hUnr E Ω w hsp _ hf _ hSfin
  obtain ⟨P, χ', hPL, hPs, hPr⟩ := hLift E Ω l n hn π χ hs _ (fun u hu => not_not.1 hu) Xf hXT
  obtain ⟨w', h', -⟩ := GlobalTheory.AboveL.exists_isPlaceOver_of_tower E Xf.K Ω A w h
  haveI : w'.asIdeal.LiesOver w.asIdeal := ⟨(GlobalTheory.AboveL.comap_eq_of_placeOver h h').symm⟩
  have hXfix := (hXw A h).1
  have hnorm := (hXw A h).2 w' h'
  obtain ⟨σ', hσ', -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL Xf.K n P w'
  obtain ⟨art, hart⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  obtain ⟨art', hart'⟩ := GlobalTheory.localArtinExists_holds Xf.K Ω A w' h'
  obtain ⟨g, hg1, -⟩ := hIne E Xf.K Ω A w w' h h' hXfix art art' hart hart'
  obtain ⟨ξ, hξ, hT, hU⟩ := hSupp E Ω n hn π { K := Xf.K, π := P } hPL A w w' h h' p i hi hXfix σ σ' hσ hσ' hM.1 n.factorial
    (by rw [hnorm, hq]) (fun s hs y hy => dvd_of_support _ s hs y hy)
  obtain ⟨-, hTS, hTP⟩ := id hT
  obtain ⟨rc', hrc'⟩ := hRec Xf.K Ω A w' h'
  have hCh := hChars Xf.K Ω A w' h' n σ' ξ hξ hTS
  have hB : ∀ s : ↥(Ine (F := E) A), (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).inePol (s : G E Ω) =
      ∏ j, (X - C ((ξ j (art' (ineIncl h' (g s))) : ℂˣ) : ℂ)) := fun s => by
    have := hTP rc hrc art' hart' (g s)
    rwa [show AlgEquiv.restrictScalars E ((g s : ↥(Ine (F := Xf.K) A)) : G Xf.K Ω) = (s : G E Ω) from hg1 s] at this
  refine ⟨Xf, P, χ', w', h', σ', rc', hPs, hPr ι r hr, hInf E Ω n hn π { K := Xf.K, π := P } hPL, hσ', hCh.1 (hU hM), hrc',
    fun t => ⟨g t, fun z => ?_, ?_⟩⟩
  · exact (DFunLike.congr_fun (hg1 t) z).symm
  · rw [hCh.2 rc' hrc' art' hart' (g t)]
    obtain ⟨a₀, ha₀, L⟩ := hrc
    have e1 : (rc (algNorm σ)).charPol (ineIncl h t) = (rc (algNorm σ)).inePol (t : G E Ω) :=
      (WD.inePol_of_mem_Ine _ t.2).symm
    have e2 : algNorm σ = (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - ((n : ℕ) : ℝ)) / 2 : ℝ) : ℂ) := rfl
    rw [e1, e2, L.nu, GlobalTheory.RoadU.DepthZeroRec.inePol_lpTw_of_mem_Ine _ _ t.2, hB t]
