import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoCaten
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsAlgebraicPointOfGroupDeterminant
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaMvpsCot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dim_le_of_int (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ h =>
    Ideal.IsIntegral.comap_lt_comap (R := R) h

theorem UpperTheory.V.Ws.Eb.htLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (T : Type) [CommRing T] [IsDomain T] [Algebra c.O T] [IsCO c.O T] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] T), Function.Injective f → (f : MvPowerSeries (Fin N) c.O →+* T).Finite → ∀ x : T →ₐ[c.O] PadicAlgCl l, (N : ℕ∞) ≤ (RingHom.ker x).height := by
  intro l _ c N T _ _ _ _ f hinj hfin x
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI := UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant c.O T (PadicAlgCl l) x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := UpperTheory.V.Alg.co_caten c.O T (RingHom.ker x)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h2 := (UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd c.O ϖ hϖ (Fin N)).2.1
  have h3 : ringKrullDim T = ringKrullDim (MvPowerSeries (Fin N) c.O) := by
    letI : Algebra (MvPowerSeries (Fin N) c.O) T := (f : MvPowerSeries (Fin N) c.O →+* T).toAlgebra
    haveI : Module.Finite (MvPowerSeries (Fin N) c.O) T := hfin
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  have h4 : ringKrullDim (T ⧸ RingHom.ker x) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange x).toRingEquiv,
      ← IsDiscreteValuationRing.ringKrullDim_eq_one c.O]
    exact dim_le_of_int c.O x.range
  rw [h3, h2, Fintype.card_fin] at h1
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
    rw [← h1]; exact add_le_add le_rfl h4
  have h6 : (N : ℕ∞) + 1 ≤ (RingHom.ker x).height + 1 := by exact_mod_cast h5
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h6
