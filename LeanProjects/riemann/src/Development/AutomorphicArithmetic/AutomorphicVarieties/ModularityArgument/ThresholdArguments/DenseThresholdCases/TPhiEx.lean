import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi E f).1, MonoidAlgebra.mapRingHom_single, map_one]
theorem UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), (∃ B : W.UniversalOrdinaryDeterminantRing K.r, True) ∧ ∀ B : W.UniversalOrdinaryDeterminantRing K.r, ∃ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X n B φ := by
  intro U Ω _ _ _ l _ c D T _ _ c' h K X n
  obtain ⟨hs, hq, hk⟩ := phiKer K.V
  obtain ⟨E, hE, hcp, hc⟩ := phiDet (maximalIdeal X.B) (algebraMap X.B X.A) X.inj K.V.pr hs hq (K.rho X n) (K.cpT X n)
    (fun g => (phiCpMap K X n g).2.2.2) (phiCpCont K X n)
    fun U hU hle => hk U hU fun A v hA hv => (phiUnr K X n A v hA hv).trans hle
  obtain ⟨ψ, hψ⟩ := phiPsiEx K X n
  obtain ⟨p, hD, hp⟩ := phiPair K.r X.inj (by norm_num) K.V.pr hs (K.rho X n) E ψ hE hc
    (fun g => (congrArg _ (hcp g)).trans (phiCpRed K X n g)) (phiIsPsi K X n ψ hψ) (phiPol K X n)
    (fun v => ⟨_, rfl, phiFlag K X n ψ hψ v⟩) (phiIne K X n)
  obtain ⟨B₀⟩ := U.b0 l T.L Ω K.s K.V c' 4 K.r X.B ⟨p⟩
  refine ⟨⟨B₀, trivial⟩, fun B => ?_⟩
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := B.univ X.B p
  refine ⟨φ, fun g => ?_, fun v i g => ?_⟩
  · have e := chi_map B.u.D (φ : B.B →+* X.B) (K.V.pr g)
    rw [h1, hD] at e
    exact e.symm.trans (hcp g)
  · have e := congrArg Units.val (DFunLike.congr_fun (h2 v i) g)
    rw [hp] at e
    exact e.trans (hψ v i g)
end
