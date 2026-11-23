import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PmSeedP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointRepresentationWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaModularIdealMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EigenbasisRankFour

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
private theorem gsp_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) :
    IsGSp (f ν) (g.map f) := by
  have a : adj (g.map f) = (adj g).map f := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  unfold IsGSp at h ⊢
  rw [a, ← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]
theorem UpperTheory.V.Th.local_zero_of_modular_p :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
        X.LocZero J (y : X.A →+* PadicAlgCl l) := by
  intro hU hA Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ y hs q hq hqy
  obtain ⟨w, κ, π, a, k, hgap, hw, hκ, hk, hev, hκw, hreg, hatt⟩ := hs.aut
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Even (w 0 + n) := ⟨(w 0).natAbs, by
    rcases Int.natAbs_eq (w 0) with e | e <;> exact Int.even_iff.2 (by omega)⟩
  obtain ⟨d0, h0, e0⟩ := hgap 0
  obtain ⟨d1, h1, e1⟩ := hgap 1
  obtain ⟨d2, h2, e2⟩ := hgap 2
  replace e0 : w 0 = w 1 + 2 * d0 := e0
  replace e1 : w 1 = w 2 + 2 * d1 := e1
  replace e2 : w 2 = w 3 + 2 * d2 := e2
  rw [Int.even_iff] at hn hev
  obtain ⟨φ', hφ'⟩ := (_root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X n).2 B
  obtain ⟨m, hm, hmk⟩ := Pt.ptWts K X B n φ' hφ' y w (fun i => Int.even_iff.2 (by fin_cases i <;> simp <;> omega)) hw
  have hg : ∀ v i j, i < j → m v j + 2 ≤ m v i := fun v i j hij => by
    have := hm v i j
    fin_cases i <;> fin_cases j <;> simp at hij this ⊢ <;> omega
  obtain ⟨hi, hi'⟩ := Pt.ptIrr K n _ hs.irr
  have hc := Pt.rho_cont K n (Pt.pt_cont X y hi)
  have hrep : (Link.pt φ' y).IsRep (K.rhoQ n _) := auRep D T c' h K X B n φ' hφ' y _ fun _ => rfl
  have hmul : ∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g))))
      ((X.P.map (y : X.A →+* PadicAlgCl l)).r g) := fun g => by
    rw [← y.commutes]
    exact gsp_map (y : X.A →+* PadicAlgCl l) (X.pair.mult g)
  have hunr := Pt.ptUnr K n (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl := Pt.ptFlag K X B n φ' hφ' y
  obtain ⟨Pp, hPp⟩ := Pt.ptPair K n _ hmul
  have haut := _root_.UpperTheory.V.Z.Win.Birth.ptAutR'_alt hU.pr K n ι _ hmul κ π a k hκ hk (Int.even_iff.2 (by omega)) hκw hreg hatt
    (Z.ImaginaryQuadraticEtaCharacter.potOfPair l T.L Ω K.s 4 _ _ Pp hPp _ m hg hfl hmk)
  have hJx := _root_.UpperTheory.V.Ws.Pt.point_representation_weights hU.pr l T.L Ω K.s K.V c' 4 K.r B ι J₀ hM.pt _ _ m (by norm_num) (by norm_num) hrep hc haut hunr hg hfl hmk
  rw [← _root_.UpperTheory.V.Ws.hida_modular_ideal_map hU D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ', Ideal.map_le_iff_le_comap]
  exact _root_.UpperTheory.V.Th.eigenbasis_rank_four hU hA l T.L Ω K.s K.V K.hV K.noMu c' K.large K.r B Λ ι J₀ hM.toHidaProps K.v0 (P1.condC D T hF hD c' h K)
    (P1.condD D T hF hD c' h K) _ _ m hJx hrep hc haut hunr hi' hg hfl hmk
    _ (hq.comap φ') fun b hb => hqy _ hb
end
