import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHermSesqOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicDataStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateIStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalRealBasisComplexCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalProductThetaMemThetaSpaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareOrthoProductThetaEqProdStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthonormalBasisGaloisMapStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSquareEvenThetaConjugateLatticeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ConjNorm

noncomputable def torTw (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Tor D :=
  ⟨fun τ x => embT D τ (σ x), lamOf D cc δ⟩

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem norm_core (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L')
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (torTw D σ cc δ) t0 L L' G) :
    G ∈ Th D (torTw D σ cc δ) L L' ∧ ∀ x, normSq D (torTw D σ cc δ) (La D (torTw D σ cc δ) L L')
      (U D (torTw D σ cc δ) x G) = nrm1Sq (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t0) ^ (fF D * N * N') := by
  have g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨b, κ, hb, ⟨hκQ, hκ⟩, rfl⟩ := hG
  have hκ1 : ‖κ‖ = 1 := hκ (algebraMap Qbar ℂ)
  obtain ⟨L₁, L₁', h₁, h₁', hY⟩ := GlobalTheory.T.exists_selfDual_pair_galoisConjugate_homLattice D σ hσ N N' L L' hL hL'
  have hb' := GlobalTheory.T.orthonormalBasis_galois_map D σ hσ N N' _ b hb
  have eLa : La D (torTw D σ cc δ) L L' = La D (tor0 D cc δ) L₁ L₁' := by
    unfold La
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, A, hA, rfl⟩
      exact ⟨w, hw, A.map σ, (hY A).1 hA, rfl⟩
    · rintro ⟨w, hw, A, hA, rfl⟩
      have e : (A.map σ.symm).map σ = A := by ext i j; simp
      refine ⟨w, hw, A.map σ.symm, (hY _).2 (by rw [e]; exact hA), ?_⟩
      congr 1
      funext τ i j
      simp [embV, tor0, torTw]
  obtain ⟨hd, hinv⟩ := GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant D g1 cc δ hc t0 ht
  obtain ⟨o1, o2⟩ := GlobalTheory.T.orthonormal_realBasis_complex_coordinates D g1 cc δ N N' _ _ hb'
  have hth := GlobalTheory.T.orthonormalProductTheta_mem_thetaSpace D (tor0 D cc δ) N N' _ _ o1 _ hd hinv
  have hn := GlobalTheory.T.meanSquare_orthoProductTheta_eq_prod D (tor0 D cc δ) N N' _ _ (GlobalTheory.T.idealPeriodLattice_of_curveDatum D g1 cc δ hc).1 o1 o2 _ hd.continuous (by
    intro ω hω z
    obtain ⟨m, -, hm⟩ := hinv ω hω
    have := congrArg norm (hm z)
    rwa [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul] at this)
  have kB : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) (fun j => (b j).map σ)) := Or.inl ⟨_, _, hb', rfl⟩
  have kL : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') := Or.inr ⟨_, _, h₁, h₁', rfl⟩
  obtain ⟨-, u2, u3, -⟩ := GlobalTheory.ConjNorm.unitary_all D cc δ hc N N' _ _ kB kL _ hth
  have u4 := (GlobalTheory.ConjNorm.unitary_all D cc δ hc N N' _ _ kL kL _ u2).1
  unfold Th
  rw [eLa]
  set F := Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) (fun j => (b j).map σ)) (La D (tor0 D cc δ) L₁ L₁')
    (pullB D (tor0 D cc δ) (fun j => (b j).map σ) (GL3Theta.th0 (lamOf D cc δ) t0)) with hF
  change (fun z => κ * F z) ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') ∧
    ∀ x, normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (U D (tor0 D cc δ) x (fun z => κ * F z)) = _
  refine ⟨⟨u2.1.const_mul κ, fun x hx z => ?_⟩, fun x => ?_⟩
  · have := u2.2 x hx z
    simp only [U] at this ⊢
    linear_combination κ * this
  · refine Eq.trans ?_ hn
    rw [← u3, ← u4 x]
    unfold normSq
    simp only [U, norm_mul, hκ1, one_mul]

theorem exists_aut (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ)
    (hM : ∀ τ x, embT D τ x ∈ M) :
    ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) ∧
      ∀ τ x, cj M ρ (embT D τ x) = embT D τ (σ x) := by
  obtain ⟨⟨hPsi, -⟩, hperm⟩ := GlobalTheory.T.inducedType_thetaGenusOne_permutes D
  obtain ⟨π, hπ⟩ := hperm M ρ hK hM
  rcases isEmpty_or_nonempty D.what₂.Tau with h | ⟨⟨τ₀⟩⟩
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun τ => h.elim τ⟩
  have hmul : ∀ g h : D.R.GG, D.host.sigmaOf (g * h) = D.host.sigmaOf g * D.host.sigmaOf h :=
    fun g h => map_mul _ g h
  have hone : D.host.sigmaOf 1 = 1 := map_one _
  have key : ∀ (τ : D.what₂.Tau) (g : D.R.GG) (x : D.host.E),
      embT D τ (D.host.sigmaOf g x) = D.host.φ₀ (D.host.sigmaOf ((D.eTau τ : D.R.GG) * g) x) := by
    intro τ g x
    rw [hmul]; rfl
  have key1 : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embT D τ x = D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have main : ∀ τ x, cj M ρ (embT D τ x) = embT D τ (D.host.sigmaOf
      ((D.eTau τ₀ : D.R.GG)⁻¹ * (D.eTau (π τ₀) : D.R.GG)) x) := by
    intro τ x
    have e1 : embT D τ x = embT D τ₀ (D.host.sigmaOf
        ((D.eTau τ₀ : D.R.GG)⁻¹ * (D.eTau τ : D.R.GG)) x) := by
      rw [key, mul_inv_cancel_left, key1]
    rw [e1, hπ, key, key]
    congr 3
    rw [mul_left_comm, mul_comm (D.eTau (π τ₀) : D.R.GG), mul_left_comm]
  refine ⟨_, fun a => ?_, main⟩
  apply (embT D τ₀).injective
  rw [← main, hPsi, (hK a).2]

theorem exists_ext (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), M ≤ M' ∧ Qbar ≤ M' ∧
      ∀ x ∈ M, ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ) (L := M) (M := ℂ) (E := algebraicClosure M ℂ) ρ
  have hle : M ≤ (algebraicClosure M ℂ).restrictScalars ℚ := fun x hx =>
    (algebraicClosure M ℂ).algebraMap_mem ⟨x, hx⟩
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, hle, fun x hx => ?_, fun x hx => ?_⟩
  · rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
    exact (mem_algebraicClosure_iff.1 hx).extendScalars (algebraMap ℚ M).injective
  · rw [← hφ]
    simp only [TaylorLogMetric.liftM, dif_pos hx, dif_pos (hle hx)]
    rfl

theorem norm_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L') (hN : Even (N * N'))
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ) (hQ : Qbar ≤ M)
    (hD : DataIn D (tor0 D cc δ) M) (hC : CoefIn D G M)
    (t0' : ℂ) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0')
    (x : VC D N N') (hx : LaQ D (tor0 D cc δ) L L' x) (hCx : CoefIn D (U D (tor0 D cc δ) x G) M) :
    (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧
    ∃ x', fnConj D M ρ (U D (tor0 D cc δ) x G) = U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ G) ∧
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
          (U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ G)) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
  have g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨cc', δ', hc', -, hlam⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M ρ hK hD.2.1 hD.2.2 1 one_pos
  obtain ⟨σ, hσ, hσ'⟩ := exists_aut D M ρ hK hD.1
  have hT : torConj D (tor0 D cc δ) M ρ = torTw D σ cc' δ' := by
    unfold torConj torTw
    congr 1
    funext τ y
    exact hσ' τ y
  have hGTh : G ∈ Th D (tor0 D cc δ) L L' :=
    (norm_core D AlgEquiv.refl (fun _ => rfl) cc δ hc t0 ht L L' hL hL' G hG).1
  have hE := (GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht N N' L L' hL hL' hN G hG M ρ hD hC).2.1 t0' ht'
  obtain ⟨m, hm, hmx⟩ := hx
  have htors := ((GlobalTheory.T.admJ_and_torsion_data_algebraic D g1).2 cc δ hc).2
  obtain ⟨x', hx', -⟩ := GlobalTheory.T.galois_data_exists D cc δ hc M ρ hK hD
    (fun t h1 h2 => ⟨hQ (htors t h1 h2).1, hQ (htors t h1 h2).2⟩) N N' L L' hL hL' x (2 * m) ⟨m, hm, hmx⟩ (by omega)
  have hcomb : comb D (tor0 D cc δ) (fun _ : Fin 1 => (1 : ℂ)) (fun _ => 0) G = G := by
    funext z; simp [comb, U_zero]
  have hg := GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D cc δ hc M ρ hK hD N N' L L' hL hL' 1 (fun _ => 1) (fun _ => 0) G x x' m hGTh hm hmx
    (fun _ => by rw [smul_zero]; exact zero_mem _) hx'
  rw [hcomb] at hg
  refine ⟨hlam ▸ (GlobalTheory.T.idealPeriodLattice_of_curveDatum D g1 cc' δ' hc').1, x', (hg hC hCx).1, ?_⟩
  rw [hT] at hE ⊢
  rw [hlam] at ht' ⊢
  exact (norm_core D σ hσ cc' δ' hc' t0' ht' L L' hL hL' _ hE).2 x'

theorem norm_big (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L') (hN : Even (N * N'))
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hQ : Qbar ≤ M)
    (hD : DataIn D (tor0 D cc δ) M) (hC : CoefIn D G M)
    (t0' : ℂ) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0')
    (x : VC D N N') (hx : LaQ D (tor0 D cc δ) L L' x) (hCx : CoefIn D (U D (tor0 D cc δ) x G) M) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
        (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
      nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
  rcases (GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M ρ hD).1 with hK | hK
  · obtain ⟨-, x', e1, e2⟩ := norm_fix D cc δ hc t0 ht L L' hL hL' hN G hG M ρ hK hQ hD hC t0' ht' x hx hCx
    rw [e1, e2]
  · obtain ⟨-, hT, hb⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M (rhoBar M ρ) hD
    have hbb : rhoBar M (rhoBar M ρ) = ρ := by
      ext y; simp [rhoBar]
    rw [hbb] at hT hb
    have hl : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (rhoBar M ρ) (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    have hmem : ∀ z, z ∈ lamConj M ρ (lamOf D cc δ) ↔
        (starRingEnd ℂ) z ∈ lamConj M (rhoBar M ρ) (lamOf D cc δ) := by
      intro z
      rw [hl, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨_, h, by simp⟩
    have ht'' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M (rhoBar M ρ) (lamOf D cc δ)) ((starRingEnd ℂ) t0') := by
      obtain ⟨a1, a2, a3⟩ := ht'
      rw [hmem] at a1 a2 a3
      refine ⟨by simpa [map_ofNat] using a1, ?_, ?_⟩
      · simpa [map_ofNat] using a3
      · simpa [map_ofNat, sub_eq_add_neg] using a2
    obtain ⟨hlat, x', e1, e2⟩ :=
      norm_fix D cc δ hc t0 ht L L' hL hL' hN G hG M (rhoBar M ρ) hK hQ hD hC _ ht'' x hx hCx
    have hTh := (GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht N N' L L' hL hL' hN G hG M (rhoBar M ρ) hD hC).1
    have e3 := ((hb N N' L L' (fnConj D M (rhoBar M ρ) G)).2.2 hTh).2 hL hL' x'
    have e4 := GlobalTheory.T.meanSquare_evenTheta_conjugateLattice _ hlat ((starRingEnd ℂ) t0')
    rw [Complex.conj_conj, ← hl] at e4
    rw [(hb N N' L L' (U D (tor0 D cc δ) x G)).1, e1, hT, e3, e2, e4]

theorem useNorm_all : ∀ D : D7, useNorm D := by
  intro D cc δ hc t0 ht N N' L L' hL hL' hN G hG M ρ hD hC t0' ht'
  obtain ⟨M', ρ', hle, hQ, he⟩ := exists_ext M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [he (g2 (lamOf D cc δ)) hD.2.1, he (g3 (lamOf D cc δ)) hD.2.2]
  have hT : torConj D (tor0 D cc δ) M ρ = torConj D (tor0 D cc δ) M' ρ' := by
    unfold torConj
    congr 1
    funext τ y
    exact (he _ (hD.1 τ y)).symm
  have hf : ∀ F : VC D N N' → ℂ, CoefIn D F M → fnConj D M ρ F = fnConj D M' ρ' F := by
    intro F hF
    funext z
    unfold fnConj
    exact tsum_congr fun α => by rw [he _ (hF α)]
  have hD' : DataIn D (tor0 D cc δ) M' := ⟨fun τ y => hle (hD.1 τ y), hle hD.2.1, hle hD.2.2⟩
  have main : ∀ x, LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x G) M →
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
          (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
    intro x hx hCx
    rw [hf _ hCx, hT, hl]
    exact norm_big D cc δ hc t0 ht L L' hL hL' hN G hG M' ρ' hQ hD' (fun α => hle (hC α)) t0' (hl ▸ ht') x hx
      (fun α => hle (hCx α))
  refine ⟨?_, main⟩
  have := main 0 ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩ (by rw [U_zero]; exact hC)
  rwa [U_zero] at this

end GlobalTheory.ConjNorm
