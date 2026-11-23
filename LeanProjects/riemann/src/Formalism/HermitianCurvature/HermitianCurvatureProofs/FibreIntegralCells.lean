import Formalism.HermitianCurvature.HermitianCurvatureProofs.RearrSymm

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.FK

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ}

theorem gPoly_of (TT : ℝ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    PBI.gPoly TT (Matrix.of (Matrix.of.symm M : G.Mat (r + 1))) = PBI.gPoly TT M := rfl

private theorem det_eq_one_of_lower_unitriangular' {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (h0 : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (fun i j hij => h0 i j hij)]
  simp [h1]

private theorem det_eq_one_of_upper_unitriangular {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (h0 : ∀ i j, j < i → U i j = 0)
    (h1 : ∀ i, U i i = 1) : U.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]

theorem gPoly_LU (TT : ℝ) {L M U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hL : L ∈ C2.LTset (r + 1))
    (hU : U ∈ C2.UTset (r + 1)) : PBI.gPoly TT (L * M * U) = PBI.gPoly TT M := by
  obtain ⟨hL0, hL1⟩ := hL
  obtain ⟨hU0, hU1⟩ := hU

  have hsub : (L * M * U).submatrix Fin.castSucc Fin.castSucc =
      L.submatrix Fin.castSucc Fin.castSucc * M.submatrix Fin.castSucc Fin.castSucc *
        U.submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc,
      hL0 (Fin.castSucc i) (Fin.last r) (Fin.castSucc_lt_last i),
      hU0 (Fin.last r) (Fin.castSucc j) (Fin.castSucc_lt_last j), zero_mul, mul_zero, add_zero]
  have hL' : (L.submatrix Fin.castSucc Fin.castSucc).det = 1 :=
    det_eq_one_of_lower_unitriangular' (fun i j h => hL0 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun i => hL1 _)
  have hU' : (U.submatrix Fin.castSucc Fin.castSucc).det = 1 :=
    det_eq_one_of_upper_unitriangular (fun i j h => hU0 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h)) (fun i => hU1 _)
  unfold PBI.gPoly
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_eq_one_of_lower_unitriangular' hL0 hL1,
    det_eq_one_of_upper_unitriangular hU0 hU1, hL', hU']
  simp

theorem gPoly_pt (TT : ℝ) (a : C.LPt) : PBI.gPoly TT (D.ptMatN a (r + 1)) = D.ptG TT r a := by
  have h : (D.ptMatN a (r + 1)).submatrix Fin.castSucc Fin.castSucc = D.ptMatN a r := by
    ext i j
    rfl
  unfold PBI.gPoly D.ptG
  rw [h]

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.FK

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD

theorem fibre_integral_cells : PBI.FibIntCells := by
  intro Wp Wq _ _ _ _ _ _ P p
  set S := p.T.base with hS
  have hz : C2.StdZ P.k P.r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ P.k P.r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  obtain ⟨μ0, hμ0⟩ := exists_haar_stabilizer P.k P.r S.z hz
  obtain ⟨μ0', hμ0'⟩ := exists_haar_stabilizer P.k P.r S.z' hz'
  obtain ⟨c1, hc1, hN1⟩ := disintN P.k P.r S.z hz μ0 S.μN hμ0 S.haarN
  obtain ⟨c2, hc2, hN2⟩ := disintN P.k P.r S.z' hz' μ0' S.μN hμ0' S.haarN
  refine ⟨μ0, μ0', (((c1 * c2 : NNReal) : ℝ) : ℂ), hμ0, hμ0', ?_⟩
  intro sec hsec F hF a σ d ha hm
  obtain ⟨hw, hd0⟩ := Dx2.VV.ptMatN_monoP' a (P.r + 1) ha.2 ha.1
  set w := ha.2 ▸ D.ptPerm a with hwdef
  set d0 := ha.2 ▸ D.ptDiag a with hd0def
  obtain ⟨e, hemp, he⟩ := splitUT (P.r + 1) w
  have hPT := phiTopCoords (P.r + 1) σ w d d0 (Wq →L[ℂ] Wp)
    ((((c1 * c2 : NNReal) : ℝ) : ℂ) • PBI.phi0 S μ0 μ0' sec F) hd0 (hm.trans hw)
  rw [hPT]
  set TT := Tz P.k P.r S.z * Tz P.k P.r S.z' with hTT
  have hgP : ∀ Y : (C2.LPidx w → ℂ) × (G.UT (P.r + 1) → ℂ),
      PBI.gPoly TT (lowP w Y.1 * C2.monoP w d0 * G.upper Y.2) = D.ptG TT P.r a := by
    intro Y
    rw [FK.gPoly_LU TT (UC.lowerUnipotent_mem w Y.1).1 (UC.upper_mem Y.2), ← hw, FK.gPoly_pt]
  show D.vecV S p.ν' p.m₀ F a = _
  by_cases hG : 0 < D.ptG TT P.r a
  · obtain ⟨σ0, hE⟩ := Dx2.VV.exE S p.ν' p.m₀ p.hF a ha hG
    have hγe := hE.1
    have hZe := hE.2.1
    have hDe := hE.2.2.1
    set γ0 := p.m₀ * σ0 with hγ0
    have hV := isotropic_vectors_linear_indep P.k P.r Wp Wq S p.ν' p.m₀ F a ha γ0 p.hF hG hγe hZe hDe
    rw [hV]
    have hZw : Zhat P.k P.r S.z S.z' γ0 = C2.monoP w d0 := hZe.trans hw
    have hpos : 0 < Gf P.k P.r S.z S.z' γ0 := by
      rw [← ptG_spec P.k P.r S.z S.z' a _ ha hZe]; exact hG
    have hrel := relevant_points_holds P.k P.r Wp Wq S a γ0 ha hγe hZe
    obtain ⟨θ1, hθ1, hint1⟩ := CV.orbJConv_cpt S γ0 w d0 F hγe hrel hd0 hZw hpos hF
    have hex : ∃ θ, D.IsNormCut S γ0 (D.muR S γ0 w) θ ∧
        Integrable (fun q => θ q • D.orbIntegrand S γ0 F q) S.μSS := ⟨θ1, hθ1, hint1⟩
    unfold D.orbJ
    rw [dif_pos hex]
    obtain ⟨hθ, hint⟩ := hex.choose_spec
    obtain ⟨hI, hEq⟩ := OG.orb_int S hγe hd0 hZw hpos hrel e hemp he hμ0 hμ0' hc1 hc2 hN1 hN2 F _ hθ hint
    rw [hEq, OJ.cell_int S γ0 w hμ0 hμ0' F hI, RCLike.real_smul_eq_coe_smul (K := ℂ), ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.smul_apply]
    rw [smul_comm]
    congr 2
    have hZp : 0 < PBI.gPoly TT (Matrix.of (Matrix.of.symm (lowP w Y.1 * C2.monoP w d0 * G.upper Y.2) :
        G.Mat (P.r + 1))) := by
      rw [FK.gPoly_of, hgP Y]; exact hG
    unfold PBI.phi0
    rw [if_pos hZp]
    obtain ⟨hsG, hsZ, hsD⟩ := hsec.2 _ hZp
    have hv := lowPH_UT (w := w) Y.1
    have hu := UC.upper_mem Y.2
    have hZ1 : Zhat P.k P.r S.z S.z' ((C2.tauM P.k P.r S.z (lowP w Y.1)ᴴ)⁻¹ * γ0 *
        C2.tauM P.k P.r S.z' (G.upper Y.2)) = lowP w Y.1 * C2.monoP w d0 * G.upper Y.2 := by
      rw [Formalism.FourierDecayAlt.P.zhat_equivalence P.k P.r S.z S.z' hz hz' _ (A.n_in_S (A.tau_N hz hv)) _
          (A.n_in_S (A.tau_N hz' hu)) γ0,
        (Formalism.FourierDecayAlt.P.c2_tau_mem P.k P.r S.z hz _ hv).2.2, (Formalism.FourierDecayAlt.P.c2_tau_mem P.k P.r S.z' hz' _ hu).2.2,
        Matrix.conjTranspose_conjTranspose, hZw]
    symm
    exact FB.fib_indep S p.ν' p.m₀ p.hF a ha hG hE hμ0 hμ0' F hv hu hsG (hsZ.trans hZ1.symm) hsD
  · have h0 : D.vecV S p.ν' p.m₀ F a = 0 := by
      unfold D.vecV; rw [dif_neg (fun h => hG h.2)]
    rw [h0]
    symm
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [Pi.smul_apply, Pi.zero_apply]
    unfold PBI.phi0
    rw [if_neg (by rw [FK.gPoly_of, hgP Y]; exact hG), smul_zero, smul_zero]

end Formalism.FourierDecayAlt.P
