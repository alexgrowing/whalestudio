import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBlockActionInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem exists_orbit (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g0 : B.Mat k n) (h : PBQ.pbF Bj B0 e H g0 ≠ 0) :
    ∃ x, PBQ.GoodP Bj x ∧ ∃ ξ : Mt k n × Mt k n, PBG.InR B0 ξ ∧
      H (D.castM e (PBQ.sP Bj x) * g0 * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0 := by
  by_contra hno
  push Not at hno
  apply h
  unfold PBQ.pbF
  rw [← integral_zero (PBQ.XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  show PBQ.pbI Bj B0 e H g0 x = 0
  unfold PBQ.pbI
  have hK : PBG.Kr B0 H (D.castM e (PBQ.sP Bj x) * g0) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    rw [hno x hx ξ hξ, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

theorem norm_entry_le_gN (g : B.Mat k n) (i j : Fin (2 * n + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem orbit_gen (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hz : B0.z = D.castV e (liftVec k p ρ Bj.z))
    (Z : Matrix (Fin p) (Fin p) ℂ) (μ : B.Mat k ρ) (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k ρ)
    (x : PBQ.XP k p ρ) (hx : PBQ.GoodP Bj x) (ξ : Mt k n × Mt k n) (hξ : PBG.InR B0 ξ) (g : B.Mat k n)
    (hg : g = D.castM e (PBQ.sP Bj x) * D.castM e (U.mMap k p ρ Z μ) * Matrix.of ξ.2 * Matrix.of ξ.1) :
    g ∈ B.GV k n ∧ (∃ u : Matrix (Fin p) (Fin p) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ ∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧
      (∀ l, Dmin k n B0.z B0.z' g l = Dmin k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) l) ∧
      Gf k n B0.z B0.z' g = Gf k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hg ⊢
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  have hm : U.mMap k p ρ Z μ ∈ B.GV k (p + ρ) := (Formalism.FourierDecayAlt.P.slice_membership k p ρ).1 Z μ hZ hμ
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (PartialBesselProperness.sP_GV Bj x) hm) hξ.2.1)
      hξ.1.1
  · refine ⟨G.upper (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩),
      LeftFubiniLemmas.upper_isUpUni _, fun a b => ?_⟩
    have hZh : U.Zh k p ρ g = Z * G.upper (fun q : G.UT p =>
        (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
      have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice k p ρ 0 0 Z μ
      rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
      rw [hg, PBQ.zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, PBQ.zh_sP_mul, e0,
        PBQ.nblk_upper _ hξ.2]
    rw [← hZh]
    exact norm_entry_le_gN g _ _
  · obtain ⟨h, hh, m, hmN, hs⟩ := PartialBesselProperness.leftFactor_mem Bj x
    rw [← hz] at hh
    have hhu : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
    have hmu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hmN.1
    set pp : B.SS k (p + ρ) := ((Matrix.of.symm h⁻¹, Matrix.of.symm m⁻¹), ξ) with hpp
    have hin : B0.inSS pp := ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN, hξ.1, hξ.2⟩
    have hsg : B.sgs pp (U.mMap k p ρ Z μ) = g := by
      rw [hg, hs]
      simp only [B.sgs, hpp]
      change (h⁻¹)⁻¹ * (m⁻¹)⁻¹ * U.mMap k p ρ Z μ * Matrix.of ξ.2 * Matrix.of ξ.1 = _
      rw [Matrix.nonsing_inv_nonsing_inv _ hhu, Matrix.nonsing_inv_nonsing_inv _ hmu]
    refine ⟨fun l => ?_, ?_⟩
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs B0 hin _ l
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs B0 hin _

end gen

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1 h2; rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lowV_top {P : M.Par} (p : KB.Pl P Wp Wq) (e : P.r + (P.r - P.r) = P.r) :
    U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z) = (p.T.bs P.r).z ∧
      U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z') = (p.T.bs P.r).z' := by
  unfold D.LevTower.base
  rw [← p.T.z_lev P.r le_rfl, ← p.T.z'_lev P.r le_rfl, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩

theorem orbit_point {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Z : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)) (hZ : Z.det ≠ 0)
    (hμ : μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)) (h : CutEX.pbTop p G Z μ ≠ 0) :
    ∃ g ∈ B.GV P.k P.r, G g ≠ 0 ∧ ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧ Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ = Z.det ∧
      Gf P.k P.r p.T.base.z p.T.base.z' g =
        Complex.normSq Z.det * Gf P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' μ := by
  have e : P.r + (P.r - P.r) = P.r := by omega
  have hμGV : μ ∈ B.GV P.k (P.r - P.r) := hμ.1
  unfold CutEX.pbTop PBQ.pbT at h
  obtain ⟨x, hx, ξ, hξ, hG⟩ := exists_orbit _ _ _ _ _ h
  have hz : p.T.base.z = D.castV e (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) := (p.T.z_lev P.r le_rfl).symm
  obtain ⟨hGV, ⟨u, hu, hb⟩, hD, hGf⟩ := orbit_gen (p.T.bs P.r) p.T.base e hz Z μ hZ hμGV x hx ξ hξ _ rfl
  refine ⟨_, hGV, hG, u, hu, hb, ?_, ?_⟩
  · rw [hD]
    rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM e _ _ _ P.r (by omega) (by omega), Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r)]
    have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice P.k P.r (P.r - P.r) 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
    unfold U.DjU
    rw [e0]
  · rw [hGf, gf_castM e]
    have hz0 := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
    have hz0' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
    have hG0 := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r) _ _ hz0 hz0' 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG0
    obtain ⟨hl1, hl2⟩ := lowV_top p e
    rw [hG0, hl1, hl2]

end Formalism.FourierDecayAlt.P.CutEXPbSupp
