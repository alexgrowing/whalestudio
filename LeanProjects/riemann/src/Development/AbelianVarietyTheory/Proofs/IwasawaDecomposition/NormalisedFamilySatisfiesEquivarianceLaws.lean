import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatumStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOThZeroTriv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MovedVacuumMemThetaFunctionsAndMoves
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaMove.Moved

namespace GlobalTheory.Mem.NatEqui

variable {D : D7}

theorem chi_smulLat {χ : IdE D → ℂ} (hχ : IsChi D χ) {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
      χ (detId D (stdL D n) (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)) =
        (∏ τ : D.what₂.Tau, (embT D τ (γ : Matrix (Fin n) (Fin n) D.host.E).det)⁻¹) * χ (detId D (stdL D n) L) := by
  letI := D.host.cmStar
  intro γ
  have hst : ∀ x : D.host.E, star x = D.host.conj x := GlobalTheory.NormSum.AdLattice.star_eq_conj D
  let z : unitary D.host.E := ⟨_, Matrix.det_of_mem_unitary γ.2⟩
  rw [GlobalTheory.Mem.Col2.ChiFacLaw.detId_image D (stdL D n) L (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)
    (γ : Matrix (Fin n) (Fin n) D.host.E)
    (star (γ : Matrix (Fin n) (Fin n) D.host.E)) γ.2.2 (fun x hx => ⟨x, hx, rfl⟩) ?_,
    hχ.1 _ _ (GlobalTheory.Mem.Col2.ChiFacLaw.norm_one_span D z.1 (by rw [← hst]; exact z.2.2))
      (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (sd_stdL D n) hL hL).1, hχ.2 z]
  rintro _ ⟨y, hy, rfl⟩
  change (star (γ : Matrix (Fin n) (Fin n) D.host.E)).mulVec ((γ : Matrix (Fin n) (Fin n) D.host.E).mulVec y) ∈ L
  rwa [Matrix.mulVec_mulVec, γ.2.1, Matrix.one_mulVec]

theorem sd_smulLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, SD D (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L) := by
  intro γ
  obtain ⟨g, hg⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D n L hL
  obtain ⟨γA, hγ⟩ := GlobalTheory.TrueTheta.exists_rat γ
  exact GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.TrueTheta.moves_smulLat hγ hg)

theorem chiFac_ne_zero {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L'} (h : SD D L) (h' : SD D L') :
    Base.chiFac χ N N' L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N) h))
    (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N') h'))

theorem chiFac_right {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} (L) {L' L''} (h' : SD D L') (h'' : SD D L'') :
    Base.chiFac χ N N' L L'' = χ (detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N') h' h'', mul_zpow]
  ring

theorem chiFac_left {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L₁} (L') (h : SD D L) (h₁ : SD D L₁) :
    Base.chiFac χ N N' L₁ L' = χ (detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N) h h₁, mul_zpow]
  ring

theorem eqP : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  intro D cc δ B χ hc hδ hχ
  letI := D.host.cmStar
  have hC : Crv D cc δ := ⟨hc, hδ⟩
  obtain ⟨χ', e, hχ', hv, q1, q2, q3⟩ := GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum D cc δ hC
  have key : ∀ N N', Even N → Even N' → ∃ a : ℂ, ∀ L L', SD D L → SD D L' → B.eNat χ N N' L L' =
      fun z => (a * (Base.chiFac χ N N' L L' / Base.chiFac χ' N N' L L')) * e N N' L L' z := by
    intro N N' hN hN'
    have s := sd_stdL D N
    have s' := sd_stdL D N'
    obtain ⟨v1, v2, -⟩ := hv N N' _ _ ⟨hN, hN', s, s'⟩
    obtain ⟨a, ha⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N' _
      (Or.inr ⟨_, _, s, s', rfl⟩)).1 _
      (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ B hC) N N') _ v1 v2
    refine ⟨a, fun L L' h h' => funext fun z => ?_⟩
    have e3 := q3 N N' ⟨_, s⟩ ⟨L, h⟩ ⟨_, s'⟩ hN hN'
    have e2 := congrFun (q2 N N' ⟨L, h⟩ ⟨_, s'⟩ ⟨L', h'⟩ hN hN') z
    dsimp only at e2 e3
    rw [e3, iop_mul, ← mul_assoc, mul_comm (χ' _ ^ _)] at e2
    have hh : B.thHalf N N' L = fun w => a * Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) (stdL D N'))
        (La D (tor0 D cc δ) L (stdL D N')) (e N N' (stdL D N) (stdL D N')) w := by
      funext w
      rw [Base.thHalf, ha]
      exact iop_mul D _ _ _ a _ w
    have h0 := chiFac_ne_zero hχ' h h'
    change Base.chiFac χ N N' L L' * B.thMoved N N' L L' z = _
    rw [Base.thMoved, hh, iop_mul, e2]
    change _ = a * (_ / Base.chiFac χ' N N' L L') * (Base.chiFac χ' N N' L L' * _)
    field_simp
  refine ⟨fun N N' L L' hN hN' γ γ' => ?_, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ'), ← q1 N N' L L' hN hN' γ γ']
    have h1 := chiFac_ne_zero hχ' (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ')
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    funext z
    change _ * pull D _ _ _ (e N N' L.1 L'.1) z = _
    congr 2
    rw [div_eq_div_iff h0 h1]
    unfold Base.chiFac
    rw [chi_smulLat hχ L.2, chi_smulLat hχ L'.2, chi_smulLat hχ' L.2, chi_smulLat hχ' L'.2]
    simp only [mul_zpow]
    ring
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L.2 L''.2, q2 N N' L L' L'' hN hN']
    funext z
    have h1 := zpow_ne_zero (-((N / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L'.2 L''.2)
    rw [iop_mul, chiFac_right hχ _ L'.2 L''.2, chiFac_right hχ' _ L'.2 L''.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L₁.2 L'.2, q3 N N' L L₁ L' hN hN']
    funext z
    have h1 := zpow_ne_zero (((N' / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L.2 L₁.2)
    rw [iop_mul, chiFac_left hχ _ L.2 L₁.2, chiFac_left hχ' _ L.2 L₁.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp

end GlobalTheory.Mem.NatEqui
