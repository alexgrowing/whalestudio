import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section dom

theorem orbJ_domL : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∃ (θ : B.SS k r → ℝ) (maj : B.SS k r → ℝ), D.IsNormCut Bs γ (D.muR Bs γ w) θ ∧
      (∀ p : B.SS k r, θ p = θ (p.1, 0)) ∧ (∀ p : B.SS k r, Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → 0 < θ p) ∧
      Integrable maj Bs.μSS ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
        (∀ p, Bs.inSS p → ‖F (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
        ∀ᵐ p ∂Bs.μSS, θ p * ‖F (B.sgs p γ)‖ ≤ cF * maj p := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  refine ⟨16 * ((c₁ : ℝ) + 1), ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hA
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN
  set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc
  set M : ℝ := A / c - 2 * bN with hM
  have hmono : C2.IsMonomial (Zhat k r Bs.z Bs.z' γ) := ⟨w, d, hd, hZ⟩
  obtain ⟨CP, hCP, -⟩ := hPP k r Bs.z Bs.z' γ (P.Dx2.Rad.std Bs) ⟨hγ, hpos⟩ hmono
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  have hnn0 : 0 ≤ nn := by positivity
  have hrn : 0 ≤ (r : ℝ) * nn := by positivity
  have hbN0 : 0 ≤ bN := by positivity
  have hccast : (c : ℝ) = ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 := by rw [hc]; push_cast; ring
  have hAc : 16 * ((r : ℝ) * nn + 1) ≤ A / c := by
    rw [le_div_iff₀ hcpos, hccast]
    calc 16 * ((r : ℝ) * nn + 1) * (((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2)
        = 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * nn + 1) := by ring
      _ ≤ A := hA
  have hA4 : 4 * bN ≤ A / c := by rw [hbN]; linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Bs.k_pos
  have hMR : 2 * ((r : ℝ) + 1) ^ 2 < M := by
    have hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1 := by
      rw [hnn]; push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
        (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]
    rw [hM, hbN]; nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hG : P.Dx2.Rad.Good Bs γ w d := ⟨P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ, P.Dx2.Rad.u_inj Bs hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good Bs hγ hd hG
  have := P.Dx2.OrbJ.sigmaF hR
  have hI := Dx3.intR Bs hγ hd hG hMR
  set μR := D.muR Bs γ w with hμR
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    simpa using (P.unitary_group_closed k r).one_mem
  have hcR : 0 < cR := by
    have := Dx3.om_pos hR hM0 hI hone
    simpa [Dx3.Om] using this
  obtain ⟨KW, hKW1, hKW⟩ := Dx3.UW_bound Bs.z Bs.z_mem Bs.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := Dx3.UW_bound Bs.z' Bs.z'_mem Bs.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  set K0 := K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hK0
  refine ⟨Dx3.cut μR M, fun p => K0 * (B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-(A / c - 3 * bN)) *
      B.gN (Matrix.of p.2.2 : B.Mat k r) ^ (-bN)),
    ⟨Dx3.cut_meas M, Dx3.cut_nonneg μR M, fun p hp => Dx3.cut_norm hR hM0 hI p hp.2.1⟩, fun _ => rfl,
    fun p hp => div_pos (Real.rpow_pos_of_pos (by linarith [P.BetaSesquilinearity.gN_ge_one hp.1]) _) (Dx3.om_pos hR hM0 hI hp.1),
    (Dx3.maj_int Bs (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul K0, ?_⟩
  intro F cF hcF hFb
  filter_upwards [P.Dx2.OrbJ.ae_inSS Bs] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := Dx3.geom Bs hγ hpos hCP hmono h2 h4
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem Bs ⟨h1, h2, h3, h4⟩ hγ
  have hGg : 0 < B.gN (B.sgs p γ) := by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]
  have hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ) := by
    have hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h1.1
    have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
    have e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 =
        (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹ := by
      simp only [B.sgs, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    rw [e]
    calc B.gN ((Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹)
        ≤ B.gN (Matrix.of p.1.1 : B.Mat k r) * B.gN (B.sgs p γ) * B.gN (Matrix.of p.2.1 : B.Mat k r)⁻¹ :=
          (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (P.B6.gN_mul_le _ _) (P.B6.gN_nonneg _))
      _ ≤ KW * B.gN (B.sgs p γ) * KW' := by
          have a1 := hKW _ h1
          have a2 := hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
          have s0 := P.B6.gN_nonneg (B.sgs p γ)
          exact mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _)
            (mul_nonneg (by linarith) s0)
      _ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring
  have hθ : Dx3.cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := Dx3.om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold Dx3.cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / Dx3.Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := Dx3.cut_nonneg μR M p
  have hFv : ‖F (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) := hFb p ⟨h1, h2, h3, h4⟩
  have hCP0 : 0 < CP := by
    by_contra hle'
    have hle := not_lt.mp hle'
    have := mul_nonpos_of_nonpos_of_nonneg hle
      (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) (c₁ * (r + 1) ^ 2))
    linarith
  have hec : c₁ * (r + 1) ^ 2 ≤ c := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hXY' : X ≤ CP * B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ^ c :=
    hXY.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hec) hCP0.le)
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  have hkey := Dx3.key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR
    hcF hCP0 hK10 hKγ0 hM hbN0 hA4
  refine hkey.trans (le_of_eq ?_)
  rw [hK0]
  ring

end dom

section fub

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def lint (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (θL : Mt k r × Mt k r → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (x : Mt k r × Mt k r) : Wq →L[ℂ] Wp :=
  (((θL x : ℝ) : ℂ) * psi k r Bs.z cStd (Matrix.of x.2)) •
    (Bs.π (Matrix.of x.1)).comp (PBG.Kr Bs F ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ))

def rint (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) (y : Mt k r × Mt k r) :
    Wq →L[ℂ] Wp :=
  star (psi k r Bs.z' cStd (Matrix.of y.2)) • (F (x * Matrix.of y.2 * Matrix.of y.1)).comp (Bs.π' (Matrix.of y.1)⁻¹)

theorem star_exp_I (x : ℝ) : star (Complex.exp (Complex.I * (x : ℂ))) = Complex.exp (-(Complex.I * (x : ℂ))) := by
  change (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) = _
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem xi11 (Bs : B.RealPlaceData k r Wp Wq) (p : B.SS k r) :
    B.xiTau Bs (1, 1) p = psi k r Bs.z cStd (Matrix.of p.1.2) * star (psi k r Bs.z' cStd (Matrix.of p.2.2)) := by
  unfold B.xiTau psi
  rw [star_exp_I, ← Complex.exp_add]
  congr 1
  simp only [B.lam, one_mul]
  push_cast
  ring

theorem orb_split_pt (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (θ : B.SS k r → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (x y : Mt k r × Mt k r) :
    θ (x, y) • D.orbIntegrand Bs γ F (x, y) =
      (((θ (x, y) : ℝ) : ℂ) * psi k r Bs.z cStd (Matrix.of x.2)) •
        (Bs.π (Matrix.of x.1)).comp (rint Bs F ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) y) := by
  unfold D.orbIntegrand B.rho rint
  rw [xi11, ContinuousLinearMap.comp_smul, smul_smul, ← Complex.coe_smul, smul_smul, mul_assoc]
  rfl

theorem fub [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (θ : B.SS k r → ℝ) (hθ : ∀ p : B.SS k r, θ p = θ (p.1, 0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hI : Integrable (fun p => θ p • D.orbIntegrand Bs γ F p) Bs.μSS)
    (hR : ∀ᵐ x ∂(Bs.μW.prod Bs.μN),
      Integrable (rint Bs F ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ)) (Bs.μW'.prod Bs.μN)) :
    Integrable (lint Bs γ (fun x => θ (x, 0)) F) (Bs.μW.prod Bs.μN) ∧
      ∫ p, θ p • D.orbIntegrand Bs γ F p ∂Bs.μSS = ∫ x, lint Bs γ (fun x => θ (x, 0)) F x ∂(Bs.μW.prod Bs.μN) := by
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW'
  have hI' : Integrable (fun p => θ p • D.orbIntegrand Bs γ F p) ((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)) := hI
  have hinner : ∀ᵐ x ∂(Bs.μW.prod Bs.μN),
      ∫ y, θ (x, y) • D.orbIntegrand Bs γ F (x, y) ∂(Bs.μW'.prod Bs.μN) = lint Bs γ (fun x => θ (x, 0)) F x := by
    filter_upwards [hR] with x hx
    simp_rw [orb_split_pt Bs γ θ F x]
    rw [show (fun y => (((θ (x, y) : ℝ) : ℂ) * psi k r Bs.z cStd (Matrix.of x.2)) •
        (Bs.π (Matrix.of x.1)).comp (rint Bs F ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) y)) =
        fun y => (((θ (x, 0) : ℝ) : ℂ) * psi k r Bs.z cStd (Matrix.of x.2)) •
          (ContinuousLinearMap.compL ℂ Wq Wp Wp (Bs.π (Matrix.of x.1)))
            (rint Bs F ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ) y) by
      funext y; rw [hθ (x, y)]; rfl]
    rw [integral_smul, ContinuousLinearMap.integral_comp_comm _ hx]
    rfl
  have hint := hI'.integral_prod_left
  refine ⟨hint.congr hinner, ?_⟩
  rw [show Bs.μSS = (Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN) from rfl, integral_prod _ hI']
  exact integral_congr_ae hinner

end fub

section inner

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem continuous_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous fun n : Mt k r => psi k r z c (Matrix.of n) := by
  unfold psi ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (continuous_finset_sum _ fun a _ => ?_)))))
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · simp only [Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun j _ => by
      show Continuous fun n : Mt k r => n (eI k r a) j * z j
      fun_prop

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : B.Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_rint (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r)
    (y : Mt k r × Mt k r) (hy : Matrix.of y.1 ∈ UWset k r Bs.z') :
    ‖rint Bs F x y‖ ≤ ‖F (x * Matrix.of y.2 * Matrix.of y.1)‖ := by
  unfold rint
  rw [norm_smul, norm_star, norm_psi, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖Bs.π' (Matrix.of y.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      rw [Bs.π'_unitary _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hy), one_mul]
  calc ‖F (x * Matrix.of y.2 * Matrix.of y.1)‖ * ‖Bs.π' (Matrix.of y.1)⁻¹‖
      ≤ ‖F (x * Matrix.of y.2 * Matrix.of y.1)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = _ := mul_one _

theorem rint_aesm (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (x : B.Mat k r) (hx : x ∈ B.GV k r)
    (hF : ContinuousOn F (B.GV k r)) :
    AEStronglyMeasurable (rint Bs F x) (Bs.μW'.prod Bs.μN) := by
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW'
  set S : Set (Mt k r × Mt k r) := {y | (Matrix.of y.1 : B.Mat k r) ∈ UWset k r Bs.z' ∧ (Matrix.of y.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r}
    with hS
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := (hWc'.preimage continuous_fst).inter (hNc.preimage continuous_snd)
  have hinv : ContinuousOn (fun y : Mt k r × Mt k r => (Matrix.of y.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp continuous_fst.continuousOn (fun y hy => hy.1.1)
  have hπ' : ContinuousOn (fun y : Mt k r × Mt k r => Bs.π' (Matrix.of y.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv (fun y hy => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hy.1)
  have hm : ContinuousOn (fun y : Mt k r × Mt k r => x * Matrix.of y.2 * Matrix.of y.1) S :=
    ((continuousOn_const.mul continuous_snd.continuousOn).mul continuous_fst.continuousOn)
  have hmem : ∀ y ∈ S, x * Matrix.of y.2 * Matrix.of y.1 ∈ B.GV k r := fun y hy =>
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hx hy.2.1) hy.1.1
  have hFc : ContinuousOn (fun y : Mt k r × Mt k r => F (x * Matrix.of y.2 * Matrix.of y.1)) S := hF.comp hm hmem
  have hψ : Continuous fun y : Mt k r × Mt k r => star (psi k r Bs.z' cStd (Matrix.of y.2)) :=
    continuous_star.comp ((continuous_psi Bs.z' cStd).comp continuous_snd)
  have hcont : ContinuousOn (rint Bs F x) S := by
    unfold rint
    exact hψ.continuousOn.smul (hFc.clm_comp hπ')
  have h1 := hcont.aestronglyMeasurable (μ := Bs.μW'.prod Bs.μN) hSc.measurableSet
  have hae : ∀ᵐ y ∂(Bs.μW'.prod Bs.μN), y ∈ S := by
    have a1 : ∀ᵐ y ∂(Bs.μW'.prod Bs.μN), (Matrix.of y.1 : B.Mat k r) ∈ UWset k r Bs.z' :=
      Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW')
    have a2 : ∀ᵐ y ∂(Bs.μW'.prod Bs.μN), (Matrix.of y.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
    filter_upwards [a1, a2] with y h1 h2 using ⟨h1, h2⟩
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

theorem inner_int (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (hγ : γ ∈ B.GV k r) (θ : B.SS k r → ℝ)
    (hθ : ∀ p : B.SS k r, θ p = θ (p.1, 0)) (hθp : ∀ p : B.SS k r, Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r → 0 < θ p)
    (maj : B.SS k r → ℝ) (hmaj : Integrable maj Bs.μSS) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (cF : ℝ)
    (hF : ContinuousOn F (B.GV k r)) (hb : ∀ᵐ p ∂Bs.μSS, θ p * ‖F (B.sgs p γ)‖ ≤ cF * maj p) :
    ∀ᵐ x ∂(Bs.μW.prod Bs.μN),
      Integrable (rint Bs F ((Matrix.of x.1)⁻¹ * (Matrix.of x.2)⁻¹ * γ)) (Bs.μW'.prod Bs.μN) := by
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarN
  haveI := Formalism.FourierDecayAlt.P.B6.haar_sigmaFinite Bs.haarW'
  have hmaj' : Integrable maj ((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)) := hmaj
  have hb' : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), θ p * ‖F (B.sgs p γ)‖ ≤ cF * maj p := hb
  have hW' : ∀ᵐ p ∂((Bs.μW.prod Bs.μN).prod (Bs.μW'.prod Bs.μN)), (Matrix.of p.2.1 : B.Mat k r) ∈ UWset k r Bs.z' :=
    Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS Bs |>.mono fun p hp => hp.2.2.1
  have hxW : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z ∧
      (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
    have a1 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.1 : B.Mat k r) ∈ UWset k r Bs.z :=
      Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarW)
    have a2 : ∀ᵐ x ∂(Bs.μW.prod Bs.μN), (Matrix.of x.2 : B.Mat k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B6.haar_ae Bs.haarN)
    filter_upwards [a1, a2] with x h1 h2 using ⟨h1, h2⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hb', Measure.ae_ae_of_ae_prod hW', hmaj'.prod_right_ae, hxW]
    with x hbx hWx hmx hx
  have hθx : 0 < θ (x, 0) := hθp (x, 0) hx.2
  have hx0 : (Matrix.of x.1 : B.Mat k r)⁻¹ * (Matrix.of x.2)⁻¹ * γ ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hx.1.1)
      (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hx.2.1)) hγ
  refine Integrable.mono' (hmx.const_mul (cF / θ (x, 0))) (rint_aesm Bs _ hx0 hF) ?_
  filter_upwards [hbx, hWx] with y hby hwy
  refine (norm_rint Bs F _ y hwy).trans ?_
  rw [hθ (x, y)] at hby
  rw [div_mul_eq_mul_div, le_div_iff₀ hθx, mul_comm]
  exact hby

end inner

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
