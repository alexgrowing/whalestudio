import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces

open Matrix MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section orbit

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem integrand_aesm' (Bs : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} {U : Set (B.Mat k r)}
    (hU : ∀ p, Bs.inSS p → B.sgs p γ ∈ U)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F U) :
    AEStronglyMeasurable (D.orbIntegrand Bs γ F) Bs.μSS := by
  set S : Set (B.SS k r) := {p | Bs.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r Bs.z).closed
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau Bs (1, 1) p :=
    (P.B7.continuous_xi Bs).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => Bs.π (Matrix.of p.1.1)) S :=
    Bs.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => Bs.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have hsgs : ContinuousOn (fun p : B.SS k r => B.sgs p γ) S :=
    ((((hinv1.mul hinv2).mul continuousOn_const).mul hc4).mul hc5)
  have hFs : ContinuousOn (fun p : B.SS k r => F (B.sgs p γ)) S :=
    hF.comp hsgs (fun p hp => hU p hp)
  have hcont : ContinuousOn (D.orbIntegrand Bs γ F) S := by
    unfold D.orbIntegrand B.rho
    exact hxi.continuousOn.smul (hπ.clm_comp (hFs.clm_comp hπ'))
  have h1 := hcont.aestronglyMeasurable (μ := Bs.μSS) hSc.measurableSet
  have hae : ∀ᵐ p ∂Bs.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS Bs
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h1

end orbit

theorem orbJ_dom : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∃ (θ : B.SS k r → ℝ) (maj : B.SS k r → ℝ), D.IsNormCut Bs γ (D.muR Bs γ w) θ ∧ Integrable maj Bs.μSS ∧
      ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
        (∀ p, Bs.inSS p → ‖F (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
        ∀ᵐ p ∂Bs.μSS, ‖θ p • D.orbIntegrand Bs γ F p‖ ≤ cF * maj p := by
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
    ⟨Dx3.cut_meas M, Dx3.cut_nonneg μR M, fun p hp => Dx3.cut_norm hR hM0 hI p hp.2.1⟩,
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
  have hFv : ‖B.rho Bs p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) :=
    (P.B7.norm_rho_le Bs ⟨h1, h2, h3, h4⟩ F γ).trans (hFb p ⟨h1, h2, h3, h4⟩)
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
  rw [norm_smul, Real.norm_of_nonneg hθ0]
  unfold D.orbIntegrand
  rw [norm_smul, P.B7.norm_xi, one_mul]
  refine hkey.trans (le_of_eq ?_)
  rw [hK0]
  ring

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem orbJ_tendsto : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H : ℕ → B.Mat k r → (Wq →L[ℂ] Wp)) (H₀ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      (∀ n, AEStronglyMeasurable (D.orbIntegrand Bs γ (H n)) Bs.μSS) →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₀) Bs.μSS →
      (∀ n p, Bs.inSS p → ‖H n (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₀ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → Tendsto (fun n => H n (B.sgs p γ)) atTop (𝓝 (H₀ (B.sgs p γ)))) →
      Tendsto (fun n => D.orbJ Bs γ (D.muR Bs γ w) (H n)) atTop (𝓝 (D.orbJ Bs γ (D.muR Bs γ w) H₀)) := by
  obtain ⟨c₃, hc₃⟩ := orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H H₀ cF hcF hm hm₀ hb hb₀ hlim
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : P.Dx2.Rad.Good Bs γ w d := ⟨P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ, P.Dx2.Rad.u_inj Bs hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G hGm hGb =>
    Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G cF hcF hGb)
  have hEq : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G hGm hGb⟩
    unfold D.orbJ
    rw [dif_pos hex]
    exact P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G hGm hGb)
  have e1 : (fun n => D.orbJ Bs γ (D.muR Bs γ w) (H n)) =
      fun n => ∫ p, θ p • D.orbIntegrand Bs γ (H n) p ∂Bs.μSS := funext fun n => hEq _ (hm n) (hb n)
  rw [e1, hEq _ hm₀ hb₀]
  refine tendsto_integral_of_dominated_convergence (fun p => cF * maj p)
    (fun n => hθ.1.aestronglyMeasurable.smul (hm n)) (hmaj.const_mul cF) (fun n => hdom (H n) cF hcF (hb n)) ?_
  filter_upwards [P.Dx2.OrbJ.ae_inSS Bs] with p hp
  have hc : Continuous (fun X : Wq →L[ℂ] Wp => θ p • (B.xiTau Bs (1, 1) p •
      (Bs.π (Matrix.of p.1.1)).comp (X.comp (Bs.π' (Matrix.of p.2.1)⁻¹)))) :=
    ((continuous_const.clm_comp (continuous_id.clm_comp continuous_const)).const_smul (B.xiTau Bs (1, 1) p)).const_smul (θ p)
  exact (hc.tendsto _).comp (hlim p hp)

theorem vecV_tendsto : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H : ℕ → B.Mat k r → (Wq →L[ℂ] Wp)) (H₀ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      (∀ n, ContinuousOn (H n) (B.GPos Bs)) → ContinuousOn H₀ (B.GPos Bs) →
      (∀ n, ∀ g ∈ B.GPos Bs, ‖H n g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₀ g‖ ≤ cF * B.gN g ^ (-A)) →
      (∀ g ∈ B.GPos Bs, Tendsto (fun n => H n g) atTop (𝓝 (H₀ g))) →
      Tendsto (fun n => D.vecV Bs ν' m₀ (H n) q) atTop (𝓝 (D.vecV Bs ν' m₀ H₀ q)) := by
  obtain ⟨c₃, hc₃⟩ := orbJ_tendsto
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H H₀ cF hcF hc hc₀ hb hb₀ hlim
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨P.B7.sgs_mem Bs hp hγ, by rw [P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H H₀ cF hcF
        (fun n => integrand_aesm' Bs horb (hc n)) (integrand_aesm' Bs horb hc₀)
        (fun n p hp => hb n _ (horb p hp)) (fun p hp => hb₀ _ (horb p hp)) (fun p hp => hlim _ (horb p hp))
    · simp only [dif_neg h']
      exact tendsto_const_nhds
  · simp only [dif_neg h]
    exact tendsto_const_nhds

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lin

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_subGV (v : List (B.Mat k r)) (hv : ∀ X ∈ v, B.inLie k r X) {f h : B.Mat k r → E}
    (hf : B.CkOn ((v.length : ℕ) : ℕ∞) (B.GV k r) f) (hh : B.CkOn ((v.length : ℕ) : ℕ∞) (B.GV k r) h) :
    ∀ g ∈ B.GV k r, B.Rw v (f - h) g = B.Rw v f g - B.Rw v h g := by
  intro g hg
  have hl : (B4.lr ([] : List (B.Mat k r)) v).length = v.length := by simp [B4.lr]
  have hAL : B4.AllLie (B4.lr ([] : List (B.Mat k r)) v) := by
    intro x hx
    simp only [B4.lr, List.map_nil, List.nil_append, List.mem_map] at hx
    obtain ⟨X, hX, rfl⟩ := hx
    exact hv X hX
  have e : ∀ F : B.Mat k r → E, B.Rw v F = B4.W (B4.lr ([] : List (B.Mat k r)) v) F := fun F => by
    rw [← B4.dLR_eq]; rfl
  rw [e, e, e]
  exact B4.W_sub _ hAL (by rw [hl]; exact hf) (by rw [hl]; exact hh) g hg

end lin

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_subGV (Θ : B.DiffOp k r Wp Wq) {o : ℕ} (ho : ∀ T ∈ Θ, T.word.length ≤ o)
    {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h₁ : B.CkOn (o : ℕ∞) (B.GV k r) F₁) (h₂ : B.CkOn (o : ℕ∞) (B.GV k r) F₂) :
    ∀ g ∈ B.GV k r, B.opApply Θ (F₁ - F₂) g = B.opApply Θ F₁ g - B.opApply Θ F₂ g := by
  intro g hg
  induction Θ with
  | nil => simp [B.opApply]
  | cons T Θ ih =>
    have e : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp),
        B.opApply (T :: Θ) F g = T.coef g (B.Rw T.word F g) + B.opApply Θ F g := fun F => by simp [B.opApply]
    rw [e, e, e, ih (fun T' hT' => ho T' (by simp [hT']))]
    have hl : ((T.word.length : ℕ) : ℕ∞) ≤ (o : ℕ∞) := by exact_mod_cast ho T (by simp)
    rw [rw_subGV T.word T.word_lie (P.B5.ckOn_mono hl h₁) (P.B5.ckOn_mono hl h₂) g hg, map_sub]
    abel

theorem opApply_continuousOn (Θ : B.DiffOp k r Wp Wq) {U : Set (B.Mat k r)} {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ T ∈ Θ, ContinuousOn (fun g => T.coef g (B.Rw T.word F g)) U) :
    ContinuousOn (B.opApply Θ F) U := by
  induction Θ with
  | nil =>
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact continuousOn_const
  | cons T Θ ih =>
    have e : B.opApply (T :: Θ) F = fun g => T.coef g (B.Rw T.word F g) + B.opApply Θ F g := by
      funext g; simp [B.opApply]
    rw [e]
    exact (h T (by simp)).add (ih fun T' hT' => h T' (by simp [hT']))

theorem opApply_bound (Bs : B.RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound Bs (fib j)) {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq} (hΘ : C6.InDDPlus Bs fib ∅ o κ Θ)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o G b →
      ∀ g ∈ B.GV k r, ε₀ ≤ Gf k r Bs.z Bs.z' g →
        ‖B.opApply Θ G g‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) := by

  have hterm : ∀ T ∈ Θ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o G b →
      ∀ g ∈ B.GV k r, ε₀ ≤ Gf k r Bs.z Bs.z' g →
        ‖T.coef g (B.Rw T.word G g)‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) := by
    intro T hT
    obtain ⟨Pp, a, bb, c, es, hP, hab, hlen, hlie, hco⟩ := hΘ.2.2 T hT
    set S : Set (B.Mat k r) := {g | g ∈ B.GV k r ∧ ε₀ ≤ Gf k r Bs.z Bs.z' g} with hSdef
    set c₀ : ℝ := min ε₀ (ε₀ ^ 2) with hc₀
    have hc₀p : 0 < c₀ := lt_min hε₀ (by positivity)
    have hSD : ∀ g ∈ S, ∀ l, (l ∈ (∅ : Finset (Fin (r + 2))) ∨ l = Fin.last (r + 1)) →
        c₀ ≤ Complex.normSq (Dmin k r Bs.z Bs.z' g l) := by
      intro g hg l hl
      rcases hl with hl | rfl
      · simp at hl
      · have := Formalism.FourierDecayAlt.P.gram_function_last_minor k r Bs.z Bs.z' Bs.T_pos.le Bs.T'_pos.le g ε₀ hg.2
        exact (min_le_left _ _).trans this
    have hSGf : ∀ g ∈ S, c₀ ≤ Complex.normSq ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ) := by
      intro g hg
      rw [Complex.normSq_ofReal]
      have h1 := hg.2
      have : ε₀ ^ 2 ≤ Gf k r Bs.z Bs.z' g * Gf k r Bs.z Bs.z' g := by nlinarith
      exact (min_le_right _ _).trans this
    have hcU := P.AdmissibleLieWords.ubl_coefP Bs fib hfib ∅ Pp a bb c es hP hab hlie hε₀ (fun g hg => hg) hc₀p hSD hSGf 0
    obtain ⟨⟨Cc, hCc0, hUB⟩, -⟩ := hcU
    set fo := (es.map fun e => e.2.length).sum with hfo
    set cw : ℝ := (T.word.map P.BetaSesquilinearity.nz).prod with hcw
    have hcw0 : 0 ≤ cw := List.prod_nonneg fun x hx => by
      obtain ⟨X, _, rfl⟩ := List.mem_map.1 hx; exact (P.BetaSesquilinearity.nz_pos X).le
    refine ⟨Cc * cw, mul_nonneg hCc0 hcw0, fun G A b hG g hg hgε => ?_⟩
    have hgS : g ∈ S := ⟨hg, hgε⟩
    have hgp := P.BetaSesquilinearity.gN_pos hg
    have hg1 := P.BetaSesquilinearity.gN_ge_one hg

    have hAdm0 : PI.UnitaryCorollaryDerivatives.CRH.admitted (k := k) (r := r) 0 [] := ⟨[], [], by simp, by simp, by simp, by simp [P.BetaSesquilinearity.wL, P.BetaSesquilinearity.wR]⟩
    have hc1 : ‖T.coef g‖ ≤ Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0) := by
      have h := hUB [] hAdm0 g hgS
      have e : P.BetaSesquilinearity.Dw [] (fun g => (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g) g =
          (Pp g * C6.monoM Bs a bb c g) • C6.Epart fib es g := rfl
      rw [e] at h
      rw [hco g ⟨hg, lt_of_lt_of_le hε₀ hgε, fun l hl => by simp at hl⟩]
      simpa using h

    have hc2 : ‖B.Rw T.word G g‖ ≤ cw * (b * B.gN g ^ (-A)) := by
      rw [P.BetaSesquilinearity.Rw_scale]
      simp only
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcw0]
      apply mul_le_mul_of_nonneg_left _ hcw0
      have hunit : ∀ X ∈ T.word.map P.BetaSesquilinearity.nrm, B.unitLie k r X := fun X hX => by
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX; exact P.BetaSesquilinearity.nrm_unit (T.word_lie Y hY)
      have h := hG.2 [] (T.word.map P.BetaSesquilinearity.nrm) (by simp) hunit (by simp; omega) g hg
      have e : B.dLR [] (T.word.map P.BetaSesquilinearity.nrm) G g = B.Rw (T.word.map P.BetaSesquilinearity.nrm) G g := rfl
      rw [e] at h
      have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos hgp _
      rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ hpw, mul_comm]
      exact h
    have hfo' : fo ≤ o := by omega
    calc ‖T.coef g (B.Rw T.word G g)‖ ≤ ‖T.coef g‖ * ‖B.Rw T.word G g‖ := (T.coef g).le_opNorm _
      _ ≤ (Cc * B.gN g ^ (κ + 3 * (r + 1) * fo + 3 * (r + 1) * 0)) * (cw * (b * B.gN g ^ (-A))) :=
          mul_le_mul hc1 hc2 (norm_nonneg _) (mul_nonneg hCc0 (by positivity))
      _ = Cc * cw * b * (B.gN g ^ (((κ + 3 * (r + 1) * fo : ℕ) : ℝ)) * B.gN g ^ (-A)) := by
          rw [Real.rpow_natCast]; ring_nf
      _ = Cc * cw * b * B.gN g ^ (((κ + 3 * (r + 1) * fo : ℕ) : ℝ) - A) := by
          rw [← Real.rpow_add hgp, sub_eq_add_neg]
      _ ≤ Cc * cw * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) := by
          have hb0 : 0 ≤ b := by
            have h := hG.2 [] [] (by simp) (by simp) (by simp) g hg
            exact le_trans (by positivity) h
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le hg1
          have : ((κ + 3 * (r + 1) * fo : ℕ) : ℝ) ≤ (κ : ℝ) + 3 * ((r : ℝ) + 1) * o := by
            have h3 : (3 * (r + 1) * fo : ℕ) ≤ 3 * (r + 1) * o := Nat.mul_le_mul_left _ hfo'
            have h4 : ((3 * (r + 1) * fo : ℕ) : ℝ) ≤ ((3 * (r + 1) * o : ℕ) : ℝ) := by exact_mod_cast h3
            push_cast at h4 ⊢; linarith
          linarith

  have hall : ∀ Θ' : B.DiffOp k r Wp Wq, (∀ T ∈ Θ', T ∈ Θ) → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o G b →
      ∀ g ∈ B.GV k r, ε₀ ≤ Gf k r Bs.z Bs.z' g →
        ‖B.opApply Θ' G g‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) := by
    intro Θ'
    induction Θ' with
    | nil =>
      intro _
      refine ⟨0, le_rfl, fun G A b _ g _ _ => ?_⟩
      simp [B.opApply]
    | cons T Θ' ih =>
      intro hsub
      obtain ⟨K1, hK1, h1⟩ := hterm T (hsub T (by simp))
      obtain ⟨K2, hK2, h2⟩ := ih fun T' hT' => hsub T' (by simp [hT'])
      refine ⟨K1 + K2, add_nonneg hK1 hK2, fun G A b hG g hg hgε => ?_⟩
      have e : B.opApply (T :: Θ') G g = T.coef g (B.Rw T.word G g) + B.opApply Θ' G g := by
        simp [B.opApply]
      rw [e]
      calc ‖T.coef g (B.Rw T.word G g) + B.opApply Θ' G g‖
          ≤ ‖T.coef g (B.Rw T.word G g)‖ + ‖B.opApply Θ' G g‖ := norm_add_le _ _
        _ ≤ K1 * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) +
            K2 * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) := add_le_add (h1 G A b hG g hg hgε) (h2 G A b hG g hg hgε)
        _ = (K1 + K2) * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o - A) := by ring
  exact hall Θ fun T hT => hT

end ops

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section misc

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ckOn_continuousOn' {m : ℕ∞} {UU : Set (B.Mat k r)} (hUU : UU ⊆ B.GV k r) {f : B.Mat k r → E}
    (h : B.CkOn m UU f) : ContinuousOn f UU := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', he⟩ := h g₀ hg₀
  have h1 : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine h1.continuousWithinAt.congr_of_eventuallyEq ?_ (he g₀ hgU (hUU hg₀))
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgUU
  exact he g hgU' (hUU hgUU)

end misc

section cut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem cutF_inCC (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : C6.IsCut0 χ) {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    {A₀ : ℝ} (hfA : ∀ m : ℕ, B.InCC A₀ m f) {ε : ℝ} (hε : 0 < ε) (A : ℝ) (mm : ℕ)
    (hA : A + 2 * ((r : ℝ) + 1) * (mm : ℝ) ≤ A₀) : B.InCC A mm (D.cutF Bs χ f ε) := by
  have e0 : 0 + r = r := Nat.zero_add r
  obtain ⟨_, _, _, h2, _⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.level_zero_estimate (k := k) (ρ := r) (D.castV e0.symm Bs.z)
    (D.castV e0.symm Bs.z') (D.castF e0 f) χ hχ A₀ (fun m => Formalism.FourierDecayAlt.P.JCTx6.Link2.inCC_castF e0 (hfA m)) ε hε
    A mm (by simpa using hA)
  have e1 : (fun g => ((χ (Gf k (0 + r) (D.castV e0.symm Bs.z) (D.castV e0.symm Bs.z') g / ε) : ℝ) : ℂ) •
      D.castF e0 f g) = D.castF e0 (D.cutF Bs χ f ε) := (Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e0 Bs χ f ε).symm
  rw [e1] at h2
  have h3 := Formalism.FourierDecayAlt.P.JCTx6.Link2.inCC_castF e0.symm h2
  rwa [Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self] at h3

theorem vecV_congrGPos (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h : ∀ g ∈ B.GPos Bs, H₁ g = H₂ g) :
    D.vecV Bs ν' m₀ H₁ q = D.vecV Bs ν' m₀ H₂ q := by
  unfold D.vecV
  by_cases hq : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := P.ptG_spec k r Bs.z Bs.z' q h'.choose hq.1 h'.choose_spec.2.1
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ hq.2
      have e := P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq.1.2 ▸ D.ptPerm q)) H₁ H₂ 1 (by
        filter_upwards [P.B5.ae_inSS Bs] with p hp
        simp only [D.orbIntegrand, B.rho, one_smul]
        rw [h _ ⟨P.B7.sgs_mem Bs hp hγ, by rw [P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩])
      rw [e, one_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq]

end cut

theorem thr_arith (r X N Cb' c₃ o κ A : ℝ) (hr : 0 ≤ r) (hX : r + 1 ≤ X) (hN : 0 ≤ N) (hCb : 0 ≤ Cb')
    (ho0 : 0 ≤ o) (ho : o ≤ Cb' * N * X) (hκ0 : 0 ≤ κ) (hκ : κ ≤ Cb' * (r + 1) * o)
    (hA : (5 * Cb' + Cb' ^ 2 + 1 + |c₃|) * (r + 1) ^ 4 * (N * X ^ 2 + X ^ 3) ≤ A) :
    c₃ * (r + 1) ^ 2 * (r * X + 1) ≤ A - 2 * (r + 1) * o - 1 - (κ + 3 * (r + 1) * o) := by
  have hR1 : 1 ≤ r + 1 := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hR4 : r + 1 ≤ (r + 1) ^ 4 := by
    have : (r + 1) ^ 1 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
    simpa using this
  have hR24 : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hX23 : X ^ 2 ≤ X ^ 3 := by nlinarith
  have hrX : r * X + 1 ≤ X ^ 3 := by nlinarith
  have hNX : 0 ≤ N * X := by positivity
  have t1 : 5 * (r + 1) * o ≤ 5 * Cb' * ((r + 1) ^ 4 * (N * X ^ 2)) := by
    have a1 : (r + 1) * o ≤ (r + 1) * (Cb' * N * X) := mul_le_mul_of_nonneg_left ho (by linarith)
    have a2 : (r + 1) * (Cb' * N * X) ≤ (r + 1) ^ 4 * (Cb' * N * X ^ 2) := by
      apply mul_le_mul hR4 _ (by positivity) (by positivity)
      have := mul_le_mul_of_nonneg_left hX2 (mul_nonneg hCb hN)
      nlinarith
    nlinarith
  have t2 : κ ≤ Cb' ^ 2 * ((r + 1) ^ 4 * (N * X ^ 2)) := by
    have a1 : κ ≤ Cb' * (r + 1) * (Cb' * N * X) :=
      hκ.trans (mul_le_mul_of_nonneg_left ho (by positivity))
    have a2 : Cb' * (r + 1) * (Cb' * N * X) = Cb' ^ 2 * ((r + 1) * (N * X)) := by ring
    have a3 : (r + 1) * (N * X) ≤ (r + 1) ^ 4 * (N * X ^ 2) := by
      apply mul_le_mul hR4 (mul_le_mul_of_nonneg_left hX2 hN) hNX (by positivity)
    calc κ ≤ _ := a1
      _ = _ := a2
      _ ≤ Cb' ^ 2 * ((r + 1) ^ 4 * (N * X ^ 2)) := mul_le_mul_of_nonneg_left a3 (by positivity)
  have t3 : (1 : ℝ) ≤ (r + 1) ^ 4 * X ^ 3 := by
    have : (1 : ℝ) ≤ (r + 1) ^ 4 := one_le_pow₀ hR1
    have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX1
    nlinarith
  have t4 : c₃ * (r + 1) ^ 2 * (r * X + 1) ≤ |c₃| * ((r + 1) ^ 4 * X ^ 3) := by
    have a0 : 0 ≤ (r + 1) ^ 2 * (r * X + 1) := by positivity
    calc c₃ * (r + 1) ^ 2 * (r * X + 1) = c₃ * ((r + 1) ^ 2 * (r * X + 1)) := by ring
      _ ≤ |c₃| * ((r + 1) ^ 2 * (r * X + 1)) := mul_le_mul_of_nonneg_right (le_abs_self _) a0
      _ ≤ |c₃| * ((r + 1) ^ 4 * X ^ 3) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hR24 hrX (by positivity) (by positivity)) (abs_nonneg _)
  have hsum : (5 * Cb' + Cb' ^ 2 + 1 + |c₃|) * (r + 1) ^ 4 * (N * X ^ 2 + X ^ 3) =
      5 * Cb' * ((r + 1) ^ 4 * (N * X ^ 2)) + Cb' ^ 2 * ((r + 1) ^ 4 * (N * X ^ 2)) +
      (5 * Cb' + Cb' ^ 2) * ((r + 1) ^ 4 * X ^ 3) + (r + 1) ^ 4 * X ^ 3 + |c₃| * ((r + 1) ^ 4 * X ^ 3) +
      (1 + |c₃|) * ((r + 1) ^ 4 * (N * X ^ 2)) := by ring
  have hpos1 : 0 ≤ (5 * Cb' + Cb' ^ 2) * ((r + 1) ^ 4 * X ^ 3) := by positivity
  have hpos2 : 0 ≤ (1 + |c₃|) * ((r + 1) ^ 4 * (N * X ^ 2)) := by positivity
  nlinarith

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cutoffs

variable {k r : ℕ}

theorem cut_norm_le (R : ℝ) (g : B.Mat k r) : ‖1 - P.JCx2.pdPsi (k := k) (r := r) R g‖ ≤ 1 := by
  simp only [P.JCx2.pdPsi, sub_sub_cancel, P.JCx2.pdPhi, Complex.norm_real, Real.norm_eq_abs, P.JCx2.pdChi]
  rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

theorem cut_tendsto_one (g : B.Mat k r) :
    Tendsto (fun n : ℕ => 1 - P.JCx2.pdPsi (k := k) (r := r) ((n : ℝ) + 1) g) atTop (𝓝 1) := by
  have e : ∀ n : ℕ, 1 - P.JCx2.pdPsi (k := k) (r := r) ((n : ℝ) + 1) g =
      P.JCx2.pdPhi ((1 / ((n : ℝ) + 1)) • g) := by
    intro n; simp [P.JCx2.pdPsi, one_div]
  simp only [e]
  have h0 : (P.JCx2.pdPhi (k := k) (r := r) ∘ fun x : ℝ => x • g) 0 = 1 := by
    simp [P.JCx2.pdPhi, P.JCx2.pdSq, P.JCx2.pd_chi_one]
  have hc : Continuous (P.JCx2.pdPhi (k := k) (r := r) ∘ fun x : ℝ => x • g) :=
    (P.JCx2.pd_phi_cd (k := k) (r := r)).continuous.comp (continuous_id.smul (continuous_const : Continuous fun _ : ℝ => g))
  have key := (hc.tendsto (0 : ℝ)).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [h0] at key
  exact key

end cutoffs

section conv

theorem vecV_cut_empty : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b₀ : ℝ)
    (cut : ℕ → B.Mat k r → ℂ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A → B.CCle A 0 F b₀ →
    B.CkOn ⊤ (B.GV k r) F → (∀ n g, cut n g = 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g) →
    Tendsto (fun n => D.vecV Bs ν' m₀ (fun g => cut n g • F g) q) atTop (𝓝 (D.vecV Bs ν' m₀ F q)) := by
  obtain ⟨c₃, hc₃⟩ := vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q F A b₀ cut hA hb₀ hFck hcut
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hFck
  have hGPG : B.GPos Bs ⊆ B.GV k r := fun g hg => hg.1
  have hb₀0 : 0 ≤ b₀ := P.JCx2.pd_ccle_nonneg hb₀
  have hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ b₀ * B.gN g ^ (-A) := by
    intro g hg
    have h0 := hb₀.2 [] [] (by simp) (by simp) (by simp) g hg
    have hgp := P.BetaSesquilinearity.gN_pos hg
    rw [Real.rpow_neg hgp.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgp _), mul_comm]
    exact h0
  have hcc : ∀ n, Continuous (cut n) := by
    intro n
    have : cut n = fun g => 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g := funext (hcut n)
    rw [this]
    exact continuous_const.sub (P.JCx2.pd_psi_cd _).continuous
  refine hc₃ k r Wp Wq Bs ν' m₀ q A hA (fun n g => cut n g • F g) F b₀ hb₀0
    (fun n => ((hcc n).continuousOn.smul hFc).mono hGPG) (hFc.mono hGPG) (fun n g hg => ?_)
    (fun g hg => hFb g hg.1) (fun g _ => ?_)
  · refine (norm_smul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hFb g hg.1))
    rw [hcut]; exact cut_norm_le _ g
  · have h1 : Tendsto (fun n => cut n g) atTop (𝓝 1) := by
      simp only [hcut]; exact cut_tendsto_one g
    simpa using h1.smul_const (F g)

theorem vecV_cut_op : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (cut : ℕ → B.Mat k r → ℂ) (nf : ℕ) (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq) (o κ : ℕ)
    (Dop : B.DiffOp k r Wp Wq) (ε₀ A₁ bF : ℝ),
    (∀ j, C6.FibBound Bs (fib j)) → C6.InDDPlus Bs fib ∅ o κ Dop → 0 < ε₀ →
    (∀ g, Gf k r Bs.z Bs.z' g < ε₀ → F g = 0) → B.CkOn ⊤ (B.GV k r) F → B.CCle A₁ o F bF →
    (∀ n g, cut n g = 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g) →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      A₁ - 1 - ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o) →
    Tendsto (fun n => D.vecV Bs ν' m₀ (B.opApply Dop (fun g => cut n g • F g)) q) atTop
      (𝓝 (D.vecV Bs ν' m₀ (B.opApply Dop F) q)) := by
  obtain ⟨c₃, hc₃⟩ := vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ _ Bs ν' m₀ q F cut nf fib o κ Dop ε₀ A₁ bF hfib hIn hε₀ hFv hFck hbF hcut hthr
  have hGPG : B.GPos Bs ⊆ B.GV k r := fun g hg => hg.1
  have hGc : Continuous (fun g : B.Mat k r => Gf k r Bs.z Bs.z' g) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
  have hFn : ∀ n : ℕ, (fun g => cut n g • F g) = F - fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g := by
    intro n; funext g; simp only [hcut, Pi.sub_apply, sub_smul, one_smul]
  have hbF0 : 0 ≤ bF := P.JCx2.pd_ccle_nonneg hbF
  obtain ⟨Kp, hKp0, hKp⟩ := P.JCx2.pd_cut_ccle (k := k) (r := r) (E := Wq →L[ℂ] Wp) o
  have hψ : ∀ n : ℕ, B.CCle (A₁ - 1) o (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g)
      (Kp * bF / ((n : ℝ) + 1)) := fun n => hKp _ (by positivity) A₁ F bF hbF
  obtain ⟨K, hK0, hKb⟩ := opApply_bound Bs fib hfib hIn hε₀
  set e₀ : ℝ := (κ : ℝ) + 3 * ((r : ℝ) + 1) * o with he₀
  have hopen : IsOpen {x : B.Mat k r | Gf k r Bs.z Bs.z' x < ε₀} := isOpen_lt hGc continuous_const
  have hbd : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (A' c : ℝ), B.CCle A' o G c →
      (∀ x, Gf k r Bs.z Bs.z' x < ε₀ → G x = 0) →
      ∀ g ∈ B.GPos Bs, ‖B.opApply Dop G g‖ ≤ K * c * B.gN g ^ (e₀ - A') := by
    intro G A' c hG hG0 g hg
    by_cases hgl : Gf k r Bs.z Bs.z' g < ε₀
    · rw [opApply_zero_near Dop hopen (fun x _ hx => hG0 x hx) g hg.1 hgl, norm_zero]
      exact mul_nonneg (mul_nonneg hK0 (P.JCx2.pd_ccle_nonneg hG)) (Real.rpow_nonneg (P.B6.gN_nonneg g) _)
    · exact hKb G A' c hG g hg.1 (not_lt.1 hgl)
  have hψ0 : ∀ (n : ℕ) x, Gf k r Bs.z Bs.z' x < ε₀ → P.JCx2.pdPsi ((n : ℝ) + 1) x • F x = 0 :=
    fun n x hx => by rw [hFv x hx, smul_zero]
  have hlen : ∀ T ∈ Dop, T.word.length ≤ o := by
    intro T hT
    obtain ⟨_, _, _, _, _, _, _, hl, _⟩ := hIn.2.2 T hT
    omega
  have hsplit : ∀ (n : ℕ), ∀ g ∈ B.GV k r, B.opApply Dop (fun g => cut n g • F g) g =
      B.opApply Dop F g - B.opApply Dop (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) g := by
    intro n g hg
    rw [hFn n]
    exact opApply_subGV Dop hlen hbF.1 (hψ n).1 g hg
  have hcont : ∀ G : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) G →
      ContinuousOn (B.opApply Dop G) (B.GPos Bs) := by
    intro G hG
    apply opApply_continuousOn
    intro T hT
    have h1 : ContinuousOn T.coef (B.GPos Bs) :=
      (ckOn_continuousOn' (fun g hg => hg.1) (hIn.1 T hT).1).mono
        (fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
    have h2 : ContinuousOn (B.Rw T.word G) (B.GPos Bs) :=
      (P.B5.ckOn_continuousOn (P.JFxG.ckOn_Rw_top hG T.word T.word_lie)).mono hGPG
    exact h1.clm_apply h2
  have hψck : ∀ n : ℕ, B.CkOn ⊤ (B.GV k r) (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) :=
    fun n => P.JCx2.pd_smooth_smul (P.JCx2.pd_psi_cd _) hFck
  set A' : ℝ := A₁ - 1 - e₀ with hA'
  set cF : ℝ := K * bF * (1 + Kp) with hcF
  have hcF0 : 0 ≤ cF := by positivity
  have hb0 : ∀ g ∈ B.GPos Bs, ‖B.opApply Dop F g‖ ≤ K * bF * B.gN g ^ (-A') := by
    intro g hg
    have hg1 := P.BetaSesquilinearity.gN_ge_one hg.1
    refine (hbd F A₁ bF hbF hFv g hg).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_exponent_le hg1 (by rw [hA']; linarith)
  have hbψ : ∀ (n : ℕ), ∀ g ∈ B.GPos Bs, ‖B.opApply Dop (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) g‖ ≤
      K * Kp * bF * B.gN g ^ (-A') * (1 / ((n : ℝ) + 1)) := by
    intro n g hg
    refine (hbd _ (A₁ - 1) _ (hψ n) (hψ0 n) g hg).trans (le_of_eq ?_)
    have e2 : e₀ - (A₁ - 1) = -A' := by rw [hA']; ring
    rw [e2]
    field_simp
  refine hc₃ k r Wp Wq Bs ν' m₀ q A' hthr
    (fun n => B.opApply Dop (fun g => cut n g • F g)) (B.opApply Dop F) cF hcF0
    (fun n => ((hcont F hFck).sub (hcont _ (hψck n))).congr (fun g hg => hsplit n g hg.1)) (hcont F hFck)
    (fun n g hg => ?_) (fun g hg => ?_) (fun g hg => ?_)
  · have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpw : 0 ≤ B.gN g ^ (-A') := Real.rpow_nonneg (P.B6.gN_nonneg g) _
    show ‖B.opApply Dop (fun g => cut n g • F g) g‖ ≤ cF * B.gN g ^ (-A')
    rw [hsplit n g hg.1]
    calc ‖B.opApply Dop F g - B.opApply Dop (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) g‖
        ≤ ‖B.opApply Dop F g‖ + ‖B.opApply Dop (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) g‖ :=
          norm_sub_le _ _
      _ ≤ K * bF * B.gN g ^ (-A') + K * Kp * bF * B.gN g ^ (-A') * (1 / ((n : ℝ) + 1)) :=
          add_le_add (hb0 g hg) (hbψ n g hg)
      _ ≤ K * bF * B.gN g ^ (-A') + K * Kp * bF * B.gN g ^ (-A') * 1 := by
          have : 0 ≤ K * Kp * bF * B.gN g ^ (-A') := by positivity
          nlinarith
      _ = cF * B.gN g ^ (-A') := by rw [hcF]; ring
  · refine (hb0 g hg).trans ?_
    have hpw : 0 ≤ B.gN g ^ (-A') := Real.rpow_nonneg (P.B6.gN_nonneg g) _
    have : K * bF ≤ cF := by
      rw [hcF]
      have : 0 ≤ K * bF := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right this hpw
  · have hz : Tendsto (fun n : ℕ => B.opApply Dop (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) g) atTop
        (𝓝 0) := by
      refine squeeze_zero_norm (fun n => hbψ n g hg) ?_
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K * Kp * bF * B.gN g ^ (-A'))
      simpa using this
    have e3 : (fun n : ℕ => B.opApply Dop (fun g => cut n g • F g) g) =
        fun n : ℕ => B.opApply Dop F g - B.opApply Dop (fun g => P.JCx2.pdPsi ((n : ℝ) + 1) g • F g) g :=
      funext fun n => hsplit n g hg.1
    show Tendsto (fun n : ℕ => B.opApply Dop (fun g => cut n g • F g) g) atTop (𝓝 (B.opApply Dop F g))
    rw [e3]
    simpa using (tendsto_const_nhds (x := B.opApply Dop F g)).sub hz

end conv

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem hsInner_tendsto {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {u v : ℕ → (Wq →L[ℂ] Wp)} {x y : Wq →L[ℂ] Wp}
    (hu : Tendsto u atTop (𝓝 x)) (hv : Tendsto v atTop (𝓝 y)) :
    Tendsto (fun n => B.hsInner (u n) (v n)) atTop (𝓝 (B.hsInner x y)) := by
  show Tendsto (fun n => inner ℂ (B.hsVec (v n)) (B.hsVec (u n))) atTop (𝓝 (inner ℂ (B.hsVec y) (B.hsVec x)))
  have h1 : Tendsto (fun n => B.hsVec (v n)) atTop (𝓝 (B.hsVec y)) := (P.BetaSesquilinearity.hsVec_cont.tendsto y).comp hv
  have h2 : Tendsto (fun n => B.hsVec (u n)) atTop (𝓝 (B.hsVec x)) := (P.BetaSesquilinearity.hsVec_cont.tendsto x).comp hu
  exact h1.inner h2

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem formLimit_top (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ)
    (cut : ℕ → B.Mat P.k P.r → ℂ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ w, KB.CutWord P p.l0 w → w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) (P.r + 1) w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) (P.r + 1) w a b)) := by
  obtain ⟨c₁, hc₁⟩ := vecV_cut_empty
  obtain ⟨c₂, hc₂⟩ := vecV_cut_op
  refine ⟨5 * max Cb 0 + max Cb 0 ^ 2 + 1 + |max c₁ c₂|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut w hw hwN a b
  have hXn : ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) = 2 * (P0.r : ℝ) + P0.k + 1 := by push_cast; ring
  have hr0 : (0 : ℝ) ≤ P0.r := Nat.cast_nonneg _
  have hrX : (P0.r : ℝ) + 1 ≤ 2 * (P0.r : ℝ) + P0.k + 1 := by
    have : (0 : ℝ) ≤ P0.k := Nat.cast_nonneg _
    linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hCb0 : (0 : ℝ) ≤ max Cb 0 := le_max_right _ _
  have hcut' : ∀ n g, cut n g = 1 - P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    rw [hcut n g]
    simp [P.JCx2.pdPsi, P.JCx2.pdPhi, P.JCx2.pdChi, P.JCx2.pdSq]
  have hFck : B.CkOn ⊤ (B.GV P0.k P0.r) (D.cutF p.T.base χ f ε) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hχ hf ε
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  have hFv : ∀ g, Gf P0.k P0.r p.T.base.z p.T.base.z' g < ε * δ → D.cutF p.T.base χ f ε g = 0 := by
    intro g hg
    show ((χ (Gf P0.k P0.r p.T.base.z p.T.base.z' g / ε) : ℝ) : ℂ) • f g = 0
    rw [hχ0 _ (by rw [div_lt_iff₀ hε]; linarith), Complex.ofReal_zero, zero_smul]

  have hmono : ∀ c : ℝ, c ≤ max c₁ c₂ → ∀ B' : ℝ,
      max c₁ c₂ * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) + 1) ≤ B' →
      c * ((P0.r : ℝ) + 1) ^ 2 * ((P0.r : ℝ) * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) + 1) ≤ B' := by
    intro c hc B' hB
    rw [hXn]
    refine le_trans ?_ hB
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
  show Tendsto (fun n => D.RRplace p.T (M.sgn P0 p.l0) p.ν' p.m₀ (Top.topOf P0 p.l0 p.T p.ν' p.m₀ p.Θ p.TP)
      (fun g => cut n g • D.cutF p.T.base χ f ε g) (P0.r + 1) w a b) atTop
    (𝓝 (D.RRplace p.T (M.sgn P0 p.l0) p.ν' p.m₀ (Top.topOf P0 p.l0 p.T p.ν' p.m₀ p.Θ p.TP)
      (D.cutF p.T.base χ f ε) (P0.r + 1) w a b))
  unfold D.RRplace
  by_cases hab : D.IsLocPt a (P0.r + 1) ∧ D.IsLocPt b (P0.r + 1)
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  have hnle : ¬ (P0.r + 1 ≤ P0.r) := by omega
  simp only [dif_pos hab, dif_neg hnle, if_true]
  by_cases hw0 : w = []
  · subst hw0
    simp only [if_true]
    have hthr := thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 0) (max c₁ c₂) 0 0 A hr0 hrX hN0 hCb0
      le_rfl (by positivity) le_rfl (by simp) hA
    obtain ⟨b₀, hb₀⟩ := cutF_inCC p.T.base hχ hfA hε A 0 (by simp)
    have hva : ∀ q, Tendsto (fun n => D.vecV p.T.base p.ν' p.m₀ (fun g => cut n g • D.cutF p.T.base χ f ε g) q)
        atTop (𝓝 (D.vecV p.T.base p.ν' p.m₀ (D.cutF p.T.base χ f ε) q)) := fun q =>
      hc₁ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ q _ A b₀ cut
        (hmono c₁ (le_max_left _ _) A (by linarith [hthr])) hb₀ hFck hcut'
    exact hsInner_tendsto (hva a) (hva b)
  · simp only [if_neg hw0]
    unfold Top.topOf
    have hve : ∀ (e : Wd.Ix (Fin w.length)) (q : C.LPt), Tendsto
        (fun n => D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (fun g => cut n g • D.cutF p.T.base χ f ε g)) q) atTop
        (𝓝 (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (D.cutF p.T.base χ f ε)) q)) := by
      intro e q
      obtain ⟨nf, fib, o, κ, Dop, hfib, hIn, ho, hκ, hΘ⟩ := hDD w hw e
      have hcongr : ∀ G, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e G) q =
          D.vecV p.T.base p.ν' p.m₀ (B.opApply Dop G) q :=
        fun G => vecV_congrGPos p.T.base p.ν' p.m₀ q (fun g hg => hΘ G g ⟨hg.1, hg.2, fun l hl => by simp at hl⟩)
      simp only [hcongr]
      have ho' : (o : ℝ) ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) := by
        calc (o : ℝ) ≤ Cb * w.length * ((2 * P0.r + P0.k + 1 : ℕ) : ℝ) := ho
          _ ≤ max Cb 0 * w.length * (2 * (P0.r : ℝ) + P0.k + 1) := by
            rw [hXn]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
              (by linarith)
          _ ≤ max Cb 0 * N * (2 * (P0.r : ℝ) + P0.k + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hwN) hCb0) (by linarith)
      have hκ' : (κ : ℝ) ≤ max Cb 0 * ((P0.r : ℝ) + 1) * o :=
        hκ.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
          (Nat.cast_nonneg _))
      have hthr := thr_arith (P0.r) (2 * (P0.r : ℝ) + P0.k + 1) N (max Cb 0) (max c₁ c₂) o κ A hr0 hrX hN0 hCb0
        (Nat.cast_nonneg _) ho' (Nat.cast_nonneg _) hκ' hA
      obtain ⟨bF, hbF⟩ := cutF_inCC p.T.base hχ hfA hε (A - 2 * ((P0.r : ℝ) + 1) * o) o (by linarith)
      exact hc₂ P0.k P0.r Wp Wq p.T.base p.ν' p.m₀ q _ cut nf fib o κ Dop (ε * δ)
        (A - 2 * ((P0.r : ℝ) + 1) * o) bF hfib hIn (mul_pos hε hδ) hFv hFck hbF hcut'
        (hmono c₂ (le_max_right _ _) _ (by linarith [hthr]))
    apply tendsto_finset_sum
    intro e _
    apply tendsto_finset_sum
    intro ρ _
    apply Tendsto.const_mul
    have hcomp : ∀ q, Tendsto (fun n => (p.TP.E ρ).comp
        (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (fun g => cut n g • D.cutF p.T.base χ f ε g)) q)) atTop
        (𝓝 ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e (D.cutF p.T.base χ f ε)) q))) := fun q =>
      ((continuous_const.clm_comp continuous_id).tendsto _).comp (hve e q)
    exact hsInner_tendsto (hcomp a) (hcomp b)

end Formalism.FourierDecayAlt.P.PBE
