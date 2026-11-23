import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbSplitPt

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_split [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    (h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q)
    (h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ) :
    ∃ θL : Mt k r × Mt k r → ℝ, ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), KB.CptCoef Bs F →
      Integrable (lint Bs h'.choose θL F) (Bs.μW.prod Bs.μN) ∧
        D.vecV Bs ν' m₀ F q = ∫ x, lint Bs h'.choose θL F x ∂(Bs.μW.prod Bs.μN) := by
  obtain ⟨c₃, hc₃⟩ := orbJ_domL
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  have hγ := h'.choose_spec.1
  have hZ := h'.choose_spec.2.1
  have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
  have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
  obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
  have hZm := hZ.trans hmono
  obtain ⟨θ, maj, hθ, hθL, hθp, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
    ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  refine ⟨fun x => θ (x, 0), fun F hF => ?_⟩
  obtain ⟨cF, hcF0, hb⟩ := Formalism.FourierDecayAlt.P.PBN.gN_bound Bs hF A (le_max_left _ _)
  have hbnd : ∀ᵐ p ∂Bs.μSS, θ p * ‖F (B.sgs p h'.choose)‖ ≤ cF * maj p :=
    hdom F cF hcF0 (fun p hp => hb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
  have hFc : ContinuousOn F (B.GV k r) := Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hF.1
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose F) Bs.μSS :=
    Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs (U := B.GV k r) (fun p hp => Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hFc
  have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := by
    refine Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm) ?_
    filter_upwards [hbnd, Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS Bs] with p hp hs
    rw [norm_smul, Real.norm_of_nonneg (hθ.2.1 p)]
    unfold D.orbIntegrand
    rw [norm_smul, Formalism.FourierDecayAlt.P.B7.norm_xi, one_mul]
    exact (mul_le_mul_of_nonneg_left (Formalism.FourierDecayAlt.P.B7.norm_rho_le Bs hs F h'.choose) (hθ.2.1 p)).trans hp
  have hR' := inner_int Bs h'.choose hγ θ hθL hθp maj hmaj cF hFc hbnd
  obtain ⟨hint, heq⟩ := fub Bs h'.choose θ hθL F hi hR'
  refine ⟨hint, ?_⟩
  unfold D.vecV
  rw [dif_pos h, dif_pos h']
  have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
      Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose F p) Bs.μSS := ⟨θ, hθ, hi⟩
  unfold D.orbJ
  rw [dif_pos hex]
  refine (Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR F _ θ hex.choose_spec.1 hθ
    hex.choose_spec.2 hi).trans heq

end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
