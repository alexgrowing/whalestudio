import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.NFx4.NO

section Curv

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A)

def curvTh0 : A := d.L.ζ * d.L.nab + d.L.ζb * d.L.nabs

def curvK : A := d.κ (fun ρ => ((absTy P ρ : ℝ) : ℂ)) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))

theorem curv_theta_split : ThetaC d = curvTh0 d + curvK d := by
  unfold ThetaC curvTh0 curvK; abel

theorem curv_fc {x y : A} (hx : x ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A))
    (hy : y ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A)) : Commute x y :=
  d.L.fns_comm x (Or.inr hx) y (Or.inr hy)

theorem curvature_theta_commutator_zeta : curvTh0 d * d.L.ζb = d.L.ζb * curvTh0 d - d.L.ζb := by
  have h1 : Commute d.L.ζ d.L.ζb := curv_fc d (by simp) (by simp)
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, d.L.nab_ζb, d.L.nabs_ζb, mul_sub, mul_one]
  rw [h1.left_comm]
  abel

theorem curvature_theta_commutes_G : curvTh0 d * d.L.GG = d.L.GG * curvTh0 d := by
  have h1 : Commute d.L.ζ d.L.ζb := curv_fc d (by simp) (by simp)
  have h2 : Commute d.L.ζ d.L.GG := curv_fc d (by simp) (by simp)
  have h3 : Commute d.L.ζb d.L.GG := curv_fc d (by simp) (by simp)
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, d.L.nab_GG, d.L.nabs_GG, mul_sub]
  rw [h2.left_comm, h3.left_comm, h1.eq]
  abel

theorem curvature_theta_commutator_nabla : curvTh0 d * d.L.nab =
    d.L.nab * curvTh0 d - d.L.nab + d.L.ζb * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) := by
  have e1 : ∀ X : A, d.L.nab * (d.L.ζ * X) = d.L.ζ * (d.L.nab * X) + X := fun X => by
    rw [← mul_assoc, d.L.nab_ζ, add_mul, one_mul, mul_assoc]
  have e2 : ∀ X : A, d.L.nab * (d.L.ζb * X) = d.L.ζb * (d.L.nab * X) := fun X => by
    rw [← mul_assoc, d.L.nab_ζb, mul_assoc]
  unfold curvTh0
  simp only [add_mul, mul_add, mul_assoc, e1, e2, mul_sub]
  abel

theorem curv_K_comm (hRel : d.Rel) {g : A} (hg : g ∈ ({d.L.ζb, d.L.GG} : Set A)) : curvK d * g = g * curvK d := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  have hg' : g ∈ ({d.L.ζ, d.L.ζi, d.L.ζb, d.L.ζbi, d.L.GG, d.L.GGi} : Set A) := by rcases hg with rfl | rfl <;> simp
  have hk : ∀ f : M.Ty P → ℂ, Commute (d.κ f) g := fun f => kap_comm_fn hRel f (Or.inl (Or.inr hg'))
  have hGi : Commute d.L.GGi g := curv_fc d (by simp) hg'
  have ha : Commute (algebraMap ℂ A (P.TT : ℂ)) g := Algebra.commute_algebraMap_left _ _
  exact ((hk _).add_left ((ha.mul_left hGi).mul_left (hk _))).eq

theorem curv_K_nab (hRel : d.Rel) : curvK d * d.L.nab = d.L.nab * curvK d +
    algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
  have hk : ∀ f : M.Ty P → ℂ, Commute (d.κ f) d.L.nab := fun f => kap_comm_fn hRel f (Or.inr (by simp))
  have ha : Commute (algebraMap ℂ A (P.TT : ℂ)) d.L.nab := Algebra.commute_algebraMap_left _ _
  have hζ : Commute (algebraMap ℂ A (P.TT : ℂ)) d.L.ζb := Algebra.commute_algebraMap_left _ _
  unfold curvK
  rw [add_mul, mul_add, (hk _).eq]
  have : algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) * d.L.nab =
      d.L.nab * (algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))) +
      algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
    rw [mul_assoc _ _ d.L.nab, (hk _).eq, ← mul_assoc, mul_assoc _ d.L.GGi d.L.nab]
    rw [show d.L.nab * (algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))) =
      algebraMap ℂ A (P.TT : ℂ) * (d.L.nab * d.L.GGi) * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) by
        rw [← mul_assoc, ← mul_assoc, ← ha.eq]; simp only [mul_assoc]]
    rw [d.L.nab_GGi]
    rw [show d.L.GGi * d.L.nab = (d.L.GGi * d.L.nab - d.L.ζb * d.L.GGi * d.L.GGi) + d.L.ζb * d.L.GGi * d.L.GGi by abel]
    simp only [mul_add, add_mul, mul_assoc]
    rw [← mul_assoc (algebraMap ℂ A (P.TT : ℂ)) d.L.ζb, hζ.eq]
    simp only [mul_assoc]
    abel
  rw [this]
  abel

theorem curv_kap_theta (hRel : d.Rel) (f : M.Ty P → ℂ) : Commute (d.κ f) (ThetaC d) := by
  have hf : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (d.κ f) g := fun g hg => kap_comm_fn hRel f hg
  have hz : Commute (d.κ f) d.L.ζ := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hzb : Commute (d.κ f) d.L.ζb := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hGi : Commute (d.κ f) d.L.GGi := hf _ (Or.inl (by simp [R.LevelData.fns]))
  have hn : Commute (d.κ f) d.L.nab := hf _ (Or.inr (by simp))
  have hns : Commute (d.κ f) d.L.nabs := hf _ (Or.inr (by simp))
  have hkk : ∀ h : M.Ty P → ℂ, Commute (d.κ f) (d.κ h) := fun h => by
    show d.κ f * d.κ h = d.κ h * d.κ f
    rw [← map_mul, ← map_mul, mul_comm]
  unfold ThetaC
  exact (((hz.mul_right hn).add_right (hzb.mul_right hns)).add_right (hkk _)).add_right
    (((Algebra.commute_algebraMap_right _ _).mul_right hGi).mul_right (hkk _))

theorem curv_theta_zb (hRel : d.Rel) : ThetaC d * d.L.ζb = d.L.ζb * ThetaC d - d.L.ζb := by
  rw [curv_theta_split, add_mul, curvature_theta_commutator_zeta, curv_K_comm d hRel (by simp), mul_add]; abel

theorem curv_theta_GG (hRel : d.Rel) : ThetaC d * d.L.GG = d.L.GG * ThetaC d := by
  rw [curv_theta_split, add_mul, curvature_theta_commutes_G, curv_K_comm d hRel (by simp), mul_add]

theorem curv_theta_nab (hRel : d.Rel) : ThetaC d * d.L.nab = d.L.nab * ThetaC d - d.L.nab +
    d.L.ζb * (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
    algebraMap ℂ A (P.TT : ℂ) * d.L.ζb * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) := by
  rw [curv_theta_split, add_mul, curvature_theta_commutator_nabla, curv_K_nab d hRel, mul_add]; abel

theorem GG_mul_l0_eq (Y : ℂ) : d.L.GG * d.L.l0 Y = -(d.L.GG * d.L.nab) - algebraMap ℂ A (Y + 1 / 2) * d.L.ζb := by
  have h3 : Commute d.L.GG d.L.ζb := curv_fc d (by simp) (by simp)
  have ha : Commute d.L.GG (algebraMap ℂ A (Y + 1 / 2)) := Algebra.commute_algebraMap_right _ _
  unfold R.LevelData.l0
  rw [mul_sub, mul_neg, ← mul_assoc, ha.eq, mul_assoc, ← mul_assoc d.L.GG, h3.eq, mul_assoc, d.L.GG_GGi, mul_one]

theorem curv_key (hRel : d.Rel) (Y : ℂ) :
    ThetaC d * (d.L.GG * d.L.l0 Y) - d.L.GG * d.L.l0 Y * ThetaC d + d.L.GG * d.L.l0 Y =
      -(d.L.GG * (d.L.ζb * ((d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) +
        algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ))))) := by
  have hzbT : Commute d.L.ζb (algebraMap ℂ A (P.TT : ℂ)) := Algebra.commute_algebraMap_right _ _
  have r1 : ThetaC d * (d.L.GG * d.L.nab) = d.L.GG * (ThetaC d * d.L.nab) := by
    rw [← mul_assoc, curv_theta_GG d hRel, mul_assoc]
  have r2 : ThetaC d * (algebraMap ℂ A (Y + 1 / 2) * d.L.ζb) =
      algebraMap ℂ A (Y + 1 / 2) * (ThetaC d * d.L.ζb) := by
    rw [← mul_assoc, (Algebra.commute_algebraMap_right (Y + 1 / 2) (ThetaC d)).eq, mul_assoc]
  rw [GG_mul_l0_eq]
  simp only [mul_neg, neg_mul, mul_sub, sub_mul, r1, r2, curv_theta_nab d hRel, curv_theta_zb d hRel]
  simp only [mul_add, mul_sub, mul_assoc]
  rw [← mul_assoc d.L.ζb (algebraMap ℂ A (P.TT : ℂ)), hzbT.eq]
  simp only [mul_assoc]
  abel

theorem curvature_block_form_holds : GTCCurvBlock := by
  intro P A _ _ _ d hRel hc ρ
  have hκ : d.κ (dTy P ρ) = Pj d ρ := rfl
  rw [hκ]
  set Pp := Pj d ρ with hPp
  have hΘ : Pp * ThetaC d = ThetaC d * Pp := comm_Pj_of d (curv_kap_theta d hRel) ρ
  have hGGP : Pp * d.L.GG = d.L.GG * Pp := comm_Pj_of d (fun f => kap_GG hRel f) ρ
  have hl0P : Pp * d.L.l0 Complex.I = d.L.l0 Complex.I * Pp := comm_Pj_of d (fun f => kappa_commute_l0 hRel f _) ρ
  have hPP : Pp * Pp = Pp := Pj_idem d ρ
  have hx : M.xC P ρ Complex.I ≠ 0 := by
    unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i _ h
    have := congrArg Complex.im h
    simp at this
  have hPt : Pp * d.QQ Complex.I 1 0 * Pp = M.xC P ρ Complex.I • (d.L.GG * d.L.l0 Complex.I * Pp) := by
    rw [normal_form_lower_left, mul_add, add_mul, lower_sum_diagonal_zero hRel, add_zero]
    rw [← mul_assoc Pp, ← mul_assoc Pp, hGGP, mul_assoc d.L.GG Pp, Q.NFData.x, hPp, Pj_kap, ← hPp]
    rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc]
    congr 1
    simp only [mul_assoc]
    rw [← mul_assoc Pp, hl0P, mul_assoc, hPP]
  set W := d.L.GG * d.L.l0 Complex.I with hW
  have hv : Pp * (ThetaC d * d.QQ Complex.I 1 0 - d.QQ Complex.I 1 0 * ThetaC d) * Pp =
      Pp * (-d.QQ Complex.I 1 0) * Pp := by rw [hc]
  have e1 : Pp * (ThetaC d * d.QQ Complex.I 1 0 - d.QQ Complex.I 1 0 * ThetaC d) * Pp =
      ThetaC d * (Pp * d.QQ Complex.I 1 0 * Pp) - (Pp * d.QQ Complex.I 1 0 * Pp) * ThetaC d := by
    rw [mul_sub, sub_mul]
    congr 1
    · rw [← mul_assoc, hΘ]; simp only [mul_assoc]
    · simp only [mul_assoc]; rw [← hΘ]
  rw [e1, mul_neg, neg_mul, hPt] at hv
  have hv2 : M.xC P ρ Complex.I • ((ThetaC d * W - W * ThetaC d + W) * Pp) = 0 := by
    have : (ThetaC d * W - W * ThetaC d + W) * Pp = ThetaC d * (W * Pp) - W * Pp * ThetaC d + W * Pp := by
      rw [add_mul, sub_mul, mul_assoc, mul_assoc W, mul_assoc W, ← hΘ]
    rw [mul_smul_comm, smul_mul_assoc] at hv
    rw [this, smul_add, smul_sub, hv]
    abel
  have hv3 : (ThetaC d * W - W * ThetaC d + W) * Pp = 0 := by
    have := congrArg (fun z => (M.xC P ρ Complex.I)⁻¹ • z) hv2
    simpa only [smul_smul, inv_mul_cancel₀ hx, one_smul, smul_zero] using this
  rw [hW, curv_key d hRel, neg_mul, neg_eq_zero] at hv3
  set C := d.L.nabs * d.L.nab - d.L.nab * d.L.nabs
  have hκP : d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)) * Pp = ((-2 * M.aC P ρ : ℝ) : ℂ) • Pp := by
    rw [hPp, kap_Pj]
  have hv4 : C * Pp + algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * (((-2 * M.aC P ρ : ℝ) : ℂ) • Pp) = 0 := by
    have e : d.L.ζbi * (d.L.GGi * (d.L.GG * (d.L.ζb * (C + algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi *
        d.κ (fun ρ => ((-2 * M.aC P ρ : ℝ) : ℂ)))) * Pp)) = 0 := by
      rw [hv3, mul_zero, mul_zero]
    rw [← e]
    simp only [mul_assoc]
    rw [← mul_assoc d.L.GGi d.L.GG, d.L.GGi_GG, one_mul, ← mul_assoc d.L.ζbi d.L.ζb, d.L.ζbi_ζb, one_mul]
    rw [add_mul]
    simp only [mul_assoc]
    rw [hκP]
  have hfin : C * Pp = -(algebraMap ℂ A (P.TT : ℂ) * d.L.GGi * d.L.GGi * (((-2 * M.aC P ρ : ℝ) : ℂ) • Pp)) :=
    eq_neg_of_add_eq_zero_left hv4
  rw [hfin, mul_smul_comm]
  simp only [mul_assoc]
  rw [← Algebra.smul_def, ← Algebra.smul_def, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

end Curv

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
