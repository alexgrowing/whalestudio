import Mathlib
import GroundTheory.PAdicHodge.AnnNormAcrisToAnnPosBig
import GroundTheory.PAdicHodge.WAFracGlue
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

variable (p) (ρ1 : Set.Ioo (0 : ℝ) 1)

abbrev inRad : Set.Ioc (0 : ℝ) ρ1 := (𝔽).radPow ρ1

abbrev circ : Set.Ioo (0 : ℝ) 1 := (𝔽).powRadius ρ1

theorem coe_circ : ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ) = (ρ1 : ℝ) ^ p := by
  show (ρ1 : ℝ) ^ p ^ (𝔽).a = _; rw [frob_a, pow_one]

theorem coe_inRad : ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ) = (ρ1 : ℝ) ^ p := coe_circ p ρ1

theorem coe_topRad_circ : ((topRad (circ p ρ1) : Set.Ioc (0 : ℝ) (circ p ρ1)) : ℝ) = (ρ1 : ℝ) ^ p :=
  coe_circ p ρ1

theorem inRad_le_circ : ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ) ≤ (topRad (circ p ρ1) : ℝ) := by
  rw [coe_inRad, coe_topRad_circ]

theorem powRad_inRad_le :
    ((((𝔽).powRad (inRad p ρ1)) : Set.Ioc (0 : ℝ) (circ p ρ1)) : ℝ) ≤ (topRad (circ p ρ1) : ℝ) := by
  rw [TeichLift.TeichFrob.coe_powRad, frob_a, pow_one, coe_inRad, coe_topRad_circ, ← pow_mul]
  exact pow_le_pow_of_le_one ρ1.2.1.le ρ1.2.2.le (Nat.le_mul_of_pos_left p hp.out.pos)

theorem circ_le : ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ1 := (𝔽).powRadius_le_self ρ1

def resCirc : (𝓣).Ann ρ1 (inRad p ρ1) →+* (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1)) :=
  (𝓣).annRes (circ_le p ρ1) (inRad_le_circ p ρ1)

def frobCirc : (𝓣).Ann ρ1 (inRad p ρ1) →+* (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1)) :=
  ((𝓣).annRes (le_refl ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ)) (powRad_inRad_le p ρ1)).comp (𝔽).annFrob

abbrev circRad : AnnRad (circ p ρ1) (topRad (circ p ρ1)) := annIn (circ p ρ1) (topRad (circ p ρ1))

variable {p}

theorem annNorm_frobCirc (x : (𝓣).Ann ρ1 (inRad p ρ1)) :
    (𝓣).annNorm _ _ (circRad p ρ1) (frobCirc p ρ1 x) =
      (𝓣).annNorm ρ1 (inRad p ρ1) (annOut ρ1 (inRad p ρ1)) x ^ p := by
  rw [frobCirc, RingHom.comp_apply, (𝓣).annNorm_annRes]
  have e : annRadOf (le_refl ((circ p ρ1 : Set.Ioo (0 : ℝ) 1) : ℝ)) (powRad_inRad_le p ρ1) (circRad p ρ1) =
      (𝔽).annPowRad (annOut ρ1 (inRad p ρ1)) := by
    apply Subtype.ext
    rw [coe_annRadOf, TeichLift.TeichFrob.coe_annPowRad, frob_a, pow_one, coe_annOut, coe_annIn,
      coe_topRad_circ]
  rw [e, TeichLift.TeichFrob.annNorm_annFrob, frob_a, pow_one]

theorem annNorm_resCirc (x : (𝓣).Ann ρ1 (inRad p ρ1)) :
    (𝓣).annNorm _ _ (circRad p ρ1) (resCirc p ρ1 x) =
      (𝓣).annNorm ρ1 (inRad p ρ1) (annIn ρ1 (inRad p ρ1)) x := by
  rw [resCirc, (𝓣).annNorm_annRes]
  congr 1

theorem piE_eq_natCast (σ : Set.Ioo (0 : ℝ) 1) : (𝓣).piE σ = (p : (𝓣).RobbaExt σ) := by
  rw [TeichLift.piE, TeichLift.ofAll]
  rw [← map_natCast (Completion.coeRingHom : (𝓣).Econ σ →+* (𝓣).RobbaExt σ) p]
  congr 1
  apply Subtype.ext
  change algebraMap (WC p) (𝓣).B ((p : ℕ) : WC p) = (((p : ℕ) : (𝓣).Econ σ) : (𝓣).B)
  rw [map_natCast]
  simp

theorem annNorm_coeAnn_sub (r : AnnRad ρ1 (inRad p ρ1)) (a b : (𝓣).Econ ρ1) :
    (𝓣).annNorm ρ1 (inRad p ρ1) r ((𝓣).coeAnn a - (𝓣).coeAnn b) =
      (𝓣).extNorm ρ1 (annIoc r) ((a : (𝓣).RobbaExt ρ1) - b) := by
  rw [← (𝓣).toAnn_coe, ← (𝓣).toAnn_coe, ← map_sub, (𝓣).annNorm_toAnn]

theorem annIoc_annOut : annIoc (annOut ρ1 (inRad p ρ1)) = topRad ρ1 := rfl

theorem annIoc_annIn : annIoc (annIn ρ1 (inRad p ρ1)) = (𝔽).radPow ρ1 := rfl

theorem frobCirc_toAnn (w : (𝓣).RobbaExt ρ1) :
    frobCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) w) =
      (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) ((𝔽).extFrob ρ1 w) := by
  rw [frobCirc, RingHom.comp_apply, TeichLift.TeichFrob.annFrob_toAnn, (𝓣).annRes_toAnn, (𝓣).res_self]

theorem resCirc_toAnn (w : (𝓣).RobbaExt ρ1) :
    resCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) w) =
      (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) ((𝓣).res ((𝔽).powRadius_le_self ρ1) w) := by
  rw [resCirc, (𝓣).annRes_toAnn]

theorem annNorm_natCast_p_circ :
    (𝓣).annNorm _ _ (circRad p ρ1) (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) = (ρ1 : ℝ) ^ p := by
  rw [annNorm_awayToAnn_natCast_p]; exact coe_circ p ρ1

set_option maxHeartbeats 3200000 in

theorem exists_eigen_of_ann (N : ℕ) (Y : (𝓣).Ann ρ1 (inRad p ρ1))
    (hY : (𝓣).annNorm _ _ (circRad p ρ1)
      (frobCirc p ρ1 Y - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 Y) = 0) :
    ∃ g : (𝓣).RobbaExt ρ1, (𝔽).extFrob ρ1 g = (p : (𝓣).RobbaExt _) ^ N *
        (𝓣).res ((𝔽).powRadius_le_self ρ1) g ∧ (𝓣).toAnn ρ1 (inRad p ρ1) g = Y := by
  choose U hU using fun J : ℕ => (𝓣).exists_coeAnn_near Y (Nat.one_div_pos_of_nat (n := J))
  set u : ℕ → (𝓣).RobbaExt ρ1 := fun J => (U J : (𝓣).RobbaExt ρ1) with hudef
  have hdiff : ∀ (r : AnnRad ρ1 (inRad p ρ1)) (J K : ℕ), (𝓣).extNorm ρ1 (annIoc r) (u J - u K) ≤
      max (1 / ((J : ℝ) + 1)) (1 / ((K : ℝ) + 1)) := by
    intro r J K
    rw [hudef, ← annNorm_coeAnn_sub]
    have e : (𝓣).coeAnn (U J) - (𝓣).coeAnn (U K) = -(Y - (𝓣).coeAnn (U J)) + (Y - (𝓣).coeAnn (U K)) := by
      ring
    rw [e]
    refine ((𝓣).annNorm_add_le r _ _).trans (max_le_max ?_ (hU K r).le)
    rw [(𝓣).annNorm_neg]; exact (hU J r).le
  have hcau : ∀ r : AnnRad ρ1 (inRad p ρ1), ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀,
      (𝓣).extNorm ρ1 (annIoc r) (u J - u K) ≤ ε := by
    intro r ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_nat_one_div_lt hε
    refine ⟨J₀, fun J hJ K hK => (hdiff r J K).trans (max_le ?_ ?_)⟩
    · exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hJ 1)).trans hJ₀.le
    · exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hK 1)).trans hJ₀.le

  have hD : ∀ J, (𝓣).extNorm (circ p ρ1) (topRad _)
      ((𝔽).extFrob ρ1 (u J) - (𝓣).piE ((𝔽).powRadius ρ1) ^ N * (𝓣).res ((𝔽).powRadius_le_self ρ1) (u J)) ≤
        1 / ((J : ℝ) + 1) := by
    intro J
    have hJ1 : 1 / ((J : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg J : (0 : ℝ) ≤ J)]
    rw [piE_eq_natCast]
    have e1 := (𝓣).annNorm_toAnn (circRad p ρ1)
      ((𝔽).extFrob ρ1 (u J) - (p : (𝓣).RobbaExt _) ^ N * (𝓣).res ((𝔽).powRadius_le_self ρ1) (u J))
    have hioc : annIoc (circRad p ρ1) = topRad (circ p ρ1) := rfl
    rw [hioc] at e1
    rw [← e1, map_sub, map_mul, map_pow, map_natCast, ← frobCirc_toAnn, ← resCirc_toAnn, hudef,
      (𝓣).toAnn_coe]
    set c := (𝓣).coeAnn (σ0 := inRad p ρ1) (U J)
    have e2 : frobCirc p ρ1 c - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 c =
        (frobCirc p ρ1 (c - Y) - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 (c - Y)) +
          (frobCirc p ρ1 Y - (p : (𝓣).Ann _ _) ^ N * resCirc p ρ1 Y) := by
      rw [map_sub, map_sub]; ring
    rw [e2]
    refine ((𝓣).annNorm_add_le _ _ _).trans (max_le ?_ (by rw [hY]; positivity))
    refine ((𝓣).annNorm_sub_le _ _ _).trans (max_le ?_ ?_)
    · rw [annNorm_frobCirc, (𝓣).annNorm_sub_comm]
      exact (pow_le_of_le_one ((𝓣).annNorm_nonneg _ _) ((hU J _).le.trans hJ1) hp.out.ne_zero).trans
        (hU J _).le
    · rw [(𝓣).annNorm_mul, (𝓣).annNorm_pow, annNorm_natCast_p_circ, annNorm_resCirc, (𝓣).annNorm_sub_comm]
      refine (mul_le_of_le_one_left ((𝓣).annNorm_nonneg _ _) ?_).trans (hU J _).le
      exact pow_le_one₀ (pow_nonneg ρ1.2.1.le p) (pow_le_one₀ ρ1.2.1.le ρ1.2.2.le)
  have hsmall : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, (𝓣).extNorm ((𝔽).powRadius ρ1) (topRad _)
      ((𝔽).extFrob ρ1 (u J) - (𝓣).piE ((𝔽).powRadius ρ1) ^ N * (𝓣).res ((𝔽).powRadius_le_self ρ1) (u J))
        ≤ ε := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_nat_one_div_lt hε
    refine ⟨J₀, fun J hJ => (hD J).trans ?_⟩
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hJ 1)).trans hJ₀.le
  obtain ⟨g, hg, hgeq⟩ := TeichLift.TeichFrob.exists_eigen_of_approx (F := 𝔽) (by rw [frob_a]; exact one_pos)
    N u (hcau (annOut ρ1 (inRad p ρ1))) (hcau (annIn ρ1 (inRad p ρ1))) hsmall
  refine ⟨g, by rw [hgeq, piE_eq_natCast], ?_⟩
  refine (𝓣).eq_of_annNorm_sub ?_ ?_
  all_goals
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ((𝓣).annNorm_nonneg _ _)
    rw [zero_add]
    obtain ⟨J₁, hJ₁⟩ := hg ε hε
    obtain ⟨J₂, hJ₂⟩ := exists_nat_one_div_lt hε
    set J := max J₁ J₂
    have e : (𝓣).toAnn ρ1 (inRad p ρ1) g - Y = ((𝓣).toAnn ρ1 (inRad p ρ1) g - (𝓣).coeAnn (U J)) +
        -(Y - (𝓣).coeAnn (U J)) := by ring
    rw [e]
    refine ((𝓣).annNorm_add_le _ _ _).trans (max_le ?_ ?_)
  · rw [← (𝓣).toAnn_coe, ← map_sub, (𝓣).annNorm_toAnn, annIoc_annIn]
    exact (hJ₁ J (le_max_left _ _)).2
  · rw [(𝓣).annNorm_neg]
    refine (hU J _).le.trans ((one_div_le_one_div_of_le (by positivity) ?_).trans hJ₂.le)
    exact_mod_cast Nat.add_le_add_right (le_max_right J₁ J₂) 1
  · rw [← (𝓣).toAnn_coe, ← map_sub, (𝓣).annNorm_toAnn, annIoc_annOut]
    exact (hJ₁ J (le_max_left _ _)).1
  · rw [(𝓣).annNorm_neg]
    refine (hU J _).le.trans ((one_div_le_one_div_of_le (by positivity) ?_).trans hJ₂.le)
    exact_mod_cast Nat.add_le_add_right (le_max_right J₁ J₂) 1

section Step3

variable (hσ : (p : ℝ)⁻¹ ≤ ((inRad p ρ1 : Set.Ioc (0 : ℝ) ρ1) : ℝ))

include hσ in
theorem inv_p_le_circ : (p : ℝ)⁻¹ ≤ ((topRad (circ p ρ1) : Set.Ioc (0 : ℝ) (circ p ρ1)) : ℝ) := by
  rw [coe_topRad_circ]; rw [coe_inRad] at hσ; exact hσ

set_option maxHeartbeats 1600000 in
theorem frobCirc_bcrisToAnn (x : BCrisPlus ℂ_[p] p) :
    frobCirc p ρ1 (bcrisToAnn hσ x) = bcrisToAnn (inv_p_le_circ ρ1 hσ) (phiPlus ℂ_[p] p x) := by
  have e : (frobCirc p ρ1).comp (bcrisToAnn hσ) = (bcrisToAnn (inv_p_le_circ ρ1 hσ)).comp (phiPlus ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply, bcrisToAnn_algebraMap, phiPlus_algebraMap, frobCirc]
      exact annRes_annFrob_acrisToAnn _ _ hσ (inv_p_le_circ ρ1 hσ) a)
  exact congrArg (fun f : BCrisPlus ℂ_[p] p →+* (𝓣).Ann _ _ => f x) e

set_option maxHeartbeats 1600000 in
theorem resCirc_bcrisToAnn (x : BCrisPlus ℂ_[p] p) :
    resCirc p ρ1 (bcrisToAnn hσ x) = bcrisToAnn (inv_p_le_circ ρ1 hσ) x := by
  rw [resCirc, annRes_bcrisToAnn]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hε hζ in
theorem frobCirc_tTilde :
    frobCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1)) =
      (p : (𝓣).Ann _ _) * (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) (tTildeExt p ε (circ p ρ1)) := by
  rw [frobCirc_toAnn, extFrob_tTildeExt hε hζ, map_mul, map_natCast]

include hε hζ in
theorem resCirc_tTilde :
    resCirc p ρ1 ((𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1)) =
      (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) (tTildeExt p ε (circ p ρ1)) := by
  rw [resCirc_toAnn, res_tTildeExt hε hζ]

set_option maxHeartbeats 1600000 in
include hε hζ in

theorem annNorm_frobCirc_sub_eq_zero {a b : BCrisPlus ℂ_[p] p} (hb : b ≠ 0)
    (hφ : phiPlus ℂ_[p] p a * b = (p : BCrisPlus ℂ_[p] p) * a * phiPlus ℂ_[p] p b) {m : ℕ}
    {Y : (𝓣).Ann ρ1 (inRad p ρ1)}
    (hY : Y * bcrisToAnn hσ b = (𝓣).toAnn ρ1 (inRad p ρ1) (tTildeExt p ε ρ1) ^ m * bcrisToAnn hσ a) :
    (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1)
      (frobCirc p ρ1 Y - (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ (m + 1) * resCirc p ρ1 Y) = 0 := by
  set hσ' := inv_p_le_circ ρ1 hσ
  set D := frobCirc p ρ1 Y - (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ (m + 1) * resCirc p ρ1 Y
  set t' := (𝓣).toAnn (circ p ρ1) (topRad (circ p ρ1)) (tTildeExt p ε (circ p ρ1))
  have h1 : frobCirc p ρ1 Y * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) =
      ((p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) * t') ^ m * bcrisToAnn hσ' (phiPlus ℂ_[p] p a) := by
    rw [← frobCirc_bcrisToAnn ρ1 hσ, ← frobCirc_bcrisToAnn ρ1 hσ, ← map_mul, hY, map_mul, map_pow,
      frobCirc_tTilde ρ1 hε hζ]
  have h2 : resCirc p ρ1 Y * bcrisToAnn hσ' b = t' ^ m * bcrisToAnn hσ' a := by
    rw [← resCirc_bcrisToAnn ρ1 hσ, ← resCirc_bcrisToAnn ρ1 hσ, ← map_mul, hY, map_mul, map_pow,
      resCirc_tTilde ρ1 hε hζ]
  have h3 : bcrisToAnn hσ' (phiPlus ℂ_[p] p a) * bcrisToAnn hσ' b =
      (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) * bcrisToAnn hσ' a * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) := by
    rw [← map_mul, hφ, map_mul, map_mul, map_natCast]
  have key : D * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) * bcrisToAnn hσ' b = 0 := by
    have e : D * bcrisToAnn hσ' (phiPlus ℂ_[p] p b) * bcrisToAnn hσ' b =
        (frobCirc p ρ1 Y * bcrisToAnn hσ' (phiPlus ℂ_[p] p b)) * bcrisToAnn hσ' b -
          (p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ (m + 1) * (resCirc p ρ1 Y * bcrisToAnn hσ' b) *
            bcrisToAnn hσ' (phiPlus ℂ_[p] p b) := by ring
    rw [e, h1, h2]
    linear_combination ((p : (𝓣).Ann (circ p ρ1) (topRad (circ p ρ1))) ^ m * t' ^ m) * h3
  have hpos1 : 0 < (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1) (bcrisToAnn hσ' (phiPlus ℂ_[p] p b)) := by
    rw [← frobCirc_bcrisToAnn ρ1 hσ, annNorm_frobCirc]
    exact pow_pos (annNorm_bcrisToAnn_pos hσ hb _) p
  have hpos2 : 0 < (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1) (bcrisToAnn hσ' b) :=
    annNorm_bcrisToAnn_pos hσ' hb _
  have h0 := congrArg ((𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1)) key
  rw [(𝓣).annNorm_mul, (𝓣).annNorm_mul, (𝓣).annNorm_zero] at h0
  have hD0 := (𝓣).annNorm_nonneg (circRad p ρ1) D
  by_contra hne
  have hDpos : 0 < (𝓣).annNorm (circ p ρ1) (topRad (circ p ρ1)) (circRad p ρ1) D :=
    lt_of_le_of_ne hD0 (Ne.symm hne)
  have := mul_pos (mul_pos hDpos hpos1) hpos2
  linarith

end Step3

end WAFrac

end GroundTheory.PAdicHodge
