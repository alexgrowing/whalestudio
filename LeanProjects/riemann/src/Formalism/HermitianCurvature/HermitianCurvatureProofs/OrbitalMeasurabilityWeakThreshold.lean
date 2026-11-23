import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDomainMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothWordsAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SandwichRhoAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordIntegralScaling

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.WeakThresholdClauses

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def WeakDominationThreshold (k r : ℕ) (A : ℝ) (m : ℕ) : Prop :=
  0 < A - 6 * (r : ℝ) * (m : ℝ) ∧
    (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) < A - 6 * (r : ℝ) * (m : ℝ)

def NNMajW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    WeakDominationThreshold k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBoundW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    WeakDominationThreshold k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeasW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    WeakDominationThreshold k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

def JWordsW : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    WeakDominationThreshold k r A m → B.InCC A m F →
    Q.CkLev k r 0 m (Q.OmPlus k r D.z D.z') (B.JF D F) ∧
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        Integrable (fun p => xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS ∧
        B.dLR u v (B.JF D F) g =
          ∫ p, xiP D p • B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g ∂D.μSS

end Formalism.FourierDecayAlt.P.WeakThresholdClauses

namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
open Formalism.FourierDecayAlt.P.WeakDominationMajorants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem scalar_majorant_weak_threshold : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW := by
  intro k r Wp Wq _ _ _ _ D A m hThr K hK hKO
  obtain ⟨C3, hC3, horb⟩ := orbit3 D.z D.z' K hK hKO
  obtain ⟨cW, hcW, hW⟩ := uw_bound D.z D.z_mem D.T_pos
  obtain ⟨cW', hcW', hW'⟩ := uw_bound D.z' D.z'_mem D.T'_pos

  have hc : 1 ≤ max cW cW' := le_trans hcW (le_max_left _ _)
  have hC4 : 1 ≤ max 1 (C3 * max cW cW' ^ (6 * r)) := le_max_left _ _
  set c := max cW cW' with hc_def
  set C4 := max 1 (C3 * c ^ (6 * r)) with hC4_def
  set NN : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hNN
  have hNN1 : 1 ≤ NN := by rw [hNN]; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  set Λ1 := max 1 (NN * c ^ 2 * C4 ^ 2) with hΛ1_def
  have hΛ1 : 1 ≤ Λ1 := le_max_left _ _
  set A1 := A - 6 * (r : ℝ) * (m : ℝ) with hA1_def

  have hA1pos : 0 < A1 := hThr.1
  set β := A1 / (6 * (r : ℝ) + 1) with hβ_def
  have hβ0 : 0 ≤ β := div_nonneg hA1pos.le (by positivity)
  have hβA : 6 * (r : ℝ) * β ≤ A1 := by
    rw [hβ_def, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hthr : r = 0 ∨ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) < β := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exact Or.inl h
    · right
      rw [hβ_def, lt_div_iff₀ (by positivity)]
      exact hThr.2

  set f : Mt k r → ℝ := fun x => gN (Matrix.of x : Mat k r) ^ (-β) with hf_def
  refine ⟨fun p => Λ1 ^ m * (C4 ^ β) ^ 2 * (f p.1.2 * f p.2.2), ?_, ?_⟩
  ·
    have : SigmaFinite D.μN := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
    have : IsFiniteMeasure D.μW := haar_finite D.haarW (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos)
    have : IsFiniteMeasure D.μW' :=
      haar_finite D.haarW' (Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos)
    have hfi : Integrable f D.μN := by
      refine ⟨((NInt.gN_cont k r).measurable.pow_const (-β)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (Orb.gN_nonneg _) _)]
      exact NInt.lint_gN_fin k r D.μN D.haarN β hthr
    have h1 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW.prod D.μN) :=
      (integrable_const (1 : ℝ)).mul_prod hfi
    have h2 : Integrable (fun q : Mt k r × Mt k r => (1 : ℝ) * f q.2) (D.μW'.prod D.μN) :=
      (integrable_const (1 : ℝ)).mul_prod hfi
    have h3 := (h1.mul_prod h2).const_mul (Λ1 ^ m * (C4 ^ β) ^ 2)
    refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [one_mul]
  · intro u v hu hv hl g hg
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp

    have hh : Matrix.of p.1.1 ∈ GV k r := hp.1.1
    have hn : Matrix.of p.1.2 ∈ Nset k r := hp.2.1
    have hh' : Matrix.of p.2.1 ∈ GV k r := hp.2.2.1.1
    have hn' : Matrix.of p.2.2 ∈ Nset k r := hp.2.2.2
    have hgG : g ∈ GV k r := (hKO hg).1
    have hx : sgs p g ∈ GV k r := by
      simp only [sgs]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
        (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hh) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (Orb.n_mem_G hn))) hgG) (Orb.n_mem_G hn')) hh'
    set X := gN (sgs p g) with hX_def
    have hX1 : 1 ≤ X := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx

    have hY : (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 = Matrix.of p.1.1 * sgs p g * (Matrix.of p.2.1)⁻¹ := by
      have hs : sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
        simp only [sgs, Matrix.mul_assoc]
      rw [hs, Matrix.mul_assoc (Matrix.of p.1.1)⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh),
        Matrix.mul_nonsing_inv_cancel_right _ _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit hh')]
    have hgh : gN (Matrix.of p.1.1) ≤ c := (hW _ hp.1).trans (le_max_left _ _)
    have hgh' : gN (Matrix.of p.2.1) ≤ c := (hW' _ hp.2.2.1).trans (le_max_right _ _)
    have hYb : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ≤ c ^ 2 * X := by
      rw [hY]
      have e1 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1 * sgs p g) (Matrix.of p.2.1)⁻¹
      have e2 := Formalism.FourierDecayAlt.P.B6.gN_mul_le (Matrix.of p.1.1) (sgs p g)
      rw [Orb.gN_inv hh'] at e1
      have := Orb.gN_nonneg (sgs p g); have := Orb.gN_nonneg (Matrix.of p.1.1)
      calc _ ≤ gN (Matrix.of p.1.1 * sgs p g) * gN (Matrix.of p.2.1) := e1
        _ ≤ (c * X) * c := by
            have e3 : gN (Matrix.of p.1.1 * sgs p g) ≤ c * X :=
              e2.trans (mul_le_mul_of_nonneg_right hgh (Orb.gN_nonneg _))
            exact mul_le_mul e3 hgh' (Orb.gN_nonneg _) (by positivity)
        _ = c ^ 2 * X := by ring
    have hYX : gN ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) ^ (3 * r) ≤ c ^ (6 * r) * X ^ (3 * r) := by
      calc _ ≤ (c ^ 2 * X) ^ (3 * r) := pow_le_pow_left₀ (Orb.gN_nonneg _) hYb _
        _ = c ^ (6 * r) * X ^ (3 * r) := by rw [mul_pow, ← pow_mul]; ring_nf
    obtain ⟨hb1, hb2⟩ := horb g hg _ hn _ hn'
    have hXr : 0 ≤ X ^ (3 * r) := by positivity
    have hG1 : gN (Matrix.of p.1.2) ≤ C4 * X ^ (3 * r) := by
      refine hb1.trans ?_
      calc C3 * _ ≤ C3 * (c ^ (6 * r) * X ^ (3 * r)) := mul_le_mul_of_nonneg_left hYX hC3
        _ = (C3 * c ^ (6 * r)) * X ^ (3 * r) := by ring
        _ ≤ C4 * X ^ (3 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) hXr
    have hG2 : gN (Matrix.of p.2.2) ≤ C4 * X ^ (3 * r) := by
      refine hb2.trans ?_
      calc C3 * _ ≤ C3 * (c ^ (6 * r) * X ^ (3 * r)) := mul_le_mul_of_nonneg_left hYX hC3
        _ = (C3 * c ^ (6 * r)) * X ^ (3 * r) := by ring
        _ ≤ C4 * X ^ (3 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) hXr

    have hlet : ∀ s h : Mat k r, s = Matrix.of p.1.2 * Matrix.of p.1.1 ∨ s = Matrix.of p.2.2 * Matrix.of p.2.1 →
        s ∈ GV k r → ∀ Y : Mat k r, unitLie k r Y → ‖s⁻¹ * Y * s‖ ≤ Λ1 * X ^ (6 * r) := by
      intro s _ hs hsG Y hYu
      have hsb : gN s ≤ C4 * X ^ (3 * r) * c := by
        rcases hs with rfl | rfl
        · exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG1 hgh (Orb.gN_nonneg _) (by positivity))
        · exact (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _).trans (mul_le_mul hG2 hgh' (Orb.gN_nonneg _) (by positivity))
      refine (ad_bd hsG hYu).trans ?_
      calc NN * gN s ^ 2 ≤ NN * (C4 * X ^ (3 * r) * c) ^ 2 := by
            gcongr; exact Orb.gN_nonneg _
        _ = (NN * c ^ 2 * C4 ^ 2) * X ^ (6 * r) := by ring_nf
        _ ≤ Λ1 * X ^ (6 * r) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hΛX : 1 ≤ Λ1 * X ^ (6 * r) := one_le_mul_of_one_le_of_one_le hΛ1 (one_le_pow₀ hX1)
    have hPu : (u.map fun Y => ‖AdL p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ u.length := by
      have := list_prod_le (u.map fun Y => ‖AdL p Y‖) (Λ1 * X ^ (6 * r)) (by
        intro y hy
        obtain ⟨Y, hYu, rfl⟩ := List.mem_map.1 hy
        exact ⟨norm_nonneg _, hlet _ (Matrix.of p.1.1) (Or.inl rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sL_mem hp) Y (hu Y hYu)⟩)
      simpa using this
    have hPv : (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ v.length := by
      have := list_prod_le (v.map fun Y => ‖AdR p Y‖) (Λ1 * X ^ (6 * r)) (by
        intro y hy
        obtain ⟨Y, hYv, rfl⟩ := List.mem_map.1 hy
        exact ⟨norm_nonneg _, hlet _ (Matrix.of p.2.1) (Or.inr rfl) (Formalism.FourierDecayAlt.P.JFxDs2.sR_mem hp) Y (hv Y hYv)⟩)
      simpa using this
    have hP : (u.map fun Y => ‖AdL p Y‖).prod * (v.map fun Y => ‖AdR p Y‖).prod ≤ (Λ1 * X ^ (6 * r)) ^ m := by
      have hu0 : 0 ≤ (u.map fun Y => ‖AdL p Y‖).prod := List.prod_nonneg fun y hy => by
        obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _
      calc _ ≤ (Λ1 * X ^ (6 * r)) ^ u.length * (Λ1 * X ^ (6 * r)) ^ v.length :=
            mul_le_mul hPu hPv (List.prod_nonneg fun y hy => by
              obtain ⟨Y, _, rfl⟩ := List.mem_map.1 hy; exact norm_nonneg _) (by positivity)
        _ = (Λ1 * X ^ (6 * r)) ^ (u.length + v.length) := by rw [pow_add]
        _ ≤ (Λ1 * X ^ (6 * r)) ^ m := pow_le_pow_right₀ hΛX hl
    exact real_step X (gN (Matrix.of p.1.2)) (gN (Matrix.of p.2.2)) C4 Λ1 A A1 β _ m r hX1 hC4
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (Orb.n_mem_G hn')) hG1 hG2 hβ0 hβA
      hA1_def hΛ1 hP

end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem domination_of_scalar_majorant : Formalism.FourierDecayAlt.P.WeakThresholdClauses.NNMajW → Formalism.FourierDecayAlt.P.WeakThresholdClauses.JDomBoundW := by
  intro hN k r Wp Wq _ _ _ _ _ _ D A m F hThr hF K hK hKO
  obtain ⟨c, hc⟩ := hF
  have hc0 : 0 ≤ c := B4.cc_nonneg hc
  obtain ⟨b, hb, hbd⟩ := hN k r Wp Wq D A m hThr K hK hKO
  refine ⟨fun p => c * b p, hb.const_mul c, fun u v hu hv hl g hg => ?_⟩
  filter_upwards [hbd u v hu hv hl g hg, B5.ae_inSS D] with p hp hSS
  have hgG : g ∈ GV k r := (hKO hg).1
  have hx : sgs p g ∈ GV k r := B7.sgs_mem D hSS hgG
  have hpos : 0 < gN (sgs p g) := B6.gN_pos hx
  have hw := allLie_ad (sL_mem hSS) (sR_mem hSS) hu hv
  have hB := B4.bound_scaled hc (B4.lr (u.map (AdL p)) (v.map (AdR p))) (B4.lrt_lr _ _) hw
    (by rw [B4.length_lr]; simpa using hl) _ hx
  rw [← B4.dLR_eq, pn_lr] at hB
  have hApos : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hpos A
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      c * ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * gN (sgs p g) ^ (-A)) := by
    rw [Real.rpow_neg hpos.le]
    rw [mul_comm (gN (sgs p g) ^ A) _, ← le_div_iff₀ hApos] at hB
    calc _ ≤ _ := hB
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc ‖rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖
      ≤ ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ := B7.norm_rho_le D hSS _ g
    _ ≤ _ := h1
    _ ≤ c * b p := mul_le_mul_of_nonneg_left hp hc0

end Formalism.FourierDecayAlt.P.JFxDs2

namespace Formalism.FourierDecayAlt.P.JFxDs3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem orbital_measurability_weak_threshold : Formalism.FourierDecayAlt.P.WeakThresholdClauses.JDomMeasW := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hF u v hu hv hl g hg
  obtain ⟨c, hc⟩ := hF
  have hc0 : 0 ≤ c := cc_nonneg hc
  have hgG : g ∈ GV k r := hg.1
  have hA : 0 ≤ A := by
    have h1 := hThr.1
    have h2 : (0 : ℝ) ≤ 6 * (r : ℝ) * (m : ℝ) := by positivity
    linarith
  have hwu : ∀ x ∈ lr u v, unitLie k r x.2 := unit_lr' hu hv
  have hwt : LRt ((lr u v).map Prod.fst) := lrt_lr u v
  have hwl : (lr u v).length ≤ m := by rw [length_lr]; exact hl
  have hx : ContinuousOn (fun p => sgs p g) {p : SS k r | D.inSS p} := B6.conjugated_pair_continuous_on D g
  have hxG : ∀ p ∈ {p : SS k r | D.inSS p}, sgs p g ∈ GV k r := fun p hp => B7.sgs_mem D hp hgG
  have hmain : ContinuousOn (fun p => W ((lr u v).map (adM p)) F (sgs p g)) {p : SS k r | D.inSS p} := by
    intro p₀ hp₀
    have hAL : AllLie ((lr u v).map (adM p₀)) := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hy
      exact adM_lie hp₀ (hwu y' hy').1
    have hck : CkOn ((0 : ℕ) : ℕ∞) (GV k r) (W ((lr u v).map (adM p₀)) F) :=
      smooth_on_of_word_derivatives ((lr u v).map (adM p₀)) hAL 0 (ckOn_mono (by simpa using hwl) hc.1)
    have hsec : ContinuousWithinAt (fun p => W ((lr u v).map (adM p₀)) F (sgs p g)) {p : SS k r | D.inSS p} p₀ :=
      ((B6.continuousOn_of_contDiffOn_group hck).comp hx hxG) p₀ hp₀
    let Kf : SS k r → ℝ := fun p => 1 + ((lr u v).map fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖).sum
    let εf : SS k r → ℝ := fun p => ((lr u v).map fun x => ‖(adM p x).2 - (adM p₀ x).2‖).sum
    have hKc : ContinuousOn Kf {p : SS k r | D.inSS p} :=
      continuousOn_const.add (cont_sum _ (fun x p => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (lr u v)
        (fun x _ => (adM_cont D x).norm.add continuousOn_const))
    have hεc : ContinuousOn εf {p : SS k r | D.inSS p} :=
      cont_sum _ (fun x p => ‖(adM p x).2 - (adM p₀ x).2‖) (lr u v)
        (fun x _ => ((adM_cont D x).sub continuousOn_const).norm)
    have hε0 : εf p₀ = 0 := by simp [εf]
    let Bf : SS k r → ℝ := fun p => ((lr u v).length : ℝ) * (Kf p ^ m * εf p * c)
    have hBc : ContinuousWithinAt Bf {p : SS k r | D.inSS p} p₀ :=
      continuousWithinAt_const.mul ((((hKc p₀ hp₀).pow m).mul (hεc p₀ hp₀)).mul continuousWithinAt_const)
    have hB0 : Bf p₀ = 0 := by simp [Bf, hε0]
    have hd : Tendsto (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
      have hBt : Tendsto Bf (𝓝[{p : SS k r | D.inSS p}] p₀) (𝓝 0) := by
        have := hBc.tendsto; rwa [hB0] at this
      refine squeeze_zero_norm' ?_ hBt
      filter_upwards [self_mem_nhdsWithin] with p hp
      have hxp := hxG p hp
      have hK1 : 1 ≤ Kf p := le_add_of_nonneg_right (List.sum_nonneg (by
        intro y hy
        obtain ⟨y', _, rfl⟩ := List.mem_map.mp hy
        positivity))
      have hT := tele hc hc0 hK1 (adM p) (adM p₀) (lr u v) [] (by simp)
        (by
          intro x hx
          have hmK := le_sum_map (fun x => ‖(adM p x).2‖ + ‖(adM p₀ x).2‖) (fun _ => by positivity) (lr u v) hx
          have hmε := le_sum_map (fun x => ‖(adM p x).2 - (adM p₀ x).2‖) (fun _ => norm_nonneg _) (lr u v) hx
          refine ⟨rfl, rfl, adM_lie hp (hwu x hx).1, adM_lie hp₀ (hwu x hx).1, ?_, ?_, hmε⟩
          · have := norm_nonneg (adM p₀ x).2
            show ‖(adM p x).2‖ ≤ Kf p
            simp only [Kf]; linarith
          · have := norm_nonneg (adM p x).2
            show ‖(adM p₀ x).2‖ ≤ Kf p
            simp only [Kf]; linarith)
        (by simpa using hwt) (by simpa using hwl) _ hxp
      simp only [List.nil_append] at hT
      have h1 : 1 ≤ gN (sgs p g) ^ A := Real.one_le_rpow (BetaSesquilinearity.gN_ge_one hxp) hA
      calc ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖
          ≤ gN (sgs p g) ^ A * ‖W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)‖ :=
            le_mul_of_one_le_left (norm_nonneg _) h1
        _ ≤ Bf p := hT
    have hdc : ContinuousWithinAt
        (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g))
        {p : SS k r | D.inSS p} p₀ := by
      have e0 : (fun p => W ((lr u v).map (adM p)) F (sgs p g) - W ((lr u v).map (adM p₀)) F (sgs p g)) p₀ = 0 :=
        sub_self _
      unfold ContinuousWithinAt
      rw [e0]
      exact hd
    refine (hdc.add hsec).congr (fun p _ => ?_) ?_
    · simp
    · simp
  have hΦ : ContinuousOn (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) {p : SS k r | D.inSS p} := by
    have e : (fun p => rho D p (dLR (u.map (AdL p)) (v.map (AdR p)) F) g) =
        fun p => B6.Sd D p (W ((lr u v).map (adM p)) F (sgs p g)) := by
      funext p
      rw [B6.rho_eq, dLR_eq, lr_ad]
    rw [e]
    exact (B6.Sd_continuousOn D).clm_apply hmain
  have := hΦ.aestronglyMeasurable (μ := D.μSS) (B6.measurableSet_inSS D)
  have hr : D.μSS.restrict {p | D.inSS p} = D.μSS := Measure.restrict_eq_self_of_ae_mem (B5.ae_inSS D)
  rwa [hr] at this

end Formalism.FourierDecayAlt.P.JFxDs3

namespace Formalism.FourierDecayAlt.P.WeakDominationWordBounds

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
  Formalism.FourierDecayAlt.P.LetterPairRecursion

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_derivative_words_weak : Formalism.FourierDecayAlt.P.WeakThresholdClauses.JWordsW := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC
  have hDom1 := Formalism.FourierDecayAlt.P.JFxDs3.orbital_measurability_weak_threshold k r Wp Wq D A m F hThr hCC
  have hDom2 := Formalism.FourierDecayAlt.P.JFxDs2.domination_of_scalar_majorant Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.scalar_majorant_weak_threshold k r Wp Wq D A m F hThr hCC
  obtain ⟨c, hc⟩ := hCC
  have hFm : CkOn (m : ℕ∞) (GV k r) F := hc.1
  have hW := words_all D hFm hDom1 hDom2
  refine ⟨ck_all D hFm hDom1 hDom2, fun u v hu hv hl g hg => ?_⟩
  obtain ⟨bd, hbdI, hbd⟩ := hDom2 {g} isCompact_singleton (Set.singleton_subset_iff.2 hg)
  have hb := hbd u v hu hv hl g (Set.mem_singleton g)
  refine ⟨hbdI.norm.mono' ((continuous_xiP D).aestronglyMeasurable.smul (hDom1 u v hu hv hl g hg)) ?_, ?_⟩
  · filter_upwards [hb] with p hp
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_xiP D p)).trans (hp.trans (Real.le_norm_self _))
  · rw [hW u v hu hv hl g hg]
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp
    rw [dLR_rho D hp]

end Formalism.FourierDecayAlt.P.WeakDominationWordBounds

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_commutes_on_open_set : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)) (Θ : DiffOp k r Wp Wq)
    (UU : Set (Mat k r)), UU ⊆ Om k r D.z D.z' → opOrder Θ ≤ m → Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A m → InCC A m F →
    Commutes D UU Θ → ∀ g ∈ UU, opApply Θ (JF D F) g = JF D (opApply Θ F) g := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F Θ UU hUU ho hT hF hC g hgU
  have hg : g ∈ Om k r D.z D.z' := hUU hgU
  have hW := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak
  have hR := Formalism.FourierDecayAlt.P.rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast ho) hCk
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp F hCo g hgU]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

end Formalism.FourierDecayAlt.P
