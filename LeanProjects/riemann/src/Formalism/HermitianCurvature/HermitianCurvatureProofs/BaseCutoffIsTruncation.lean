import Formalism.HermitianCurvature.StatementTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishingAtRelevantPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetClassEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FibreExpansionZeroFails
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.Topx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt.P.Dx3 in
theorem orbConv_common : ∃ c₃ : ℝ, 0 ≤ c₃ ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r D.z D.z' γ = C2.monoP w d → 0 < Gf k r D.z D.z' γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (Formalism.FourierDecayAlt.D.muR D γ w) θ ∧
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.InCC A 1 F →
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  refine ⟨16 * ((c₁ : ℝ) + 1), by positivity, ?_⟩
  intro k r Wp Wq _ _ _ _ D γ w d A hγ hd hZ hpos hA
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN
  set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc
  set M : ℝ := A / c - 2 * bN with hM
  have hmono : C2.IsMonomial (Zhat k r D.z D.z' γ) := ⟨w, d, hd, hZ⟩
  obtain ⟨CP, hCP, -⟩ := hPP k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono

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
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1 := by
    rw [hnn]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]
  have hMR : 2 * ((r : ℝ) + 1) ^ 2 < M := by
    rw [hM, hbN]; nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hA0 : 0 ≤ A := by
    have := div_nonneg_iff.mp (show 0 ≤ A / c by linarith)
    rcases this with h | h
    · exact h.1
    · linarith [h.2]

  have hG : P.Dx2.Rad.Good D γ w d := ⟨P.Dx2.Rad.exists_rho D hγ hpos hd hZ, P.Dx2.Rad.u_inj D hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good D hγ hd hG
  have := P.Dx2.OrbJ.sigmaF hR
  have hI := intR D hγ hd hG hMR
  set μR := Formalism.FourierDecayAlt.D.muR D γ w with hμR
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    simpa using (P.unitary_group_closed k r).one_mem
  have hcR : 0 < cR := by
    have := om_pos hR hM0 hI hone
    simpa [Om] using this

  obtain ⟨KW, hKW1, hKW⟩ := UW_bound D.z D.z_mem D.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := UW_bound D.z' D.z'_mem D.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  refine ⟨cut μR M, ⟨cut_meas M, cut_nonneg μR M, fun p hp => cut_norm hR hM0 hI p hp.2.1⟩, fun F hF => ?_⟩

  obtain ⟨sharpFunctionalExponent, hCC⟩ := hF
  set cF := max sharpFunctionalExponent 0 with hcF
  have hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ cF * B.gN g ^ (-A) := by
    intro g hg
    have h0 := hCC.2 [] [] (by simp) (by simp) (by simp) g hg
    have e : B.dLR [] [] F g = F g := rfl
    rw [e] at h0
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpw]
    calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := by ring
      _ ≤ sharpFunctionalExponent := h0
      _ ≤ cF := le_max_left _ _
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hCC.1
  set Kf := cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hKf
  have hmaj := (maj_int D (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul Kf
  refine Integrable.mono' hmaj ((cut_meas M).aestronglyMeasurable.smul (integrand_aesm D hγ hFc)) ?_
  filter_upwards [P.Dx2.OrbJ.ae_inSS D] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := geom D hγ hpos hCP hmono h2 h4
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem D ⟨h1, h2, h3, h4⟩ hγ
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
  have hθ : cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := cut_nonneg μR M p
  have hFv : ‖B.rho D p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) :=
    (P.B7.norm_rho_le D ⟨h1, h2, h3, h4⟩ F γ).trans (hFb _ hsgs)
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
  have hkey := key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR
    (le_max_right _ _) hCP0 hK10 hKγ0 hM hbN0 hA4
  rw [norm_smul, Real.norm_of_nonneg hθ0]
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [norm_smul, P.B7.norm_xi, one_mul]
  exact hkey

section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem hsInner_eq [FiniteDimensional ℂ Wq] (X Y : Wq →L[ℂ] Wp) :
    B.hsInner X Y = ∑ i, inner ℂ (Y (stdOrthonormalBasis ℂ Wq i)) (X (stdOrthonormalBasis ℂ Wq i)) := by
  simp [B.hsInner, B.hsVec, PiLp.inner_apply]

theorem hsInner_neg_left [FiniteDimensional ℂ Wq] (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (-X) Y = -B.hsInner X Y := by
  simp [hsInner_eq, inner_neg_right, Finset.sum_neg_distrib]

theorem hsInner_neg_right [FiniteDimensional ℂ Wq] (X Y : Wq →L[ℂ] Wp) :
    B.hsInner X (-Y) = -B.hsInner X Y := by
  simp [hsInner_eq, inner_neg_left, Finset.sum_neg_distrib]

theorem inCC_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A A' : ℝ} {m : ℕ}
    {F : B.Mat k r → E} (hAA : A' ≤ A) (h : B.InCC A m F) : B.InCC A' m F := by
  unfold B.InCC B.CCle at h ⊢
  obtain ⟨c, hc1, hc2⟩ := h
  refine ⟨c, hc1, fun u v hu hv hl g hg => ?_⟩
  have h1 : 1 ≤ B.gN g := by
    first
    | exact BetaSesquilinearity.gN_ge_one hg
    | exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    | exact Formalism.FourierDecayAlt.BetaSesquilinearity.gN_ge_one hg
  calc B.gN g ^ A' * ‖B.dLR u v F g‖ ≤ B.gN g ^ A * ‖B.dLR u v F g‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 hAA) (norm_nonneg _)
    _ ≤ c := hc2 u v hu hv hl g hg

theorem ckOn_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {UU : Set (B.Mat k r)}
    {f : B.Mat k r → E} (h : B.CkOn m UU f) : B.CkOn m UU (fun x => -f x) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
  exact ⟨U, fun x => -f' x, hU, hgU, hcd.neg, fun g hg hG => congrArg Neg.neg (heq g hg hG)⟩

def chi0 (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

theorem base_cutoff_is_truncation : C6.IsCut0 chi0 := by
  unfold C6.IsCut0
  refine ⟨?_, ⟨1 / 2, by norm_num, fun x hx => ?_⟩, fun x hx => ?_⟩
  · exact Real.smoothTransition.contDiff.comp (f := fun x : ℝ => 2 * x - 1) (by fun_prop)
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · exact Real.smoothTransition.one_of_one_le (by linarith)

end helpers

section diff

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def negT (T : B.DTerm k r Wp Wq) : B.DTerm k r Wp Wq where
  coef := fun x => -T.coef x
  coefAdj := fun x => -T.coefAdj x
  word := T.word
  word_lie := T.word_lie
  adj_id := fun x A B' => by
    simp only [ContinuousLinearMap.neg_apply, hsInner_neg_left, hsInner_neg_right, T.adj_id]

def diffOp (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) : B.DiffOp k r Wp Wq := Θ₁ ++ Θ₂.map negT

theorem opApply_diffOp (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (diffOp Θ₁ Θ₂) F g = B.opApply Θ₁ F g - B.opApply Θ₂ F g := by
  have key : ∀ l : B.DiffOp k r Wp Wq,
      ((l.map negT).map fun T => T.coef g (B.Rw T.word F g)).sum
        = -(l.map fun T => T.coef g (B.Rw T.word F g)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, ih, neg_add]
      simp [negT]
  unfold B.opApply diffOp
  rw [List.map_append, List.sum_append, key, sub_eq_add_neg]

theorem foldr_max_append (l₁ l₂ : List ℕ) :
    (l₁ ++ l₂).foldr max 0 = max (l₁.foldr max 0) (l₂.foldr max 0) := by
  induction l₁ with
  | nil => simp
  | cons a l ih => simp [ih, max_assoc]

theorem opOrder_diffOp (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) :
    B.opOrder (diffOp Θ₁ Θ₂) = max (B.opOrder Θ₁) (B.opOrder Θ₂) := by
  unfold B.opOrder diffOp
  rw [List.map_append, foldr_max_append, List.map_map]
  rfl

theorem rho_sub (D : B.RealPlaceData k r Wp Wq) (p : B.SS k r) (F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.rho D p (fun x => F₁ x - F₂ x) g = B.rho D p F₁ g - B.rho D p F₂ g := by
  simp [B.rho, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

theorem epart_left {nf nf' : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (fib' : Fin nf' → B.Mat k r → C6.EndH Wp Wq) (es : List (Fin nf × List (B.Mat k r))) (g : B.Mat k r) :
    C6.Epart (Fin.append fib fib') (es.map fun e => (Fin.castAdd nf' e.1, e.2)) g = C6.Epart fib es g := by
  simp [C6.Epart, Function.comp_def, Fin.append_left]

theorem epart_right {nf nf' : ℕ} (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq)
    (fib' : Fin nf' → B.Mat k r → C6.EndH Wp Wq) (es : List (Fin nf' × List (B.Mat k r))) (g : B.Mat k r) :
    C6.Epart (Fin.append fib fib') (es.map fun e => (Fin.natAdd nf e.1, e.2)) g = C6.Epart fib' es g := by
  simp [C6.Epart, Function.comp_def, Fin.append_right]

theorem inDDPlus_diff (D : B.RealPlaceData k r Wp Wq) {nf nf' : ℕ} {fib : Fin nf → B.Mat k r → C6.EndH Wp Wq}
    {fib' : Fin nf' → B.Mat k r → C6.EndH Wp Wq} {L : Finset (Fin (r + 2))} {o κ o' κ' : ℕ}
    {Θ₁ Θ₂ : B.DiffOp k r Wp Wq} (h₁ : C6.InDDPlus D fib L o κ Θ₁) (h₂ : C6.InDDPlus D fib' L o' κ' Θ₂) :
    C6.InDDPlus D (Fin.append fib fib') L (max o o') (max κ κ') (diffOp Θ₁ Θ₂) := by
  unfold C6.InDDPlus at h₁ h₂ ⊢
  obtain ⟨hs₁, hc₁, ht₁⟩ := h₁
  obtain ⟨hs₂, hc₂, ht₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rcases List.mem_append.1 hT with hT | hT
    · exact hs₁ T hT
    · obtain ⟨T₂, hT₂, rfl⟩ := List.mem_map.1 hT
      exact ⟨ckOn_neg (hs₂ T₂ hT₂).1, ckOn_neg (hs₂ T₂ hT₂).2⟩
  · intro p hp f hf g hg
    have mono : ∀ (m m' : ℕ∞), m' ≤ m → B.CkOn m (B.GV k r) f → B.CkOn m' (B.GV k r) f := by
      intro m m' hm h g₀ hg₀
      obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
      exact ⟨U, f', hU, hgU, hcd.of_le (by exact_mod_cast hm), heq⟩
    rw [opOrder_diffOp] at hf
    have e1 := hc₁ p hp f (mono _ _ (by exact_mod_cast le_max_left _ _) hf) g hg
    have e2 := hc₂ p hp f (mono _ _ (by exact_mod_cast le_max_right _ _) hf) g hg
    have hfun : B.opApply (diffOp Θ₁ Θ₂) f = fun x => B.opApply Θ₁ f x - B.opApply Θ₂ f x := by
      funext x
      exact opApply_diffOp Θ₁ Θ₂ f x
    rw [opApply_diffOp, e1, e2, hfun, rho_sub]
  · intro T hT
    rcases List.mem_append.1 hT with hT | hT
    · obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hco⟩ := ht₁ T hT
      refine ⟨P, a, b, c, es.map fun e => (Fin.castAdd nf' e.1, e.2), ?_, hab, ?_, ?_, ?_⟩
      · obtain ⟨q, hq, hqe⟩ := hP
        exact ⟨q, hq.trans (le_max_left _ _), hqe⟩
      · simp only [List.map_map, Function.comp_def]
        exact hlen.trans (le_max_left _ _)
      · intro e he X hX
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        exact hlie e' he' X hX
      · intro g hg
        rw [hco g hg, epart_left]
    · obtain ⟨T₂, hT₂, rfl⟩ := List.mem_map.1 hT
      obtain ⟨P, a, b, c, es, hP, hab, hlen, hlie, hco⟩ := ht₂ T₂ hT₂
      refine ⟨fun g => -P g, a, b, c, es.map fun e => (Fin.natAdd nf e.1, e.2), ?_, hab, ?_, ?_, ?_⟩
      · obtain ⟨q, hq, hqe⟩ := hP
        refine ⟨-q, ?_, fun g => ?_⟩
        · rw [MvPolynomial.totalDegree_neg]
          exact hq.trans (le_max_right _ _)
        · rw [map_neg, ← hqe g]
      · simp only [List.map_map, Function.comp_def]
        exact hlen.trans (le_max_right _ _)
      · intro e he X hX
        obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
        exact hlie e' he' X hX
      · intro g hg
        show -T₂.coef g = _
        rw [hco g hg, epart_right]
        simp [neg_mul, neg_smul]

end diff

def LiftRadialOp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) P.r)
    (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (Θ Θ' : Top.TopLift P.k P.r Wp Wq),
    1 ≤ P.r → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → Top.IsTopLift P Bs L st Θ → Top.IsTopLift P Bs L st Θ' →
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (Dop Dop' : B.DiffOp P.k P.r Wp Wq),
      B.SmoothCoef (C6.domL Bs ∅) Dop → B.Commutes Bs (C6.domL Bs ∅) Dop →
      B.SmoothCoef (C6.domL Bs ∅) Dop' → B.Commutes Bs (C6.domL Bs ∅) Dop' →
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL Bs ∅, Θ.Θ w e F g = B.opApply Dop F g) →
      (∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ∀ g ∈ C6.domL Bs ∅, Θ'.Θ w e F g = B.opApply Dop' F g) →
      ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
        B.CkOn ((max (B.opOrder Dop) (B.opOrder Dop') : ℕ) : ℕ∞) (C6.bigPos Bs) J →
        C6.EquivOn Bs (C6.bigPos Bs) J → ∀ g ∈ C6.bigPos Bs, B.opApply Dop J g = B.opApply Dop' J g

theorem thr_arith {c₃ CV R Nn : ℝ} (hc₃ : 0 ≤ c₃) (hCV : 8 * c₃ ≤ CV) (hR : 1 ≤ R) (hN : 1 ≤ Nn) :
    c₃ * (R + 1) ^ 2 * (R * Nn + 1) ≤ R * (CV * (R ^ 3 * Nn + Nn ^ 2 + R ^ 4)) := by
  have hR0 : 0 ≤ R := by linarith
  have hN0 : 0 ≤ Nn := by linarith
  have hRN : 1 ≤ R * Nn := by nlinarith
  have h1 : (R + 1) ^ 2 ≤ 4 * R ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * R + 1) (sub_nonneg.2 hR)]
  have h2 : R * Nn + 1 ≤ 2 * (R * Nn) := by linarith
  have h3 : c₃ * (R + 1) ^ 2 * (R * Nn + 1) ≤ c₃ * (4 * R ^ 2) * (2 * (R * Nn)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 hc₃) h2 (by linarith) (mul_nonneg hc₃ (by positivity))
  have hpos : 0 ≤ R ^ 3 * Nn + Nn ^ 2 + R ^ 4 := by positivity
  have h4 : 8 * c₃ * (R ^ 3 * Nn + Nn ^ 2 + R ^ 4) ≤ CV * (R ^ 3 * Nn + Nn ^ 2 + R ^ 4) :=
    mul_le_mul_of_nonneg_right hCV hpos
  have h5 : c₃ * (4 * R ^ 2) * (2 * (R * Nn)) ≤ R * (8 * c₃ * (R ^ 3 * Nn + Nn ^ 2 + R ^ 4)) := by
    nlinarith [mul_nonneg (mul_nonneg hc₃ (pow_nonneg hR0 3)) (mul_nonneg hN0 (sub_nonneg.2 hR)),
      mul_nonneg hc₃ (mul_nonneg hR0 (sq_nonneg Nn)), mul_nonneg hc₃ (pow_nonneg hR0 5)]
  calc c₃ * (R + 1) ^ 2 * (R * Nn + 1) ≤ c₃ * (4 * R ^ 2) * (2 * (R * Nn)) := h3
    _ ≤ R * (8 * c₃ * (R ^ 3 * Nn + Nn ^ 2 + R ^ 4)) := h5
    _ ≤ R * (CV * (R ^ 3 * Nn + Nn ^ 2 + R ^ 4)) := mul_le_mul_of_nonneg_left h4 hR0

theorem cutAll_empty {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (χ₀ : ℝ → ℝ) (de : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : C6.cutAll D χ₀ de ∅ F = F := by
  funext g
  simp [C6.cutAll, C6.chiAll]

theorem topLiftVanishing_of_density_of_radialOp (hDens : C6.LemmaDens) (hRad : LiftRadialOp) : Top.TopLiftVanishing := by
  intro Cb hCb
  obtain ⟨C₀v, hC₀v⟩ := Formalism.FourierDecayAlt.P.vanishing_at_relevant_points Formalism.FourierDecayAlt.P.orbital_integral_commutes_large hDens Cb hCb
  obtain ⟨c₃, hc₃, hConv⟩ := orbConv_common
  obtain ⟨C₀b, hC₀b⟩ := Formalism.FourierDecayAlt.P.c6_budgetArith_proof Cb (⌈8 * c₃⌉₊ + 1) hCb
  refine ⟨max C₀v C₀b, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs ν' m₀ L st Θ Θ' hr hpl _hbf hT hT' hD hD' w As A ε F h1 h2 _hAu hA hcl e p _hp
  obtain ⟨nf, fib, o, κ, Dop, hfib, hDD, ho, hκ, hΘ⟩ := hD w e
  obtain ⟨nf', fib', o', κ', Dop', hfib', hDD', ho', hκ', hΘ'⟩ := hD' w e
  obtain ⟨hε, -, hclm, hsupp⟩ := hcl
  have hrr : (1 : ℝ) ≤ P.r := by exact_mod_cast hr
  have hAs0 : (0 : ℝ) ≤ As := Nat.cast_nonneg _
  have hr4 : (0 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 4 := by positivity
  have hAv : C₀v * ((P.r : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hr4) hAs0) hA
  have hAb : C₀b * ((P.r : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hr4) hAs0) hA
  have hn2 : 2 * P.r + 2 ≤ 2 * P.r + P.k + 1 := by have := Bs.k_pos; omega
  have hn1 : (1 : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * P.r + P.k + 1)
  have hCV : 8 * c₃ ≤ ((⌈8 * c₃⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (8 * c₃); push_cast; linarith

  have hdecay : ∀ (nf₁ : ℕ) (fib₁ : Fin nf₁ → B.Mat P.k P.r → C6.EndH Wp Wq) (o₁ κ₁ : ℕ)
      (Dop₁ : B.DiffOp P.k P.r Wp Wq), (∀ j, C6.FibBound Bs (fib₁ j)) → C6.InDDPlus Bs fib₁ ∅ o₁ κ₁ Dop₁ →
      (o₁ : ℝ) ≤ Cb * (w.length : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) →
      (κ₁ : ℝ) ≤ Cb * ((P.r : ℝ) + 1) * (o₁ : ℝ) →
      B.InCC (c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1)) 1 (B.opApply Dop₁ F) := by
    intro nf₁ fib₁ o₁ κ₁ Dop₁ hf₁ hd₁ ho₁ hκ₁
    have hB := Formalism.FourierDecayAlt.P.budget_class_estimate P.k P.r Wp Wq Bs nf₁ fib₁ ∅ o₁ κ₁ Dop₁ ε 1 chi0 A F hε one_pos
      base_cutoff_is_truncation hf₁ hd₁ hclm hsupp 1
    rw [cutAll_empty] at hB
    refine inCC_le ?_ hB
    have hBA := hC₀b P.r (2 * P.r + P.k + 1) w.length o₁ κ₁ As A hr hn2 h1 h2 ho₁ hκ₁ hAb
    have hthr := thr_arith hc₃ hCV hrr hn1
    have hmm : (1 : ℝ) ≤ (C6.mmV (⌈8 * c₃⌉₊ + 1) P.r : ℝ) := by
      unfold C6.mmV
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hkey : 3 * ((P.r : ℝ) + 1) * (((1 : ℕ) : ℝ) + o₁) ≤
        3 * ((P.r : ℝ) + 1) * ((C6.mmV (⌈8 * c₃⌉₊ + 1) P.r : ℝ) + o₁) :=
      mul_le_mul_of_nonneg_left (by push_cast; linarith) (by positivity)
    unfold C6.AV at hBA
    push_cast at hBA hthr hkey ⊢
    linarith

  unfold D.vecV
  by_cases h : D.IsLocPt p (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r p
  swap
  · rw [dif_neg h, dif_neg h]
  rw [dif_pos h, dif_pos h]
  by_cases h' : ∃ γ ∈ B.GV P.k P.r, Zhat P.k P.r Bs.z Bs.z' γ = D.ptMatN p (P.r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
  swap
  · rw [dif_neg h', dif_neg h']
  rw [dif_pos h', dif_pos h']
  obtain ⟨hγ, hZ, -⟩ := h'.choose_spec
  obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' p (P.r + 1) h.1.2 h.1.1
  have hZm := hZ.trans hmono
  have hrel : C6.IsRelevant Bs h'.choose := Formalism.FourierDecayAlt.P.relevant_points_holds P.k P.r Wp Wq Bs p h'.choose h.1 hγ hZ
  have hGpos : 0 < Gf P.k P.r Bs.z Bs.z' h'.choose := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec P.k P.r Bs.z Bs.z' p h'.choose h.1 hZ]; exact h.2
  obtain ⟨O, hOμ, hOJ⟩ := Formalism.FourierDecayAlt.P.orbital_data_of_parts Formalism.FourierDecayAlt.P.radial_measure_is_haar Formalism.FourierDecayAlt.P.orbital_integral_indep_choice P.k P.r Wp Wq Bs
    h'.choose _ _ hrel hd hZm
  obtain ⟨θ, hθ, hθint⟩ := hConv P.k P.r Wp Wq Bs h'.choose _ _ _ hγ hd hZm hGpos le_rfl

  have horb : ∀ (G₁ G₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), (∀ g ∈ C6.domL Bs ∅, G₁ g = G₂ g) →
      ∀ᵐ q ∂Bs.μSS, D.orbIntegrand Bs h'.choose G₁ q = (1 : ℂ) • D.orbIntegrand Bs h'.choose G₂ q := by
    intro G₁ G₂ hG
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with q hq
    have hm : B.sgs q h'.choose ∈ C6.domL Bs ∅ :=
      ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hq hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hq]; exact hGpos, by simp⟩
    simp only [D.orbIntegrand, B.rho, hG _ hm, one_smul]
  rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose _ _ _ 1 (horb _ _ (hΘ F)),
    Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose _ _ _ 1 (horb _ _ (hΘ' F)), one_smul, one_smul]
  have hi₁ := hθint _ (hdecay _ fib _ _ Dop hfib hDD ho hκ)
  have hi₂ := hθint _ (hdecay _ fib' _ _ Dop' hfib' hDD' ho' hκ')
  have hθO : D.IsNormCut Bs h'.choose O.μR θ := by rw [hOμ]; exact hθ
  rw [← hOJ _ ⟨θ, hθO, hi₁⟩, ← hOJ _ ⟨θ, hθO, hi₂⟩]
  have hw₁ := O.weil (B.opApply Dop F) θ hθO.1 hθO.2.1 hθO.2.2 hi₁
  have hw₂ := O.weil (B.opApply Dop' F) θ hθO.1 hθO.2.1 hθO.2.2 hi₂

  have hΔ := inDDPlus_diff Bs hDD hDD'
  have hRZ : C6.RadZero Bs (diffOp Dop Dop') := by
    intro J hJ hE g hg
    rw [opApply_diffOp, sub_eq_zero]
    exact hRad Wp Wq P Bs L st Θ Θ' hr hpl hT hT' w e Dop Dop' hDD.1 hDD.2.1 hDD'.1 hDD'.2.1 hΘ hΘ' J
      (by rw [← opOrder_diffOp]; exact hJ) hE g hg
  have hfibA : ∀ j, C6.FibBound Bs (Fin.append fib fib' j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hfib i
    · rw [Fin.append_right]; exact hfib' i
  have hoΔ : ((max o o' : ℕ) : ℝ) ≤ Cb * (w.length : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_max]; exact max_le ho ho'
  have hκΔ : ((max κ κ' : ℕ) : ℝ) ≤ Cb * ((P.r : ℝ) + 1) * ((max o o' : ℕ) : ℝ) := by
    rw [Nat.cast_max, Nat.cast_max]
    have hc0 : 0 ≤ Cb * ((P.r : ℝ) + 1) := by positivity
    exact max_le (le_trans hκ (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0))
      (le_trans hκ' (mul_le_mul_of_nonneg_left (le_max_right _ _) hc0))
  have hV := hC₀v P.k P.r Wp Wq Bs (nf + nf') (Fin.append fib fib') ∅ (max o o') (max κ κ') w.length As
    (diffOp Dop Dop') ε 1 chi0 A F h'.choose O hr hε one_pos base_cutoff_is_truncation hfibA hΔ hRZ hoΔ hκΔ h1 h2 hAv hclm
    hsupp hrel hGpos
  rw [cutAll_empty] at hV
  have e3 : B.opApply (diffOp Dop Dop') F = fun x => B.opApply Dop F x - B.opApply Dop' F x :=
    funext fun x => opApply_diffOp Dop Dop' F x
  have hsplit : (fun q => θ q • D.orbIntegrand Bs h'.choose (B.opApply (diffOp Dop Dop') F) q) =
      fun q => θ q • D.orbIntegrand Bs h'.choose (B.opApply Dop F) q -
        θ q • D.orbIntegrand Bs h'.choose (B.opApply Dop' F) q := by
    funext q
    simp only [D.orbIntegrand, e3, rho_sub, smul_sub]
  have hi₃ : Integrable (fun q => θ q • D.orbIntegrand Bs h'.choose (B.opApply (diffOp Dop Dop') F) q)
      Bs.μSS := by
    rw [hsplit]; exact hi₁.sub hi₂
  have hw₃ := O.weil (B.opApply (diffOp Dop Dop') F) θ hθO.1 hθO.2.1 hθO.2.2 hi₃
  rw [hV] at hw₃
  change ∫ q, θ q • D.orbIntegrand Bs h'.choose (B.opApply (diffOp Dop Dop') F) q ∂Bs.μSS = 0 at hw₃
  rw [hsplit, integral_sub hi₁ hi₂, sub_eq_zero] at hw₃
  rw [← hw₁, ← hw₂]
  exact hw₃

end Formalism.FourierDecayAlt.P.Topx2
