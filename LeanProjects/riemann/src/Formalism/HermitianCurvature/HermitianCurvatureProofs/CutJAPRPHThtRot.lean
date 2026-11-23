import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH

noncomputable section

namespace TR

open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.P.TheSecStab

section block

variable {k : ℕ}

theorem img_perp_a {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : herm (Hb k) a a = -(T : ℂ))
    (hb : herm (Hb k) b b = -(T' : ℂ)) {x : Fin (k + 1) → ℂ} (hxb : herm (Hb k) x b = 0) :
    herm (Hb k) (gA k a T *ᵥ (gB k b T' *ᵥ x)) a = 0 := by
  have hne : ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hT').ne'
  have hne' : star ((Real.sqrt T' : ℝ) : ℂ) ≠ 0 := by
    rw [show star ((Real.sqrt T' : ℝ) : ℂ) = _ from Complex.conj_ofReal _]; exact hne
  have h1 : herm (Hb k) (gB k b T' *ᵥ x) (Pi.single (Fin.last k) 1) = 0 := by
    rw [← form_of_unitary (Hb k) (gB_spec k hT' hb).1, (gB_spec k hT' hb).2, herm_smul_right] at hxb
    exact (mul_eq_zero.1 hxb).resolve_left hne'
  have h2 := form_of_unitary (Hb k) (gA_spec k hT ha).1 (gB k b T' *ᵥ x)
    (((Real.sqrt T : ℝ) : ℂ) • Pi.single (Fin.last k) 1)
  rw [(gA_spec k hT ha).2] at h2
  rw [h2, herm_smul_right, h1, mul_zero]

theorem img_perp_0 {a b : Fin (k + 1) → ℂ} {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : herm (Hb k) a a = -(T : ℂ))
    (hb : herm (Hb k) b b = -(T' : ℂ)) {x : Fin (k + 1) → ℂ}
    (hx0 : herm (Hb k) x ((gB k b T')⁻¹ *ᵥ Pi.single 0 1) = 0) :
    herm (Hb k) (gA k a T *ᵥ (gB k b T' *ᵥ x)) (gA k a T *ᵥ Pi.single 0 1) = 0 := by
  rw [form_of_unitary (Hb k) (gA_spec k hT ha).1, ← DC.gB_adj hT' hb]
  exact hx0

end block

section big

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}

theorem stabilizer_fixes_section_embedding (hk : 1 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) {h : Q.Mx k r}
    (hfix : ∀ v, inWb k r v → herm (Hpk k r) v z = 0 → herm (Hpk k r) v (DC.EE k r z) = 0 → h *ᵥ v = v) :
    h * SSn.io0 k r z z' (theSection k r z z') ζ = SSn.io0 k r z z' (theSection k r z z') ζ := by
  have ha := SettingConstruction.herm_self k r z hz
  have hb := SettingConstruction.herm_self k r z' hz'
  rw [DC.section_embedding_eq_matrix hk hz hz' hT hT' hζ]
  ext i j
  obtain ⟨h1, h2, h3⟩ := DC.uu_facts (r := r) hk hz' hT' j
  have g2 : herm (Hb k) (wbPart k r (DC.uu k r z' j)) (wbPart k r z') = 0 := by
    rw [← DC.herm_of h1 hz']; exact h2
  have g3 : herm (Hb k) (wbPart k r (DC.uu k r z' j)) ((gB k (wbPart k r z') (Tz k r z'))⁻¹ *ᵥ Pi.single 0 1) = 0 := by
    rw [DC.EE', DC.herm_of h1 (inWb_jV _), wbPart_jV] at h3; exact h3
  have e := hfix (jV k r (gA k (wbPart k r z) (Tz k r z) *ᵥ (gB k (wbPart k r z') (Tz k r z') *ᵥ wbPart k r (DC.uu k r z' j))))
    (inWb_jV _)
    (by rw [DC.herm_of (inWb_jV _) hz, wbPart_jV]; exact img_perp_a hT hT' ha hb g2)
    (by rw [DC.EE, herm_jV]; exact img_perp_0 hT hT' ha hb g3)
  rw [Matrix.mul_apply]
  exact congrFun e i

end big

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
  {π : B.Mat k r → (Wp →L[ℂ] Wp)} {π' : B.Mat k r → (Wq →L[ℂ] Wq)}

theorem tht_iota_smul (F F' : Fin k → Fin (2 * r + k + 1) → ℂ) (a a' : Fin (2 * r + k + 1) → ℂ) (u : ℂ) {ι ι' : B.Mat k r}
    (h : ∀ q, ι' *ᵥ F' q = u • (ι *ᵥ F' q)) : tht k r z z' π π' F F' a a' ι' = u • tht k r z z' π π' F F' a a' ι := by
  unfold tht
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h q, P.Qx8.herm_smul_left', smul_smul]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tht_rot (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : Qr.IsRepW k r z π)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hR' : Qr.IsRepW k r z' π')
    {F F' : Fin k → Fin (2 * r + k + 1) → ℂ} (hF : Q.IsFrameOf k r [z] F) (hF' : Q.IsFrameOf k r [z'] F')
    {h h' : B.Mat k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (u : ℂ) (hu : conj u * u = 1)
    {a a' : Fin (2 * r + k + 1) → ℂ} {ι : B.Mat k r} (ha : h *ᵥ a = u • a) (ha' : h' *ᵥ a' = u • a') (hι : h * ι = ι)
    (hsc : ∀ q, h' *ᵥ F' q = u • F' q) (X : Wq →L[ℂ] Wp) :
    (π h).comp ((tht k r z z' π π' F F' a a' ι X).comp (π' h')) =
      conj u • tht k r z z' π π' F F' a a' ι ((π h).comp (X.comp (π' h'))) := by
  have uh' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hinv : (h'⁻¹)⁻¹ = h' := Matrix.nonsing_inv_nonsing_inv _ uh'
  have e2 : h'⁻¹ *ᵥ a' = conj u • a' := by
    have e := congrArg (fun v => conj u • (h'⁻¹ *ᵥ v)) ha'
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uh', Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, hu,
      one_smul] at e
    exact e.symm
  have e3 : ∀ q, (h * ι * h') *ᵥ F' q = u • (ι *ᵥ F' q) := by
    intro q
    rw [hι, ← Matrix.mulVec_mulVec, hsc q, Matrix.mulVec_smul]
  have key := TF.tht_eqv hz hT hR hz' hT' hR' hF hF' hh (P.LieBracketMultiplication.uw_inv hh') a a' ι X
  rw [hinv, ha, e2, TF.tht_phase hz hT hR hz' hT' hR' hF hF', tht_iota_smul F F' a a' u e3, smul_smul] at key
  rw [← key, FunLike.coe_smul, Pi.smul_apply]
  congr 1
  linear_combination (conj u) * hu

end gen

end TR

open Formalism.FourierDecayAlt.P.TheSec in
theorem theta_rotation_holds : ThtRot := by
  intro Wp Wq _ _ _ _ _ _ P Bs hPl hk hsec Bw Bw' hBw hBw' θ h h' hh hh' ζ hζ hν hfix hsc Xf
  obtain ⟨hOK, hz, hz', hTe, hTe', hty, hty'⟩ := hPl
  have hT : 0 < Tz P.k P.r Bs.z := hTe ▸ hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := hTe' ▸ hOK.T'_pos
  have hR : Qr.IsRepW P.k P.r Bs.z Bs.π := ⟨hty.2.1, hty.2.2.1⟩
  have hR' : Qr.IsRepW P.k P.r Bs.z' Bs.π' := ⟨hty'.2.1, hty'.2.2.1⟩
  have hk1 : 1 ≤ P.k := by omega
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by rw [hTe, hTe']; exact hζ
  have hu : conj (PS.eM θ) * PS.eM θ = 1 := by
    rw [← Complex.star_def, PS.star_eM]; exact PS.expPlus_mul_expMinus θ
  have hcu : conj (PS.eM θ) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.star_def, PS.star_eM]; rfl
  rw [hsec] at hν hfix ⊢
  obtain ⟨hE, hEz, _⟩ := DC.EE'_facts (r := P.r) hk1 hz' hT'
  have hν' : h' *ᵥ SSn.nu0' P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ =
      PS.eM θ • SSn.nu0' P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ := by
    rw [DC.nu0'_eq hk1 hz hz' hT hT' hζ', Matrix.mulVec_neg, smul_neg]
    exact congrArg Neg.neg (hsc _ hE hEz)
  have hι : h * SSn.io0 P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ =
      SSn.io0 P.k P.r Bs.z Bs.z' (theSection P.k P.r Bs.z Bs.z') ζ := by
    refine TR.stabilizer_fixes_section_embedding hk1 hz hz' hT hT' hζ' ?_
    rw [DC.section_first_vector_eq hk1 hz hz' hT hT' hζ'] at hfix
    exact hfix
  rw [← hcu]
  exact TR.tht_rot hz hT hR hz' hT' hR' hBw hBw' hh hh' (PS.eM θ) hu hν hν' hι
    (fun q => hsc _ (TF.frame_inW hBw' q).1 (TF.frame_inW hBw' q).2) Xf

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.PH
