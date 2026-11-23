import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.RSEigen

open Ad3 Ad3.R

def pr (μ : Measure G2) (𝓕 : Set G2) (φ : G2 → ℂ) (A B : G2) : ℂ :=
  ∫ g in 𝓕 ∩ band, φ (g * A) * conj (φ (g * B)) ∂μ

section Pairing

variable {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {φ : G2 → ℂ}

theorem trans_cont (hc : Continuous φ) (A B : G2) :
    Continuous fun g => φ (g * A) * conj (φ (g * B)) :=
  (hc.comp (continuous_id.mul continuous_const)).mul
    (Complex.continuous_conj.comp (hc.comp (continuous_id.mul continuous_const)))

theorem trans_bdd (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (A B : G2) :
    ∃ C : ℝ, ∀ g, ‖φ (g * A) * conj (φ (g * B))‖ ≤ C := by
  obtain ⟨C, hC⟩ := hb
  refine ⟨C * C, fun g => ?_⟩
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

theorem trans_integrable (hS : Set0 μ 𝓕 mK 𝓓) (hc : Continuous φ) (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (A B : G2) :
    Integrable (fun g => φ (g * A) * conj (φ (g * B))) (μ.restrict (𝓕 ∩ band)) := by
  haveI : IsFiniteMeasure (μ.restrict (𝓕 ∩ band)) := ⟨by simpa using hS.vol⟩
  obtain ⟨C, hC⟩ := trans_bdd hb A B
  exact Integrable.of_bound (trans_cont hc A B).aestronglyMeasurable C (ae_of_all _ hC)

theorem mul_conj_circle (w : Circle) : (w : ℂ) * conj (w : ℂ) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]; simp

theorem trans_linv (hl : LInv φ) (A B : G2) : LInv fun g => φ (g * A) * conj (φ (g * B)) := by
  intro γ g
  simp only [mul_assoc]
  rw [hl, hl]

theorem trans_cinv {ω : HeckeCharacter ℚ} (hz : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (A B : G2) :
    CInv fun g => φ (g * A) * conj (φ (g * B)) := by
  intro z g
  have hw := mul_conj_circle (ω.toIdele z)
  simp only [mul_assoc, hz, map_mul]
  calc _ = ((ω.toIdele z : ℂ) * conj (ω.toIdele z : ℂ)) * (φ (g * A) * conj (φ (g * B))) := by ring
    _ = _ := by rw [hw, one_mul]

theorem pr_trans (hS : Set0 μ 𝓕 mK 𝓓) (hG : G1) {ω : HeckeCharacter ℚ} (hc : Continuous φ)
    (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (hl : LInv φ)
    (hz : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (A B h : G2) :
    pr μ 𝓕 φ (h * A) (h * B) = pr μ 𝓕 φ A B := by
  have := (hG μ 𝓕 mK 𝓓 hS _ (trans_cont hc A B) (trans_bdd hb A B) (trans_linv hl A B)).1
    (trans_cinv hz A B) h
  simp only [mul_assoc] at this
  simpa only [pr, mul_assoc] using this

theorem pr_right {Y X : G2} {w : ℂ} (hX : ∀ g, φ (g * X) = w * φ g) :
    pr μ 𝓕 φ (Y * X) 1 = w * pr μ 𝓕 φ Y 1 := by
  have : ∀ g, φ (g * (Y * X)) * conj (φ (g * 1)) = w * (φ (g * Y) * conj (φ (g * 1))) := fun g => by
    rw [← mul_assoc g, hX]; ring
  simp only [pr, this]
  exact integral_const_mul _ _

theorem pr_left (hS : Set0 μ 𝓕 mK 𝓓) (hG : G1) {ω : HeckeCharacter ℚ} (hc : Continuous φ)
    (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (hl : LInv φ)
    (hz : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) {Y X : G2} {w : ℂ} (hw : ‖w‖ = 1)
    (hX : ∀ g, φ (g * X) = w * φ g) :
    pr μ 𝓕 φ (X * Y) 1 = w * pr μ 𝓕 φ Y 1 := by
  have h1 := pr_trans hS hG hc hb hl hz Y X⁻¹ X
  rw [mul_inv_cancel] at h1
  rw [h1]
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; simp
  have hinv : ∀ g, φ (g * X⁻¹) = w⁻¹ * φ g := fun g => by
    have := hX (g * X⁻¹)
    rw [inv_mul_cancel_right] at this
    rw [this]; field_simp
  have hcw : conj (w⁻¹) = w := by
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_left hww
  have : ∀ g, φ (g * Y) * conj (φ (g * X⁻¹)) = w * (φ (g * Y) * conj (φ (g * 1))) := fun g => by
    rw [hinv, map_mul, hcw, mul_one]; ring
  simp only [pr, this]
  exact integral_const_mul _ _

theorem pr_zero (hS : Set0 μ 𝓕 mK 𝓓) (hG : G1) {ω : HeckeCharacter ℚ} (hc : Continuous φ)
    (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (hl : LInv φ)
    (hz : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) {Y X X' : G2} {w w' : ℂ} (hw : ‖w‖ = 1)
    (hX : ∀ g, φ (g * X) = w * φ g) (hX' : ∀ g, φ (g * X') = w' * φ g) (hcomm : X * Y = Y * X')
    (hne : w ≠ w') : pr μ 𝓕 φ Y 1 = 0 := by
  have h1 := pr_left (Y := Y) hS hG hc hb hl hz hw hX
  rw [hcomm, pr_right hX'] at h1
  have : (w' - w) * pr μ 𝓕 φ Y 1 = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

theorem sum_expand {α : Type} (hS : Set0 μ 𝓕 mK 𝓓) (hc : Continuous φ)
    (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (B : Finset α) (t : α → G2) (Λ : ℂ)
    (hsum : ∀ g, ∑ b ∈ B, φ (g * t b) = Λ * φ g) :
    Λ * conj Λ * pr μ 𝓕 φ 1 1 = ∑ b ∈ B, ∑ b' ∈ B, pr μ 𝓕 φ (t b) (t b') := by
  have key : ∀ g, Λ * conj Λ * (φ (g * 1) * conj (φ (g * 1))) =
      ∑ b ∈ B, ∑ b' ∈ B, φ (g * t b) * conj (φ (g * t b')) := fun g => by
    rw [← Finset.sum_mul_sum, ← map_sum, hsum, map_mul, mul_one]; ring
  calc Λ * conj Λ * pr μ 𝓕 φ 1 1
      = ∫ g in 𝓕 ∩ band, Λ * conj Λ * (φ (g * 1) * conj (φ (g * 1))) ∂μ :=
        (integral_const_mul _ _).symm
    _ = ∫ g in 𝓕 ∩ band, ∑ b ∈ B, ∑ b' ∈ B, φ (g * t b) * conj (φ (g * t b')) ∂μ := by simp only [key]
    _ = ∑ b ∈ B, ∫ g in 𝓕 ∩ band, ∑ b' ∈ B, φ (g * t b) * conj (φ (g * t b')) ∂μ :=
        integral_finset_sum _ fun b _ => integrable_finset_sum _ fun b' _ => trans_integrable hS hc hb _ _
    _ = _ := Finset.sum_congr rfl fun b _ =>
        integral_finset_sum _ fun b' _ => trans_integrable hS hc hb _ _

theorem pr_self_ne (hS : Set0 μ 𝓕 mK 𝓓) (hG : G1) {ω : HeckeCharacter ℚ} (hc : Continuous φ)
    (hb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) (hl : LInv φ)
    (hz : ∀ (z : Jd) g, φ (dg2 z z * g) = (ω.toIdele z : ℂ) * φ g) (h0 : φ ≠ 0) :
    pr μ 𝓕 φ 1 1 ≠ 0 := by
  set F : G2 → ℂ := fun g => ((‖φ g‖ : ℝ) : ℂ) with hF
  have hFc : Continuous F := Complex.continuous_ofReal.comp hc.norm
  have hFb : ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun g => by simpa [hF] using hC g⟩
  have hFl : LInv F := fun γ g => by simp only [hF, hl γ g]
  have hFz : CInv F := fun z g => by simp only [hF, hz, norm_mul, Circle.norm_coe, one_mul]
  have hF0 : F ≠ 0 := by
    intro h
    apply h0
    funext g
    have := congrFun h g
    simpa [hF] using this
  have := (hG μ 𝓕 mK 𝓓 hS F hFc hFb hFl).2.2 hFz hF0
  have heq : ∀ g, F g * conj (F g) = φ (g * 1) * conj (φ (g * 1)) := fun g => by
    simp only [hF, mul_one, Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simpa only [pr, heq] using this

end Pairing

section Local

theorem mem_integer_iff_ord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp, neg_nonpos]

theorem reps_ord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) {b b' : F} (hb : b ∈ B) (hb' : b' ∈ B) (hne : b ≠ b') :
    ord (((ϖ⁻¹ : Fˣ) : F) * (b - b')) = -1 := by
  obtain ⟨h1, hint, huniq⟩ := hR
  set y : F := ((ϖ⁻¹ : Fˣ) : F) * (b - b') with hy
  have hyO : y ∉ 𝒪[F] := by
    intro hmem
    apply hne
    refine (huniq b (hint b hb)).unique ⟨hb, ?_⟩ ⟨hb', hmem⟩
    simp
  have hy0 : y ≠ 0 := fun h => hyO (h ▸ zero_mem _)
  have hϖ0 : (ϖ : F) ≠ 0 := ϖ.ne_zero
  have hprod : (ϖ : F) * y = b - b' := by
    rw [hy, ← mul_assoc, Units.mul_inv, one_mul]
  have hmem : (ϖ : F) * y ∈ 𝒪[F] := by
    rw [hprod]; exact sub_mem (hint b hb) (hint b' hb')
  rw [mem_integer_iff_ord (mul_ne_zero hϖ0 hy0), ord_mul hϖ0 hy0, h1] at hmem
  rw [mem_integer_iff_ord hy0, not_le] at hyO
  omega

theorem upm_mul {F : Type} [Field F] (ϖ : Fˣ) (b b' : F) :
    upm ϖ b' * uni2 (((ϖ⁻¹ : Fˣ) : F) * (b - b')) = upm ϖ b := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upm, uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem loc_mul {v : Pl} {x y : GL (Fin 2) (Qv v)} {h h' : G2} (hx : IsLoc2 v x h) (hy : IsLoc2 v y h') :
    IsLoc2 v (x * y) (h * h') :=
  ⟨by rw [GroundTheory.Automorphic.Reduction.finAt_mul, hx.1, hy.1],
   fun v' hv => by rw [GroundTheory.Automorphic.Reduction.finAt_mul, hx.2.1 v' hv, hy.2.1 v' hv, one_mul],
   fun w => by rw [GroundTheory.Automorphic.Reduction.infAt_mul, hx.2.2 w, hy.2.2 w, one_mul]⟩

theorem loc_one (v : Pl) : IsLoc2 v 1 (1 : G2) :=
  ⟨by simpa using GroundTheory.Automorphic.Reduction.finAt_mul v (1 : G2) 1,
   fun v' _ => by simpa using GroundTheory.Automorphic.Reduction.finAt_mul v' (1 : G2) 1,
   fun w => by simpa using GroundTheory.Automorphic.Reduction.infAt_mul w (1 : G2) 1⟩

theorem loc_unique (hinj : ∀ g g' : G2, (∀ v, finAt v g = finAt v g') → (∀ w, infAt w g = infAt w g') → g = g')
    {v : Pl} {x : GL (Fin 2) (Qv v)} {h h' : G2} (hx : IsLoc2 v x h) (hx' : IsLoc2 v x h') : h = h' :=
  hinj h h' (fun v' => by
    by_cases e : v' = v
    · subst e; rw [hx.1, hx'.1]
    · rw [hx.2.1 v' e, hx'.2.1 v' e]) fun w => by rw [hx.2.2 w, hx'.2.2 w]

end Local

theorem wr_ne (k : ℕ) : WR k (-1) ≠ 0 := by
  unfold WR
  rw [if_pos (by simp)]
  exact Complex.ofReal_ne_zero.2 (mul_ne_zero (pow_ne_zero _ (by simp)) (Real.exp_ne_zero _))

theorem wh_zero (g : G2) : Wh 0 g = 0 := by
  simp [Wh]

theorem abs_eigenvalue_sq : B0 → C1 → U2 → G0 → G1 → F0b → F1 → F2 → F3 → F5 → F4 := by
  intro hB0 hC1 hU2 hG0 hG1 hF0b hF1 hF2 hF3 hF5 k N _ hk χ hχ f a hf ha ω φ hω hφ v hv
  obtain ⟨hloc, -, -, hinj, -⟩ := hB0
  obtain ⟨hstd, hres, hprime, -, -, hex, hunit⟩ := hloc v
  obtain ⟨hpar, -⟩ := hF1 k N χ f a hf ha.2.1 ω hω
  have hcond := (hF0b k N χ hχ hpar ω hω).bad v hv
  have hn : 1 ≤ N.factorization (pOf v) := hprime.factorization_pos_of_dvd (NeZero.ne N) hv
  have hHk : Hk k N a ω φ := hF3 k N hk χ hχ f a hf ha ω φ hω hφ
  have hF2' := hF2 k N hk χ hχ f a hf ha ω φ hω hφ
  obtain ⟨hbd, -⟩ := hF5 k N hk χ hχ f a hf ha ω φ hω hφ
  obtain ⟨μ, 𝓕, mK, 𝓓, hS⟩ := hG0
  choose ι hι using hex
  have hfn : ∀ g, LocFn v φ g (fun x => φ (g * ι x)) := fun g x h hx => by
    show φ (g * ι x) = _
    rw [loc_unique hinj (hι x) hx]
  have hT := fun g => hHk.bad v hv g _ (hfn g)
  have hι1 : ι 1 = 1 := loc_unique hinj (hι 1) (loc_one v)
  have hK : ∀ x d, GammaZeroLevelMembership (N.factorization (pOf v)) x d → ∀ g,
      φ (g * ι x) = ((localChar ω v d : ℂˣ) : ℂ) * φ g := fun x d hx g => by
    have := (hT g).1 x d hx 1
    simpa [hι1] using this
  obtain ⟨⟨ϖ, B, hR⟩, hcard, -⟩ := hC1 (Qv v) (localAdelicChar ℚ v) hstd
  have hsum : ∀ g, ∑ b ∈ B, φ (g * ι (upm ϖ b)) = lamOf k a v * φ g := fun g => by
    have := (hT g).2 ϖ B hR 1
    simpa [hι1] using this
  have hoff : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → pr μ 𝓕 φ (ι (upm ϖ b)) (ι (upm ϖ b')) = 0 := by
    intro b hb b' hb' hne
    obtain ⟨x, d, x', d', hx, hx', hcomm, hdne⟩ := hU2 (Qv v) (localAdelicChar ℚ v) hstd (localChar ω v) (hunit ω).1
      (by rw [hcond]; exact hn) _ (reps_ord hR hb hb' hne)
    rw [hcond] at hx hx'
    have hY : ι (upm ϖ b') * ι (uni2 (((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * (b - b'))) = ι (upm ϖ b) :=
      loc_unique hinj (loc_mul (hι _) (hι _)) (by rw [upm_mul]; exact hι _)
    have hcomm' : ι x * ι (uni2 (((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * (b - b'))) =
        ι (uni2 (((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * (b - b'))) * ι x' :=
      loc_unique hinj (loc_mul (hι _) (hι _)) (by rw [hcomm]; exact loc_mul (hι _) (hι _))
    have h2 := pr_trans hS hG1 hφ.cont hbd hφ.left hφ.cen (ι (uni2 (((ϖ⁻¹ : (Qv v)ˣ) : Qv v) * (b - b')))) 1 (ι (upm ϖ b'))
    rw [hY, mul_one] at h2
    rw [h2]
    exact pr_zero hS hG1 hφ.cont hbd hφ.left hφ.cen ((hunit ω).2 d) (hK x d hx) (hK x' d' hx') hcomm'
      fun h => hdne (Units.ext h)
  have hdiag : ∀ b, pr μ 𝓕 φ (ι (upm ϖ b)) (ι (upm ϖ b)) = pr μ 𝓕 φ 1 1 := fun b => by
    simpa using pr_trans hS hG1 hφ.cont hbd hφ.left hφ.cen 1 1 (ι (upm ϖ b))
  have h0 : φ ≠ 0 := by
    rintro rfl
    have h := hF2'.2.2.2 (-1)
    rw [wh_zero] at h
    exact wr_ne k h.symm
  have hne := pr_self_ne hS hG1 hφ.cont hbd hφ.left hφ.cen h0
  have hexp := sum_expand hS hφ.cont hbd B (fun b => ι (upm ϖ b)) (lamOf k a v) hsum
  have hdd : ∑ b ∈ B, ∑ b' ∈ B, pr μ 𝓕 φ (ι (upm ϖ b)) (ι (upm ϖ b')) = (B.card : ℂ) * pr μ 𝓕 φ 1 1 := by
    rw [Finset.sum_congr rfl (fun b hb => (Finset.sum_eq_single_of_mem b hb
      (fun b' hb' hne => hoff b hb b' hb' hne.symm)).trans (hdiag b))]
    simp
  have hfin := mul_right_cancel₀ hne (hexp.trans hdd)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hcard ϖ B hR, hres] at hfin
  exact_mod_cast hfin

end GlobalTheory.CompanionTheory.RSEigen
end
