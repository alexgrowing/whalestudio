import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM
open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RiemInt

open GlobalTheory.RosatiAH GlobalTheory.AppellHumbertTrivial

theorem im_hermForm_int {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : IsFactorAH u Hm χ) (l m : u.Λ) :
    ∃ n : ℤ, (hermForm Hm l m).im = n := by
  have hper : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hil : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have him : ⊤ ≤ (u.ex (0 + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have hlm : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h.2.2 l i 0 hi
  have h2 := h.2.2 m i _ hil
  have h3 := h.2.2 m i 0 hi
  have h4 := h.2.2 l i _ him
  have hne := u.fr_ne i _ hlm
  have hs : hermForm Hm m l = star (hermForm Hm l m) := by
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.1.eq, Matrix.dotProduct_mulVec]
  have hχl : χ l ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  have hχm : χ m ≠ 0 := norm_ne_zero_iff.1 (by rw [h.2.1]; exact one_ne_zero)
  rw [h2] at h1
  rw [h4, h1] at h3
  simp only [zero_add, zero_dotProduct, mul_zero] at h3 hne
  rw [add_comm (m : Fin g → ℂ) l] at h3
  unfold hermForm at hs ⊢
  rw [hs] at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h3
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h3
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h3 ⊢
  simp only [Complex.exp_add] at h3
  have he : Complex.exp (Real.pi * c) = Complex.exp (Real.pi * star c) := by
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hχl hχm)
      (Complex.exp_ne_zero (Real.pi / 2 * a))) (Complex.exp_ne_zero (Real.pi / 2 * b))) hne) ?_
    linear_combination h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  have hp := Real.pi_pos
  refine mul_left_cancel₀ (a := 2 * Real.pi) (by positivity) ?_
  linear_combination this

variable {g : ℕ}

theorem diag_eq_two_mul (Hc H2 : Matrix (Fin (g + g)) (Fin (g + g)) ℂ)
    (hSc : ∀ x y x' y', hermForm Hc (Fin.append x y) (Fin.append x' y') = hermForm Hc (Fin.append y x) (Fin.append y' x'))
    (hS2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') = hermForm H2 (Fin.append y x) (Fin.append y' x'))
    (hM2 : ∀ x y x' y', hermForm H2 (Fin.append x y) (Fin.append x' y') =
      hermForm Hc (Fin.append x ((2 : ℂ) • y)) (Fin.append x' ((2 : ℂ) • y'))) (z w : Fin g → ℂ) :
    hermForm Hc (Fin.append z z) (Fin.append w w) = 2 * hermForm Hc (Fin.append z 0) (Fin.append 0 w) := by
  have hA : ∀ x x', hermForm Hc (Fin.append x 0) (Fin.append x' 0) = 0 := by
    intro x x'
    have e1 := hM2 x 0 x' 0
    have e2 := hS2 x 0 x' 0
    have e3 := hM2 0 x 0 x'
    have e4 := hSc x 0 x' 0
    simp only [smul_zero] at e1
    have e5 : Fin.append (0 : Fin g → ℂ) ((2 : ℂ) • x) = (2 : ℂ) • Fin.append 0 x := by
      rw [← append_smul, smul_zero]
    have e6 : Fin.append (0 : Fin g → ℂ) ((2 : ℂ) • x') = (2 : ℂ) • Fin.append 0 x' := by
      rw [← append_smul, smul_zero]
    rw [e5, e6, hermForm_smul_left, hermForm_smul_right] at e3
    have hs : (star (2 : ℂ)) = 2 := by simp
    rw [hs] at e3
    linear_combination (-1/3 : ℂ) * (-e1 + e2 + e3 - 4 * e4)
  have hA2 : ∀ y y', hermForm Hc (Fin.append 0 y) (Fin.append 0 y') = 0 := by
    intro y y'
    rw [← hSc y 0 y' 0]
    exact hA y y'
  rw [herm_append, hA, hA2, ← hSc z 0 0 w]
  ring

end GlobalTheory.RiemInt

open GlobalTheory.RosatiAH GlobalTheory.RiemInt in

theorem GlobalTheory.RiemInt.riemannForm_int : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∀ (c' : 𝔠.elt) (l l' : u.Λ), ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (((e j ((c' : F) / (2 * (c : F))) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im = n := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH c' l l'
  obtain ⟨U0, hU0⟩ := GlobalTheory.exists_holUnif_tensor_self X.A X.ab (X.diag c) _ u
  have hAb2 := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have frame : ∀ c' : 𝔠.elt, ∃ (U : HolUnif (X.A ⊗ X.A) (X.P c') (Module.finrank ℚ F + Module.finrank ℚ F))
      (H : Matrix (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) (Fin (Module.finrank ℚ F + Module.finrank ℚ F)) ℂ)
      (χ : U.Λ → ℂ), (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) ∧ IsFactorAH U H χ := fun c' => by
    obtain ⟨U, H, χ', hex, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif (X.A ⊗ X.A) hAb2 _ _ U0 (X.P c') (X.isLB c')
    exact ⟨U, H, χ', fun x y => by rw [hex]; exact hU0 x y, hF⟩
  choose U H χ' hex hF using frame
  have hswap : ∀ d v, (U d).ex (fswap _ v) = (U d).ex v ≫ lift (snd X.A X.A) (fst X.A X.A) := by
    intro d v
    rw [eq_append v, fswap_append, hex, hex]
    simp
  have hmul : ∀ d d' (b : 𝓞 F) v, (U d').ex (fmul (dmul fun j => (e j (b : F) : ℂ)) v) =
      (U d).ex v ≫ lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b) := by
    intro d d' b v
    rw [eq_append v, fmul_append, hex, hex, dmul_apply, hu]
    simp
  have hdiag : ∀ z, (U c).ex (fdiag _ z) = u.ex z ≫ lift (𝟙 X.A) (𝟙 X.A) := by
    intro z
    rw [fdiag_apply, hex]
    simp
  have hdLB : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hD := hermForm_eq_of_lbIso_pull X.A (X.A ⊗ X.A) (X.diag c) (X.P c) hdLB (X.isLB c) _ _ u (U c) _ χ (H c) (χ' c)
    (isFactorAH_of_isAH hAH) (hF c) (lift (𝟙 X.A) (𝟙 X.A)) (fdiag _) hdiag (by unfold Obj.diag; exact GlobalTheory.lbIso_refl hdLB)
  have hS : ∀ d x y x' y', hermForm (H d) (Fin.append x y) (Fin.append x' y') =
      hermForm (H d) (Fin.append y x) (Fin.append y' x') := by
    intro d x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P d) (X.P d) (X.isLB d) (X.isLB d) _ _ (U d) (U d)
      (H d) (χ' d) (H d) (χ' d) (hF d) (hF d) (lift (snd X.A X.A) (fst X.A X.A)) (fswap _) (hswap d) (X.symm d)
      (Fin.append x y) (Fin.append x' y')
    rwa [fswap_append, fswap_append] at this
  have hM : ∀ (b : 𝓞 F) d x y x' y', hermForm (H (b • d)) (Fin.append x y) (Fin.append x' y') =
      hermForm (H d) (Fin.append x (dmul (fun j => (e j (b : F) : ℂ)) y))
        (Fin.append x' (dmul (fun j => (e j (b : F) : ℂ)) y')) := by
    intro b d x y x' y'
    have := hermForm_eq_of_lbIso_pull (X.A ⊗ X.A) (X.A ⊗ X.A) (X.P (b • d)) (X.P d) (X.isLB _) (X.isLB d) _ _
      (U (b • d)) (U d) (H _) (χ' _) (H d) (χ' d) (hF _) (hF d)
      (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)) (fmul (dmul fun j => (e j (b : F) : ℂ)))
      (hmul _ d b) (X.smul b d) (Fin.append x y) (Fin.append x' y')
    rwa [fmul_append, fmul_append] at this
  have h2F : (((2 : 𝓞 F)) : F) = 2 := by norm_cast
  have h2 : (dmul fun j => (e j (((2 : 𝓞 F) : F)) : ℂ)) = (2 : ℂ) • LinearMap.id := by
    refine LinearMap.ext fun z => funext fun k => ?_
    simp only [dmul_apply, h2F, map_ofNat, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_ofNat]
  have hB : ∀ z w, 2 * hermForm (H c) (Fin.append z 0) (Fin.append 0 w) =
      ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
    intro z w
    rw [← diag_eq_two_mul (H c) (H ((2 : 𝓞 F) • c)) (hS c) (hS _) (fun x y x' y' => by rw [hM 2 c, h2]; rfl),
      ← fdiag_apply, ← fdiag_apply, ← hD]
    simp only [hermForm, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hl : Fin.append (l : Fin (Module.finrank ℚ F) → ℂ) 0 ∈ (U c').Λ := by
    rw [← (U c').ker, hex, (u.ker _).2 l.2, (u.ker _).2 u.Λ.zero_mem]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, MonObj.one_comp]
    · rw [lift_snd, MonObj.one_comp]
  have hl' : Fin.append 0 (l' : Fin (Module.finrank ℚ F) → ℂ) ∈ (U c').Λ := by
    rw [← (U c').ker, hex, (u.ker _).2 l'.2, (u.ker _).2 u.Λ.zero_mem]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, MonObj.one_comp]
    · rw [lift_snd, MonObj.one_comp]
  obtain ⟨n, hn⟩ := im_hermForm_int (A := X.A ⊗ X.A) (X.isLB c') (U c') (hF c') ⟨_, hl⟩ ⟨_, hl'⟩
  refine ⟨n, ?_⟩
  rw [← hn]
  congr 1
  have hc0 : (c : F) ≠ 0 := by
    intro h0
    have := hc (e ⟨0, Module.finrank_pos⟩)
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective (A := 𝓞 F) ((c' : F) / (c : F))
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  change (b : F) / (d : F) = _ at hbd
  have hcc : d • c' = b • c := by
    apply Subtype.ext
    rw [div_eq_div_iff hd0 hc0] at hbd
    simp only [Submodule.coe_smul, Algebra.smul_def]
    change (d : F) * c' = (b : F) * c
    rw [hbd, mul_comm]
  have hde : ∀ j, (e j (d : F) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (map_ne_zero (e j)).2 hd0
  set w : Fin (Module.finrank ℚ F) → ℂ := fun j => (e j (d : F) : ℂ)⁻¹ * (l' : Fin (Module.finrank ℚ F) → ℂ) j with hw
  have e1 := hM d c' l 0 0 w
  have e2 := hM b c l 0 0 w
  have e3 : dmul (fun j => (e j (d : F) : ℂ)) w = l' := by
    funext j
    simp only [dmul_apply, hw]
    rw [← _root_.mul_assoc, mul_inv_cancel₀ (hde j), _root_.one_mul]
  rw [hcc, e2, map_zero, map_zero, e3] at e1
  change _ = hermForm (H c') (Fin.append (l : Fin (Module.finrank ℚ F) → ℂ) 0) (Fin.append 0 (l' : Fin (Module.finrank ℚ F) → ℂ))
  rw [← e1]
  refine mul_left_cancel₀ (two_ne_zero (α := ℂ)) ?_
  rw [hB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e4 : (c' : F) / (2 * (c : F)) = (b : F) / (d : F) / 2 := by
    rw [hbd]; field_simp
  have := hde j
  simp only [e4, dmul_apply, hw, map_div₀, map_mul, map_inv₀, map_ofNat, Complex.conj_ofReal, Complex.ofReal_div,
    Complex.ofReal_ofNat]
  field_simp
