import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannTheoremNonprincipalPolarisedTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAppellHumbertStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFactorAHLamDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleEndoFactorPullbackStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.TorusRM

namespace GlobalTheory.TorusRM

open GlobalTheory.CechPic

theorem exists_obj_of_polarised_torus : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (𝔠 : FracId F) (r : Fin (Module.finrank ℚ F) → ℝ) (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)),
    (∀ i, 0 < r i) → DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ →
    (∀ (a : 𝓞 F), ∀ w ∈ Λ, (fun i ↦ (e i (a : F) : ℂ) * w i) ∈ Λ) →
    (∀ c ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e i c * r i : ℝ) : ℂ) * l i * starRingEnd ℂ (l' i)).im = n) →
    (∀ w : Fin (Module.finrank ℚ F) → ℂ, (∀ c ∈ 𝔠.elt, ∀ l ∈ Λ, ∃ n : ℤ,
      (∑ i, ((e i c * r i : ℝ) : ℂ) * w i * starRingEnd ℂ (l i)).im = n) → w ∈ Λ) →
    ∀ c : 𝔠.elt, IsTotPos (c : F) →
    ∃ (X : Obj F 𝔠 (Sp ℂ)) (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)),
      (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧
      (∀ (a : 𝓞 F) w, u.ex (fun i ↦ (e i (a : F) : ℂ) * w i) = u.ex w ≫ X.rm.act a) ∧
      ∃ χ, u.IsAH (Matrix.diagonal fun i ↦ ((2 * (e i (c : F) * r i) : ℝ) : ℂ)) χ := by
  intro F _ _ _ e 𝔠 r Λ hr hdisc hfull hstab hint hdual c hc
  let Hc : F → Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ :=
    fun x ↦ Matrix.diagonal fun i ↦ ((e i x * r i : ℝ) : ℂ)
  have form : ∀ x (z w : Fin (Module.finrank ℚ F) → ℂ),
      z ⬝ᵥ (Hc x).mulVec (star w) = ∑ i, ((e i x * r i : ℝ) : ℂ) * z i * starRingEnd ℂ (w i) := by
    intro x z w
    simp only [Hc, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.star_def]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have herm : ∀ x, (Hc x).IsHermitian := fun x ↦ by
    simp only [Hc, Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  have pos : ∀ x : F, IsTotPos x → ∀ z : Fin (Module.finrank ℚ F) → ℂ, z ≠ 0 →
      0 < (z ⬝ᵥ (Hc x).mulVec (star z)).re := by
    intro x hx z hz
    rw [form, Complex.re_sum]
    have h1 : ∀ i, (((e i x * r i : ℝ) : ℂ) * z i * starRingEnd ℂ (z i)).re = (e i x * r i) * Complex.normSq (z i) := by
      intro i
      rw [_root_.mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp_rw [h1]
    obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    exact Finset.sum_pos' (fun i _ ↦ mul_nonneg (mul_pos (hx _) (hr i)).le (Complex.normSq_nonneg _))
      ⟨j, Finset.mem_univ _, mul_pos (mul_pos (hx _) (hr j)) (Complex.normSq_pos.2 hj)⟩
  have integ : ∀ x ∈ 𝔠.elt, ∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ (Hc x).mulVec (star l')).im = n :=
    fun x hx l hl l' hl' ↦ by rw [form]; exact hint x hx l hl l' hl'
  obtain ⟨A, _, ab, dim, L₀, u₀, χ₀, hL₀, hΛ₀, hAH₀⟩ :=
    GlobalTheory.T.riemann_theorem_nonprincipal_polarised_torus _ Λ (Hc c) hdisc hfull (herm c) (pos c hc) (integ c c.2)
  haveI := ab.comm
  have hproj : IsProjOver A.hom :=
    GlobalTheory.ProjSpace.isProjOver_of_relAmple (GlobalTheory.T.rel_ample_of_appell_humbert _ A ab L₀ u₀ (Hc c) χ₀ hL₀ hAH₀)
  let ρ : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ) :=
    (Algebra.lmul ℂ (Fin (Module.finrank ℚ F) → ℂ)).toRingHom.comp
      (Pi.ringHom fun i ↦ (Complex.ofRealHom.comp (e i)).comp (algebraMap (𝓞 F) F))
  have hρ : ∀ a w, ρ a w = fun i ↦ (e i (a : F) : ℂ) * w i := fun a w ↦ rfl
  obtain ⟨rm, hrm⟩ := GlobalTheory.TorusAction.exists_oAct_of_map_lattice _ A ab L₀ u₀ (𝓞 F) ρ fun a z hz ↦ by
    rw [hΛ₀] at hz ⊢
    rw [hρ]
    exact hstab a z hz
  have hb := fun x : 𝔠.elt ↦ GlobalTheory.T.exists_appell_humbert_factor _ A ab L₀ u₀ (Hc c) χ₀ hL₀ hAH₀ (Hc x) (herm x)
    (fun l hl l' hl' ↦ integ x x.2 l ((hΛ₀ l).1 hl) l' ((hΛ₀ l').1 hl'))
  choose M u χ hM hex hf using hb
  have memΛ : ∀ x z, z ∈ (u x).Λ ↔ z ∈ Λ := fun x z ↦ by
    rw [← (u x).ker, hex x, u₀.ker, hΛ₀]
  have hΘ : ∀ x, ∃ t : LB.Gen (Theta A (M x)), t.IsGen :=
    fun x ↦ exists_gen_theta_of_isAbelianScheme ℂ A ab (M x) (hM x)
  have hlam : ∀ x, (abelian₂ A (M x)).IsLB := fun x ↦ LB.isLB_linComb (hM x) _ _
  obtain ⟨u', χ', hex', hf'⟩ := GlobalTheory.TorusRM.exists_isFactorAH_lam_diag _ A ab (M c) (u c) (Hc c) (χ c) (hM c) (hf c)
  have hsmul : ∀ (a : 𝓞 F) (x : 𝔠.elt),
      LBIso (abelian₂ A (M (a • x))) ((abelian₂ A (M x)).pull (lift (fst A A) (snd A A ≫ rm.act a)).left) :=
    fun a x ↦ GlobalTheory.T.appell_humbert_hom_compatible _ A ab hproj (M x) (M (a • x)) (u x) (u (a • x)) (Hc x) (Hc (a • x))
        (χ x) (χ _) (rm.act a) (ρ a) (hM x) (hM _) ((hex _).trans (hex x).symm) (hf x) (hf _) (rm.hom a)
        (fun z ↦ by rw [hex x]; exact hrm a z)
        (fun z w ↦ by
          rw [form, form]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hcoe : algebraMap (𝓞 F) F a = (a : F) := rfl
          simp only [hρ, Submodule.coe_smul, Algebra.smul_def, hcoe, map_mul, Complex.ofReal_mul, Complex.conj_ofReal]
          ring)
        (fun z w ↦ by
          rw [form, form, hρ, hρ]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [map_mul, Complex.conj_ofReal]
          ring)
  have hc0 : (c : F) ≠ 0 := fun h ↦ by
    have := hc (e ⟨0, Module.finrank_pos⟩)
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  have hact0 : rm.act 0 = 1 := by
    have h := rm.add 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have hmul : ∀ x : 𝔠.elt, (x : F) ≠ 0 → ∃ a₀ : 𝓞 F, IsTotPos ((a₀ • x : 𝔠.elt) : F) := by
    intro x hx
    obtain ⟨k, hk, hint'⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x : F))).exists_integral_multiple
    refine ⟨⟨(k * k : ℤ) • (x : F), ?_⟩, fun τ ↦ ?_⟩
    · rw [mul_smul]
      exact hint'.smul k
    · have h1 : τ (x : F) ≠ 0 := (map_ne_zero τ).2 hx
      have h2 : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
      have h3 : τ (((k * k : ℤ) • (x : F)) * (x : F)) = ((k : ℝ) * τ x) ^ 2 := by
        simp only [zsmul_eq_mul, map_mul, map_intCast, Int.cast_mul]
        ring
      change 0 < τ (((k * k : ℤ) • (x : F)) * (x : F))
      rw [h3]
      positivity
  have hker : ∀ (x : 𝔠.elt) (T : Over (Sp ℂ)) (y : T ⟶ A),
      HasGen ((abelian₂ A (M x)).pull (lift (fst A T) (snd A T ≫ y)).left) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • x) → y ≫ rm.act a = 1 := by
    intro x T y hy a ha
    by_cases hx : (x : F) = 0
    · obtain ⟨b, hb⟩ := ha c
      have hb' : (a : F) * c = (b : F) * x := by
        have := congrArg (fun y : 𝔠.elt ↦ (y : F)) hb
        simpa [Submodule.coe_smul, Algebra.smul_def] using this
      rw [hx, mul_zero] at hb'
      have ha0 : a = 0 := by
        rcases mul_eq_zero.1 hb' with h | h
        · exact_mod_cast h
        · exact absurd h hc0
      rw [ha0, hact0, MonObj.comp_one]
    · obtain ⟨a₀, ha₀⟩ := hmul x hx
      refine GlobalTheory.T.line_bundle_endo_factor_pullback _ A ab (M x) (u x) (Hc x) (χ x) (rm.act a) (hM x) (hf x)
        (M (a₀ • x)) (u (a₀ • x)) (Hc (a₀ • x : 𝔠.elt)) (χ (a₀ • x)) (rm.act a₀) (hM _)
        (isAH_of_isFactorAH (hf _) (pos _ ha₀)) (rm.hom a₀) (hsmul a₀ x) (fun w hw ↦ ?_) T y hy
      rw [hex x, ← hrm a w, u₀.ker, hΛ₀]
      refine hdual _ fun d hd l hl ↦ ?_
      obtain ⟨b, hb⟩ := ha ⟨d, hd⟩
      have hb' : (a : F) * d = (b : F) * x := by
        have := congrArg (fun y : 𝔠.elt ↦ (y : F)) hb
        simpa [Submodule.coe_smul, Algebra.smul_def] using this
      obtain ⟨n, hn⟩ := hw (ρ b l) ((memΛ x _).2 (by rw [hρ]; exact hstab b l hl))
      refine ⟨n, ?_⟩
      rw [← hn, form]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := congrArg (fun y ↦ ((e i y : ℝ) : ℂ)) hb'
      simp only [map_mul, Complex.ofReal_mul] at hi
      simp only [hρ, map_mul, Complex.ofReal_mul, Complex.conj_ofReal]
      linear_combination (↑(r i) * w i * (starRingEnd ℂ) (l i)) * hi
  let X : Obj F 𝔠 (Sp ℂ) :=
    { A := A
      ab := ab
      dim := dim
      rm := rm
      P := fun x ↦ abelian₂ A (M x)
      isLB := hlam
      rig₁ := fun x ↦ (cls_eq_zero_iff (pull_isLB (hlam x) _)).1 (by
        rw [Elliptic.cls_pull_lam (hM x), lam_one_left])
      rig₂ := fun x ↦ (cls_eq_zero_iff (pull_isLB (hlam x) _)).1 (by
        rw [Elliptic.cls_pull_lam (hM x), lam_one_right])
      symm := fun x ↦ (cls_eq_iff (hlam x) (pull_isLB (hlam x) _)).1 (by
        have h₁ : cls _ (hlam x) = lam (cls (M x) (hM x)) (fst A A) (snd A A) := cls_cube_two (hM x) _ _ (hlam x)
        rw [Elliptic.cls_pull_lam (hM x), h₁, lam_comm])
      add := fun x x' ↦ GlobalTheory.T.hermitian_forms_add_of_factor_product _ A ab hproj (M x) (M x') (M (x + x')) (u x) (u x') (u (x + x'))
        (Hc x) (Hc x') (Hc (x + x')) (χ x) (χ x') (χ (x + x')) (hM x) (hM x') (hM _)
        ((hex x').trans (hex x).symm) ((hex _).trans (hex x).symm) (hf x) (hf x') (hf _) (by
          simp only [Hc, Submodule.coe_add, map_add, Matrix.diagonal_add]
          congr 1
          funext i
          push_cast
          ring)
      smul := hsmul
      pos := fun x hx ↦ EighthPowerFactor.relAmple_diag_lam ab (hM x) (hΘ x)
        (GlobalTheory.T.rel_ample_of_appell_humbert _ A ab (M x) (u x) (Hc x) (χ x) (hM x) (isAH_of_isFactorAH (hf x) (pos x hx)))
      ker := hker }
  refine ⟨X, u', fun w ↦ ?_, fun a w ↦ ?_, χ', ?_⟩
  · rw [← u'.ker, hex', ← memΛ c, (u c).ker]
  · change u'.ex (ρ a w) = u'.ex w ≫ rm.act a
    rw [hex', hex c]
    exact hrm a w
  · have hm : (2 : ℂ) • Hc c = Matrix.diagonal fun i ↦ ((2 * (e i (c : F) * r i) : ℝ) : ℂ) := by
      simp only [Hc, ← Matrix.diagonal_smul]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [← hm]
    refine isAH_of_isFactorAH hf' fun z hz ↦ ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h2 : ∀ s : ℂ, ((2 : ℂ) * s).re = 2 * s.re := fun s ↦ by simp [Complex.mul_re]
    rw [h2]
    exact mul_pos two_pos (pos c hc z hz)

end GlobalTheory.TorusRM
