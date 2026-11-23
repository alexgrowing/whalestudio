import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

namespace GlobalTheory.CMCurveTest

theorem w_sq {d : ℕ} (h4 : d % 4 = 3) {w : ℂ} (hw : w = (1 + Complex.I * √d) / 2) :
    w ^ 2 + (((1 + d) / 4 : ℕ) : ℂ) = w := by
  have h : ((((1 + d) / 4 : ℕ) : ℂ)) * 4 = 1 + d := by
    have : (1 + d) / 4 * 4 = 1 + d := by omega
    exact_mod_cast this
  have h2 : ((√d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rw [hw]
  linear_combination h / 4 + Complex.I ^ 2 * h2 / 4 + (d : ℂ) * Complex.I_sq / 4

theorem mul_eq_lift {S : Scheme.{0}} (P : Out.PolAV S) (a b : P.A ⟶ P.A) : a * b = lift a b ≫ μ[P.A] := rfl

theorem mean_log_of_cmCurve (h : CMCurve) {d : ℕ} [NeZero d] (h7 : 7 ≤ d) (hs : Squarefree d) (h4 : d % 4 = 3)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A)
      (n : (M →+* ℂ) → ℝ), P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ s, 0 < n s) ∧
      (∀ s r, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
      (∃ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left) (u : HolUnif P'.A P'.L P'.g) (c : ℂ),
        IsPolFibre ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) P P' φ ∧ c ≠ 0 ∧
        ∀ z, z ∈ u.Λ ↔ ∃ a b : ℤ, z = fun _ => c * (a + b * ((1 + Complex.I * √d) / 2))) ∧
      ((-((∑ s, Real.log (n s)) / Module.finrank ℚ M) : ℝ) : ℂ) =
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain ⟨K, _, _, h2, hr, hD, ⟨σ⟩, hτ⟩ := cmCurve_hypotheses.2.2 d h7 hs h4
  obtain ⟨τ, hτ⟩ := hτ σ
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, ha, hn, hb⟩ := h d h7 hs h4 K h2 hr
  choose n hn0 hn using hn
  obtain ⟨P', φ, -, u, -, -, -, hP, -⟩ := (hn (algebraMap M ℂ) _).2 rfl
  obtain ⟨c, hc, hl⟩ := ha P' φ hP u
  refine ⟨M, inferInstance, P, v, n, hg, hv, hn0, hn, ⟨P', φ, u, c, hP, hc, by simpa only [hw] using hl⟩, ?_⟩
  rw [hb n (fun s => (hn s _).2 rfl) σ τ hτ]
  have e := (LFunction_one_and_mean_log_eta h2 hD (by omega) hχ σ hτ).2
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast classNumber_pos K
  have hd : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have e1 : -((∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K) =
      Real.log (4 * Real.pi) + (∑ C, Real.log ((τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
    have : ∀ C, Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4) =
        Real.log (4 * Real.pi) + Real.log ((τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4) := fun C => by
      rw [_root_.mul_assoc (4 * Real.pi), Real.log_mul (by positivity) (mul_ne_zero (τ C).im_ne_zero
        (pow_ne_zero _ (norm_ne_zero_iff.2 (ModularForm.eta_ne_zero (τ C).2))))]
    simp only [this, Finset.sum_neg_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (Fintype.card (ClassGroup (𝓞 K)) : ℝ) = classNumber K from rfl]
    field_simp
  have e2 : Real.log (2 * Real.pi / √d) = Real.log (4 * Real.pi) - Real.log (2 * √d) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  rw [e1, Complex.ofReal_add, e, e2]
  push_cast
  ring

variable {R : Type} [CommRing R]

def scaleVec {A : Over (Sp R)} (c : R) (v : epsR R ⟶ A) : epsR R ⟶ A :=
  Over.homMk (spMap (epsScaleR c) ≫ v.left) (by
    rw [Category.assoc, Over.w v]
    refine (spMap_comp_spMap _ _).trans ?_
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

theorem isVecOver_scaleVec {R' : Type} [CommRing R'] {f : R →+* R'} {A : Over (Sp R)} {A' : Over (Sp R')}
    {φ : A'.left ⟶ A.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} (h : IsVecOver f φ v v') (c : R) :
    IsVecOver f φ (scaleVec c v) (scaleVec (f c) v') := by
  change (spMap (epsScaleR (f c)) ≫ v'.left) ≫ φ = spMap (Chart.dualMapR f) ≫ spMap (epsScaleR c) ≫ v.left
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc]
  congr 1
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem primeSpectrum_dual_eq (x y : PrimeSpectrum (DualNumber ℂ)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber ℂ), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem isDiff_scaleVec {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {w : Fin g → ℂ}
    {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ) : u.IsDiff (c • w) (scaleVec c v) := by
  intro U hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dual_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (scaleVec c v).left.appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]

theorem isLieNormSq_scaleVec {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} {s : R →+* ℂ} {r : ℝ}
    (h : IsLieNormSq P v s r) (c : R) : IsLieNormSq P (scaleVec c v) s (‖s c‖ ^ 2 * r) := by
  obtain ⟨P', φ, v', u, Hm, χ, w, h1, h2, h3, h4, rfl⟩ := h
  refine ⟨P', φ, scaleVec (s c) v', u, Hm, χ, s c • w, h1, isVecOver_scaleVec h2 c, h3, isDiff_scaleVec u h4 _, ?_⟩
  have : hermForm Hm (s c • w) (s c • w) = (‖s c‖ ^ 2 : ℝ) * hermForm Hm w w := by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← _root_.mul_assoc, Complex.star_def, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, mul_comm (s c)]
  rw [this, Complex.re_ofReal_mul]
  ring

theorem two_smul_generator {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} {s : R →+* ℂ} {r : ℝ}
    (h : IsLieNormSq P v s r) : IsLieNormSq P (scaleVec 2 v) s (4 * r) ∧ IsLieNormSq P (scaleVec 0 v) s 0 := by
  have h2 := isLieNormSq_scaleVec h 2
  have h0 := isLieNormSq_scaleVec h 0
  rw [map_ofNat, Complex.norm_ofNat] at h2
  rw [map_zero, norm_zero] at h0
  norm_num at h2 h0
  exact ⟨h2, h0⟩

end GlobalTheory.CMCurveTest
