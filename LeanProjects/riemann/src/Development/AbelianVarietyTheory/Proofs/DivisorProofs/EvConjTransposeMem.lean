import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv

noncomputable section

open MeasureTheory
open scoped Pointwise Matrix
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF.CoefPolyPf

variable {n : ℕ} {ε : Fin n → Bool}

lemma continuous_toMK : Continuous (fun k : KG ε => toMK k) :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

lemma continuous_ev (P : Poly n) : Continuous (fun g : Mat n => ev g P) := by
  have h : Continuous (fun g : Mat n =>
      (Sum.elim (fun x : Fin n × Fin n => g x.1 x.2) (fun x : Fin n × Fin n => star (g x.1 x.2)))) := by
    refine continuous_pi fun i => ?_
    rcases i with x | x
    · exact (continuous_apply x.2).comp (continuous_apply x.1)
    · exact continuous_star.comp ((continuous_apply x.2).comp (continuous_apply x.1))
  exact (MvPolynomial.continuous_eval P).comp h

lemma integ {E : Type} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

def Gen : Set (Mat n → KG ε → ℂ) :=
  {Φ | ∃ (Q : Poly n) (g : KG ε → ℂ), Continuous g ∧ Φ = fun k h => ev k Q * g h}

lemma gen_mul : (Gen : Set (Mat n → KG ε → ℂ)) * (Gen : Set (Mat n → KG ε → ℂ)) ⊆ Gen := by
  refine Set.mul_subset_iff.2 ?_
  rintro _ ⟨Q, g, hg, rfl⟩ _ ⟨Q', g', hg', rfl⟩
  refine ⟨Q * Q', g * g', hg.mul hg', ?_⟩
  funext k h
  simp only [Pi.mul_apply, map_mul]
  ring

lemma span_mul {Φ Ψ : Mat n → KG ε → ℂ} (hΦ : Φ ∈ Submodule.span ℂ (Gen (ε := ε)))
    (hΨ : Ψ ∈ Submodule.span ℂ (Gen (ε := ε))) : Φ * Ψ ∈ Submodule.span ℂ (Gen (ε := ε)) := by
  have := Submodule.mul_mem_mul hΦ hΨ
  rw [Submodule.span_mul_span] at this
  exact Submodule.span_mono gen_mul this

lemma ev_X (k : Mat n) (i : (Fin n × Fin n) ⊕ (Fin n × Fin n)) :
    ev k (MvPolynomial.X i) = Sum.elim (fun x : Fin n × Fin n => k x.1 x.2) (fun x => star (k x.1 x.2)) i := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma ev_C (k : Mat n) (a : ℂ) : ev k (MvPolynomial.C a) = a := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma coord_mem (a b : Fin n) : Continuous (fun h : KG ε => toMK h a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_toMK)

lemma ev_conjTranspose_mem (P : Poly n) :
    (fun (k : Mat n) (h : KG ε) => ev (kᴴ * toMK h) P) ∈ Submodule.span ℂ (Gen (ε := ε)) := by
  induction P using MvPolynomial.induction_on with
  | C a => exact Submodule.subset_span ⟨MvPolynomial.C a, 1, continuous_const, by funext k h; simp [ev_C]⟩
  | add p q hp hq =>
      have := Submodule.add_mem _ hp hq
      convert this using 1
      funext k h
      simp [map_add]
  | mul_X p i hp =>
      have hx : (fun (k : Mat n) (h : KG ε) => ev (kᴴ * toMK h) (MvPolynomial.X i)) ∈
          Submodule.span ℂ (Gen (ε := ε)) := by
        rcases i with ⟨a, b⟩ | ⟨a, b⟩
        · have : (fun (k : Mat n) (h : KG ε) => ev (kᴴ * toMK h) (MvPolynomial.X (Sum.inl (a, b)))) =
              ∑ c, fun (k : Mat n) (h : KG ε) => ev k (MvPolynomial.X (Sum.inr (c, a))) * toMK h c b := by
            funext k h
            simp [ev_X, Matrix.mul_apply, Finset.sum_apply]
          rw [this]
          exact Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨_, _, coord_mem c b, rfl⟩
        · have : (fun (k : Mat n) (h : KG ε) => ev (kᴴ * toMK h) (MvPolynomial.X (Sum.inr (a, b)))) =
              ∑ c, fun (k : Mat n) (h : KG ε) => ev k (MvPolynomial.X (Sum.inl (c, a))) * star (toMK h c b) := by
            funext k h
            simp [ev_X, Matrix.mul_apply, Finset.sum_apply]
          rw [this]
          exact Submodule.sum_mem _ fun c _ =>
            Submodule.subset_span ⟨_, _, continuous_star.comp (coord_mem c b), rfl⟩
      have := span_mul hp hx
      convert this using 1
      funext k h
      simp [map_mul]

lemma integral_span {Φ : Mat n → KG ε → ℂ} (hΦ : Φ ∈ Submodule.span ℂ (Gen (ε := ε))) (c : KG ε → ℂ)
    (hc : Continuous c) :
    (∀ k, Continuous (Φ k)) ∧ ∃ Q : Poly n, ∀ k, ∫ h, Φ k h * c h ∂(muK ε) = ev k Q := by
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨Q, g, hg, rfl⟩ := hΦ
    refine ⟨fun k => continuous_const.mul hg, Q * MvPolynomial.C (∫ h, g h * c h ∂(muK ε)), fun k => ?_⟩
    rw [map_mul, ev_C, ← integral_const_mul]
    congr 1
    funext h
    ring
  | zero => exact ⟨fun k => continuous_const, 0, fun k => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨c1, Q1, e1⟩ := h1
    obtain ⟨c2, Q2, e2⟩ := h2
    refine ⟨fun k => (c1 k).add (c2 k), Q1 + Q2, fun k => ?_⟩
    simp only [Pi.add_apply, add_mul, map_add]
    rw [integral_add (f := fun h => Φ k h * c h) (g := fun h => Ψ k h * c h) (integ ((c1 k).mul hc))
      (integ ((c2 k).mul hc)), e1, e2]
  | smul a Φ _ h1 =>
    obtain ⟨c1, Q1, e1⟩ := h1
    refine ⟨fun k => continuous_const.mul (c1 k), MvPolynomial.C a * Q1, fun k => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, map_mul]
    rw [integral_const_mul, e1, ev_C]

end GlobalTheory.PsCo.PcEF.CoefPolyPf

namespace GlobalTheory.PsCo.PcEF.CoefPolyPf

variable {n : ℕ} {ε : Fin n → Bool}

def coordC (ab : Fin n × Fin n) : C(KG ε, ℂ) := ⟨fun h => toMK h ab.1 ab.2, coord_mem ab.1 ab.2⟩

def polyAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) := StarAlgebra.adjoin ℂ (Set.range coordC)

lemma polyAlg_poly {φ : C(KG ε, ℂ)} (hφ : φ ∈ polyAlg ε) : ∃ P : Poly n, ∀ h, φ h = ev (toMK h) P := by
  have hφ' : φ ∈ (polyAlg ε).toSubalgebra := hφ
  rw [polyAlg, StarAlgebra.adjoin_toSubalgebra] at hφ'
  clear hφ
  induction hφ' using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ab, rfl⟩ | hx
    · exact ⟨MvPolynomial.X (Sum.inl ab), fun h => by simp [ev_X, coordC]⟩
    · rw [Set.mem_star] at hx
      obtain ⟨ab, hab⟩ := hx
      refine ⟨MvPolynomial.X (Sum.inr ab), fun h => ?_⟩
      have : x = star (coordC ab) := by rw [hab, star_star]
      rw [this]
      simp [ev_X, coordC]
  | algebraMap r => exact ⟨MvPolynomial.C r, fun h => by simp [ev_C]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, fun h => by simp [hP, hQ, map_add]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P * Q, fun h => by simp [hP, hQ, map_mul]⟩

lemma toMK_injective : Function.Injective (fun k : KG ε => toMK k) := by
  intro x y hxy
  exact Subtype.ext (Subtype.ext (Units.ext hxy))

lemma polyAlg_sep : (polyAlg ε).SeparatesPoints := by
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy (toMK_injective h)
  obtain ⟨a, b, hab⟩ : ∃ a b, toMK x a b ≠ toMK y a b := by
    by_contra hc
    push_neg at hc
    exact hne (Matrix.ext hc)
  exact ⟨_, ⟨coordC (a, b), StarAlgebra.subset_adjoin ℂ _ ⟨(a, b), rfl⟩, rfl⟩, hab⟩

lemma lip (g : KG ε → ℂ) (hg : Continuous g) :
    Continuous (fun φ : C(KG ε, ℂ) => ∫ h, φ h * g h ∂(muK ε)) := by
  have hb : ∀ φ ψ : C(KG ε, ℂ), dist (∫ h, φ h * g h ∂(muK ε)) (∫ h, ψ h * g h ∂(muK ε)) ≤
      (∫ h, ‖g h‖ ∂(muK ε)) * dist φ ψ := by
    intro φ ψ
    rw [dist_eq_norm, ← integral_sub (f := fun h => φ h * g h) (g := fun h => ψ h * g h)
      (integ (φ.continuous.mul hg)) (integ (ψ.continuous.mul hg)), dist_eq_norm,
      mul_comm, ← integral_const_mul]
    refine norm_integral_le_of_norm_le ((integ hg.norm).const_mul _) (Filter.Eventually.of_forall fun h => ?_)
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm (φ - ψ) h) (norm_nonneg _)
  have hC : 0 ≤ ∫ h, ‖g h‖ ∂(muK ε) := integral_nonneg fun _ => norm_nonneg _
  exact (LipschitzWith.of_dist_le_mul (K := ⟨_, hC⟩) hb).continuous

lemma eq_zero_of_orth (g : KG ε → ℂ) (hg : Continuous g)
    (h0 : ∀ P : Poly n, ∫ h, ev (toMK h) P * g h ∂(muK ε) = 0) : g = 0 := by
  set Z : Set C(KG ε, ℂ) := {φ | ∫ h, φ h * g h ∂(muK ε) = 0} with hZ
  have hZc : IsClosed Z := isClosed_eq (lip g hg) continuous_const
  have hAZ : ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ Z := by
    intro φ hφ
    obtain ⟨P, hP⟩ := polyAlg_poly hφ
    show ∫ h, φ h * g h ∂(muK ε) = 0
    simp_rw [hP]
    exact h0 P
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyAlg_sep (ε := ε))
  have hmem : star (⟨g, hg⟩ : C(KG ε, ℂ)) ∈ Z := by
    have : star (⟨g, hg⟩ : C(KG ε, ℂ)) ∈ (polyAlg ε).topologicalClosure := by rw [htop]; trivial
    rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at this
    exact closure_minimal hAZ hZc this
  have h1 : ∫ h, ((‖g h‖ ^ 2 : ℝ) : ℂ) ∂(muK ε) = 0 := by
    rw [← hmem]
    congr 1
    funext h
    simp [Complex.conj_mul']
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h1
  have hint : Integrable (fun h => ‖g h‖ ^ 2) (muK ε) := integ (hg.norm.pow 2)
  have hae := (integral_eq_zero_iff_of_nonneg (fun h => by positivity) hint).1 h1
  have heq : (fun h => ‖g h‖ ^ 2) = (0 : KG ε → ℝ) :=
    (Continuous.ae_eq_iff_eq (muK ε) (hg.norm.pow 2) continuous_const).1 hae
  funext h
  have := congrFun heq h
  simpa using this

end GlobalTheory.PsCo.PcEF.CoefPolyPf

namespace GlobalTheory.PsCo.PcEF.CoefPolyPf

variable {n : ℕ} {ε : Fin n → Bool}

lemma toMK_mul (x y : KG ε) : toMK (x * y) = toMK x * toMK y := rfl

lemma toMK_one : toMK (1 : KG ε) = 1 := rfl

lemma toMK_inv (x : KG ε) : toMK x⁻¹ = (toMK x)ᴴ := by
  have hu : toMK x * star (toMK x) = 1 := Matrix.mem_unitaryGroup_iff.1 x.2.1
  have h1 : toMK x⁻¹ * toMK x = 1 := by rw [← toMK_mul, inv_mul_cancel, toMK_one]
  calc toMK x⁻¹ = toMK x⁻¹ * (toMK x * star (toMK x)) := by rw [hu, Matrix.mul_one]
    _ = star (toMK x) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

lemma cont_orbit {T : Mat n → (W →L[ℂ] W)} (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (v : W) :
    Continuous (fun h : KG ε => T (toMK h) v) :=
  (hT.2.2 v).comp_continuous continuous_toMK (fun h => h.2)

def avgSpan (ε : Fin n → Bool) (T : Mat n → (W →L[ℂ] W)) (v : W) : Submodule ℂ W :=
  Submodule.span ℂ (Set.range fun P : Poly n => ∫ h, ev (toMK h) P • T (toMK h) v ∂(muK ε))

lemma mem_avgSpan {T : Mat n → (W →L[ℂ] W)} (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (v : W) :
    v ∈ avgSpan ε T v := by
  haveI := FiniteDimensional.complete ℂ W
  by_contra hv
  rw [← Submodule.orthogonal_orthogonal (avgSpan ε T v), Submodule.mem_orthogonal] at hv
  push_neg at hv
  obtain ⟨u, hu, huv⟩ := hv
  have hg : Continuous (fun h : KG ε => ⟪u, T (toMK h) v⟫_ℂ) := continuous_const.inner (cont_orbit hT v)
  have h0 : ∀ P : Poly n, ∫ h, ev (toMK h) P * ⟪u, T (toMK h) v⟫_ℂ ∂(muK ε) = 0 := by
    intro P
    have hx : (∫ h, ev (toMK h) P • T (toMK h) v ∂(muK ε)) ∈ avgSpan ε T v :=
      Submodule.subset_span ⟨P, rfl⟩
    have := Submodule.inner_left_of_mem_orthogonal hx hu
    have hint : Integrable (fun h : KG ε => ev (toMK h) P • T (toMK h) v) (muK ε) :=
      integ (((continuous_ev P).comp continuous_toMK).smul (cont_orbit hT v))
    rw [← integral_inner hint] at this
    simpa [inner_smul_right] using this
  have := congrFun (eq_zero_of_orth _ hg h0) 1
  simp only [toMK_one, hT.1.1, Pi.zero_apply] at this
  exact huv this

lemma coef_avgSpan {T : Mat n → (W →L[ℂ] W)} (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (v w : W) {x : W}
    (hx : x ∈ avgSpan ε T v) : ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, ⟪w, T k x⟫_ℂ = ev k Q := by
  haveI := FiniteDimensional.complete ℂ W
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, rfl⟩ := hx
    have hc : Continuous (fun h : KG ε => ⟪w, T (toMK h) v⟫_ℂ) := continuous_const.inner (cont_orbit hT v)
    obtain ⟨-, Q, hQ⟩ := integral_span (ev_conjTranspose_mem (ε := ε) P) _ hc
    refine ⟨Q, fun k hk => ?_⟩
    obtain ⟨k', hk'⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [Formalism.REAL.range_toMK]; exact hk
    simp only at hk'
    subst hk'
    rw [← hQ]
    have hint : Integrable (fun h : KG ε => ev (toMK h) P • T (toMK h) v) (muK ε) :=
      integ (((continuous_ev P).comp continuous_toMK).smul (cont_orbit hT v))
    have hint2 : Integrable (fun h : KG ε => T (toMK k') (ev (toMK h) P • T (toMK h) v)) (muK ε) :=
      integ ((T (toMK k')).continuous.comp (((continuous_ev P).comp continuous_toMK).smul (cont_orbit hT v)))
    rw [← ContinuousLinearMap.integral_comp_comm _ hint, ← integral_inner hint2]
    have hF : ∀ h : KG ε, ⟪w, T (toMK k') (ev (toMK h) P • T (toMK h) v)⟫_ℂ =
        (fun y : KG ε => ev ((toMK k')ᴴ * toMK y) P * ⟪w, T (toMK y) v⟫_ℂ) (k' * h) := by
      intro h
      show _ = ev ((toMK k')ᴴ * toMK (k' * h)) P * ⟪w, T (toMK (k' * h)) v⟫_ℂ
      rw [toMK_mul, ← Matrix.mul_assoc, ← toMK_inv, ← toMK_mul k'⁻¹ k', inv_mul_cancel, toMK_one, Matrix.one_mul,
        map_smul, inner_smul_right, hT.1.2 _ k'.2 _ h.2]
      rfl
    simp_rw [hF]
    exact integral_mul_left_eq_self (fun y : KG ε => ev ((toMK k')ᴴ * toMK y) P * ⟪w, T (toMK y) v⟫_ℂ) k'
  | zero => exact ⟨0, fun k _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, fun k hk => by rw [map_add, inner_add_right, hP k hk, hQ k hk, map_add]⟩
  | smul a x _ hx =>
    obtain ⟨P, hP⟩ := hx
    exact ⟨MvPolynomial.C a * P, fun k hk => by rw [map_smul, inner_smul_right, hP k hk, map_mul, ev_C]⟩

end GlobalTheory.PsCo.PcEF.CoefPolyPf

namespace GlobalTheory.PsCo.PcEF

theorem coefPoly : CoefPoly := by
  intro n ε W _ _ _ T hT v w
  obtain ⟨Q, hQ⟩ := CoefPolyPf.coef_avgSpan hT v w (CoefPolyPf.mem_avgSpan hT v)
  exact ⟨Q, hQ⟩

end GlobalTheory.PsCo.PcEF
