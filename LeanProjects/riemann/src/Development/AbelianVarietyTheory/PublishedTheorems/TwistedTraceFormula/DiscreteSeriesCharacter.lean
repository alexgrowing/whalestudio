import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace
open GlobalTheory.AutomorphicL2Unitary (descend LeftInv mk measurable_mk)
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open GlobalTheory.RealInd (IsIrrAdm IsIndModel IndModule Flag groupRep indFun leviOne mats)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar

section Disc

variable {n : ℕ}

def weylDisc (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  resultant x.charpoly (derivative x.charpoly) n (n - 1) / x.det ^ (n - 1)

theorem weylDisc_eq_prod {x : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ} (hz : ∀ a, z a ≠ 0)
    (h : x.charpoly = ∏ a, (X - C (z a))) : weylDisc x = ∏ a, ∏ b ∈ Finset.univ.erase a, (1 - z b / z a) := by
  have hn : (∏ a, (X - C (z a))).natDegree = n := by rw [← h, charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hd : x.det = ∏ a, z a := by
    have := Matrix.det_eq_sign_charpoly_coeff x
    rw [h, coeff_zero_eq_eval_zero] at this
    simp [this, eval_prod, Finset.prod_neg, ← mul_assoc, ← mul_pow]
  have hr := resultant_prod_left Finset.univ (fun a => X - C (z a)) (derivative (∏ a, (X - C (z a)))) (n - 1)
    (by simp) ((natDegree_derivative_le _).trans (by rw [hn]))
  rw [hn] at hr
  rw [weylDisc, h, hr, hd, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [natDegree_X_sub_C, resultant_X_sub_C_left _ _ _ ((natDegree_derivative_le _).trans (by rw [hn])),
    derivative_prod_finset, eval_finsetSum, Finset.sum_eq_single a, show n - 1 = (Finset.univ.erase a).card by simp,
    ← Finset.prod_const, eval_mul, eval_prod]
  · simp only [derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, mul_one, eval_sub, eval_X, eval_C,
      ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun b _ => by field_simp [hz a]
  · intro b _ hb
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := a) (by simp [hb.symm]) (by simp), zero_mul]
  · simp

theorem weylDisc_diagonal {z : Fin n → ℂ} (hz : ∀ a, z a ≠ 0) :
    weylDisc (diagonal z) = ∏ a, ∏ b ∈ Finset.univ.erase a, (1 - z b / z a) :=
  weylDisc_eq_prod hz (charpoly_diagonal z)

theorem weylDisc_ne_zero_iff {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.det ≠ 0) : weylDisc x ≠ 0 ↔ IsRegSS x := by
  have hn : x.charpoly.natDegree = n := by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h1 : (derivative x.charpoly).natDegree = n - 1 := by rw [natDegree_derivative, hn]
  have := isUnit_resultant_iff_isCoprime (g := derivative x.charpoly) x.charpoly_monic
  rw [hn, h1, isUnit_iff_ne_zero] at this
  rw [weylDisc, div_ne_zero_iff, this, IsRegSS, separable_def]
  exact and_iff_left (pow_ne_zero _ hx)

theorem continuous_weylDisc {Y : Type*} [TopologicalSpace Y] {x : Y → Matrix (Fin n) (Fin n) ℂ} (hc : Continuous x)
    (hx : ∀ y, (x y).det ≠ 0) : Continuous fun y => weylDisc (x y) := by
  have h1 : ∀ i, Continuous fun y => (x y).charpoly.coeff i := fun i => by
    have : (fun y => (x y).charpoly.coeff i) =
        fun y => MvPolynomial.eval (fun p : Fin n × Fin n => x y p.1 p.2) ((Matrix.charpoly.univ ℂ (Fin n)).coeff i) :=
      funext fun y => (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id ℂ)
        (fun p : Fin n × Fin n => x y p.1 p.2) i).symm
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun p => hc.matrix_elem _ _)
  refine Continuous.div (Continuous.matrix_det (continuous_matrix fun i j => ?_)) (hc.matrix_det.pow _)
    fun y => pow_ne_zero _ (hx y)
  induction j using Fin.addCases with
  | left j =>
    simp only [sylvester, of_apply, Fin.addCases_left, coeff_derivative]
    split_ifs
    exacts [(h1 _).mul continuous_const, continuous_const]
  | right j =>
    simp only [sylvester, of_apply, Fin.addCases_right]
    split_ifs
    exacts [h1 _, continuous_const]

end Disc

section Cartan

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_ujMat : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val

theorem det_ujMat_ne_zero (g : UJ ε) : (ujMat ε g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 g.1.isUnit).ne_zero

def IsCartanSub (T : Subgroup (UJ ε)) : Prop := ∃ s, IsRegSS (ujMat ε s) ∧ T = cent s

def IsCartanSystem (𝒯 : Finset (Subgroup (UJ ε))) : Prop :=
  (∀ T ∈ 𝒯, IsCartanSub T) ∧
    ∀ T : Subgroup (UJ ε), IsCartanSub T → ∃! T', T' ∈ 𝒯 ∧ ∃ x, T.map (MulAut.conj x).toMonoidHom = T'

def weylOrder {H : Type} [Group H] (T : Subgroup H) : ℕ := T.relIndex (Subgroup.normalizer (T : Set H))

theorem IsCartanSub.isClosed {T : Subgroup (UJ ε)} (h : IsCartanSub T) : IsClosed (T : Set (UJ ε)) := by
  obtain ⟨s, -, rfl⟩ := h
  exact isClosed_cent s

theorem IsCartanSub.le_cent {T : Subgroup (UJ ε)} (h : IsCartanSub T) {t : UJ ε} (ht : t ∈ T) : T ≤ cent t := by
  obtain ⟨s, hs, rfl⟩ := h
  exact fun u hu => mem_cent.2 (congrArg Subtype.val
    ((isMulCommutative_cent_realUJ hs).is_comm.comm ⟨u, hu⟩ ⟨t, ht⟩))

theorem IsCartanSub.eq_cent {T : Subgroup (UJ ε)} (h : IsCartanSub T) {t : UJ ε} (ht : t ∈ T)
    (hr : IsRegSS (ujMat ε t)) : T = cent t := by
  refine le_antisymm (h.le_cent ht) ?_
  obtain ⟨s, hs, rfl⟩ := h
  exact IsCartanSub.le_cent ⟨t, hr, rfl⟩ (mem_cent.2 (mem_cent.1 ht).symm)

theorem IsCartanSub.isMulRightInvariant {T : Subgroup (UJ ε)} (h : IsCartanSub T) (dt : Measure T)
    [dt.IsMulLeftInvariant] : dt.IsMulRightInvariant := by
  obtain ⟨s, hs, rfl⟩ := h
  exact isMulRightInvariant_cent (isMulCommutative_cent_realUJ hs) dt

theorem IsCartanSub.quotInt_eq {T : Subgroup (UJ ε)} (h : IsCartanSub T) {t : UJ ε} (ht : t ∈ T)
    (hr : IsRegSS (ujMat ε t)) (dt : Measure T) [dt.IsHaarMeasure] {μ : Measure (UJ ε)} {f : UJ ε → ℂ} {c : ℂ}
    (hf : ∀ (ds : Measure (cent t)) [ds.IsHaarMeasure] [ds.IsMulRightInvariant], HasOrbInt μ t ds f c) :
    quotInt T dt μ (conjFn t f) = c := by
  have := h.isMulRightInvariant dt
  obtain rfl := h.eq_cent ht hr
  exact (hf dt).2

end Cartan

section Char

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

def IsAnalyticAt (Θ : UJ ε → ℂ) (s : UJ ε) : Prop :=
  ∃ Φ : (Fin n → Fin n → ℂ) → ℂ, AnalyticAt ℝ Φ (matCoord (ujMat ε) s) ∧ ∀ᶠ g in 𝓝 s, Θ g = Φ (matCoord (ujMat ε) g)

def IsGlobalChar (μ : Measure (UJ ε)) (π : UJ ε →* (V →L[ℂ] V)) (Θ : UJ ε → ℂ) : Prop :=
  IsCharFn (ujMat ε) μ π Θ ∧ ∀ s, IsRegSS (ujMat ε s) → IsAnalyticAt Θ s ∧ ∀ x, Θ (x⁻¹ * s * x) = Θ s

theorem isInducing_matCoord : Topology.IsInducing (matCoord (ujMat ε)) := (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing

theorem isGlobalChar_trivial (μ : Measure (UJ ε)) [μ.IsHaarMeasure] : IsGlobalChar μ (charRep 1) fun _ => 1 :=
  ⟨⟨continuous_const.locallyIntegrable, fun _ _ => continuousAt_const, fun _ hf =>
    repTrace_charRep (χ := 1) continuous_const (continuous_of_mem_ccSmooth isInducing_matCoord.continuous hf) hf.1⟩,
    fun _ _ => ⟨⟨fun _ => 1, analyticAt_const, .of_forall fun _ => rfl⟩, fun _ => rfl⟩⟩

end Char

section Torus

variable {n : ℕ}

def torusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) : UJ ε :=
  ⟨⟨diagonal fun a => Complex.exp (θ a * Complex.I), diagonal fun a => Complex.exp (-(θ a * Complex.I)),
    by simp [← Complex.exp_add], by simp [← Complex.exp_add]⟩, by
      change _ᴴ * Jm ε * _ = Jm ε
      simp only [Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
      congr 1
      funext a
      rw [mul_right_comm, Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp⟩

theorem ujMat_torusPt (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    ujMat ε (torusPt ε θ) = diagonal fun a => Complex.exp (θ a * Complex.I) := rfl

def wtVal (μ θ : Fin n → ℝ) : ℂ := Complex.exp ((∑ a, μ a * θ a : ℝ) * Complex.I)

def weylDenom (θ : Fin n → ℝ) : ℂ :=
  ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (((θ a - θ b) / 2 : ℝ) * Complex.I) -
    Complex.exp ((-((θ a - θ b) / 2) : ℝ) * Complex.I))

def compactWeyl (ε : Fin n → Bool) : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun w => ε ∘ w = ε

def halfDim (ε : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun a => ε a = true).card * (Finset.univ.filter fun a => ε a = false).card

def dsChar (ε : Fin n → Bool) (lam θ : Fin n → ℝ) : ℂ :=
  (-1) ^ halfDim ε * (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * wtVal (lam ∘ w.symm) θ) / weylDenom θ

theorem weylDenom_mul (θ : Fin n → ℝ) : weylDenom θ * wtVal (fun _ => ((n : ℝ) - 1) / 2) θ =
    ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  have h : ∑ a, ((n : ℝ) - 1) / 2 * θ a = ∑ a, ∑ b ∈ Finset.Ioi a, (θ a + θ b) / 2 := by
    have h1 : ∑ a, ∑ b ∈ Finset.Ioi a, θ b = ∑ b, ∑ _a ∈ Finset.Iio b, θ b :=
      Finset.sum_comm' (by simp)
    simp only [← Finset.sum_div, Finset.sum_add_distrib, h1, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio,
      nsmul_eq_mul]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := a.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [weylDenom, wtVal, h]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [sub_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 2 <;> push_cast <;> ring

theorem weylDenom_ne_zero {ε : Fin n → Bool} {θ : Fin n → ℝ} (h : IsRegSS (ujMat ε (torusPt ε θ))) :
    weylDenom θ ≠ 0 := by
  rw [IsRegSS, ujMat_torusPt, charpoly_diagonal, separable_prod_X_sub_C_iff] at h
  refine left_ne_zero_of_mul (weylDenom_mul θ ▸ Finset.prod_ne_zero_iff.2 fun a _ =>
    Finset.prod_ne_zero_iff.2 fun b hb => sub_ne_zero.2 fun e => (Finset.mem_Ioi.1 hb).ne (h e))

theorem dsChar_eq (ε : Fin n → Bool) {lam : Fin n → ℝ} {m : Fin n → ℤ} (hm : ∀ a, lam a + ((n : ℝ) - 1) / 2 = m a)
    (θ : Fin n → ℝ) : dsChar ε lam θ = (-1) ^ halfDim ε *
      (∑ w ∈ compactWeyl ε, ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, Complex.exp (θ a * Complex.I) ^ m (w.symm a)) /
        ∏ a, ∏ b ∈ Finset.Ioi a, (Complex.exp (θ a * Complex.I) - Complex.exp (θ b * Complex.I)) := by
  rw [dsChar, ← weylDenom_mul, ← mul_div_mul_right _ _ (c := wtVal (fun _ => ((n : ℝ) - 1) / 2) θ) (Complex.exp_ne_zero _),
    mul_assoc, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, wtVal, wtVal, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  simp only [← add_mul, Function.comp, hm, ← Complex.exp_int_mul, ← Complex.exp_sum, Complex.ofReal_sum,
    Finset.sum_mul]
  simp [mul_assoc]

example (e : Bool) (l θ : ℝ) : dsChar ![e] ![l] ![θ] = Complex.exp (l * θ * Complex.I) := by
  cases e <;> simp [dsChar, halfDim, compactWeyl, weylDenom, wtVal, Finset.filter_singleton]

example (lam θ : Fin 2 → ℝ) : dsChar ![true, false] lam θ =
    wtVal (lam + ![1 / 2, -1 / 2]) θ / (1 - wtVal ![1, -1] θ) := by
  have h1 : compactWeyl ![true, false] = {1} := by decide
  have h2 : halfDim ![true, false] = 1 := by decide
  have h3 : Complex.exp (((θ 0 - θ 1) / 2 : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have h4 : (Finset.Ioi (0 : Fin 2)) = {1} := by decide
  have h5 : (Finset.Ioi (1 : Fin 2)) = ∅ := by decide
  rw [dsChar, h1, h2, Finset.sum_singleton, weylDenom, Fin.prod_univ_two, h4, h5, Finset.prod_singleton,
    Finset.prod_empty, mul_one, ← neg_div_neg_eq, ← mul_div_mul_right _ _ h3, neg_sub, sub_mul]
  simp only [wtVal, ← Complex.exp_add, Fin.sum_univ_two]
  congr 1
  · simp only [pow_one, neg_mul, one_mul, neg_neg, Equiv.Perm.sign_one, Units.val_one, Int.cast_one,
      ← Complex.exp_add]
    congr 1
    simp [show (1 : Equiv.Perm (Fin 2)).symm = 1 from rfl]
    ring
  · rw [← Complex.exp_zero]
    congr 2 <;> simp <;> ring

theorem exists_isRegSS_torusPt (ε : Fin n → Bool) : ∃ θ, IsRegSS (ujMat ε (torusPt ε θ)) := by
  refine ⟨fun a => 1 / ((a : ℕ) + 1), ?_⟩
  rw [IsRegSS, ujMat_torusPt, charpoly_diagonal, separable_prod_X_sub_C_iff]
  have hb : ∀ a : Fin n, -Real.pi < (((1 / ((a : ℕ) + 1) : ℝ) : ℂ) * Complex.I).im ∧
      (((1 / ((a : ℕ) + 1) : ℝ) : ℂ) * Complex.I).im ≤ Real.pi := fun a => by
    have h1 : (0 : ℝ) < 1 / ((a : ℕ) + 1) := by positivity
    have h2 : (1 : ℝ) / ((a : ℕ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; simp
    rw [Complex.mul_I_im, Complex.ofReal_re]
    constructor <;> linarith [Real.pi_gt_three]
  intro a b h
  have := Complex.exp_inj_of_neg_pi_lt_of_le_pi (hb a).1 (hb a).2 (hb b).1 (hb b).2 h
  rw [mul_left_inj' Complex.I_ne_zero, Complex.ofReal_inj, one_div, one_div, _root_.inv_inj, add_left_inj,
    Nat.cast_inj] at this
  exact Fin.ext this

example (e : Bool) : IsCartanSystem ({⊤} : Finset (Subgroup (UJ ![e]))) ∧ weylOrder (⊤ : Subgroup (UJ ![e])) = 1 := by
  have hc : ∀ s : UJ ![e], cent s = ⊤ := fun s => eq_top_iff.2 fun t _ => mem_cent.2 (Subtype.ext (Units.ext
    (Matrix.ext fun i j => by fin_cases i; fin_cases j; simp [Matrix.mul_apply, mul_comm])))
  obtain ⟨θ, hθ⟩ := exists_isRegSS_torusPt ![e]
  refine ⟨⟨fun T hT => ⟨_, hθ, by rw [Finset.mem_singleton.1 hT, hc]⟩, fun T ⟨s, _, hs⟩ => ⟨⊤, ⟨by simp, 1, ?_⟩,
    fun T' h => Finset.mem_singleton.1 h.1⟩⟩, Subgroup.relIndex_top_left _⟩
  rw [hs, hc]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj 1).surjective

end Torus

end GlobalTheory.HCChar

namespace GlobalTheory.Published

open GlobalTheory.HCChar

def CharacterRegularity : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsIrrAdm ε π),
    ∃ Θ, IsGlobalChar μ (groupRep ε h.2.1.1) Θ

def DiscreteSeriesCharacter : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)),
    IsHCParam lam → IsDS ε lam σ → ∀ h : IsURepOn (UJset ε) σ, ∃ Θ, IsGlobalChar μ (ujRep h) Θ ∧
      ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

def WeylIntegrationFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯) ∧
    (∀ T : Subgroup (UJ ε), IsCartanSub T → weylOrder T ≠ 0) ∧
    ∀ (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (𝒯 : Finset (Subgroup (UJ ε))), IsCartanSystem 𝒯 →
      ∀ dt : ∀ T : Subgroup (UJ ε), Measure T, (∀ T ∈ 𝒯, (dt T).IsHaarMeasure) →
        ∀ F : UJ ε → ℝ≥0∞, Measurable F →
          ∫⁻ g, F g ∂μ = ∑ T ∈ 𝒯, (weylOrder T : ℝ≥0∞)⁻¹ *
            ∫⁻ t : T, ‖weylDisc (ujMat ε t)‖ₑ * ∫⁻ q, F (q.out⁻¹ * t * q.out) ∂quotMeas T (dt T) μ ∂dt T

def InducedCharacterSupport : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (a : ℕ) (j : Fin a → ℕ) (W : Flag n a),
    IsIsoFlag ε j W → (∀ i, 1 ≤ j i) → a ≠ 0 →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ (s : Fin a → ℂ) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
        (ρ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (ι : indFun (ε := ε) ⊤ j W σ s →ₗ[ℂ] X),
        IsIndModel ⊤ (KG ε) (muK ε) _ ρ ι → ∀ h : IsCRepOn (UJset ε) ρ, ∃ Θ, IsGlobalChar μ (groupRep ε h) Θ ∧
          ∀ g, IsRegSS (ujMat ε g) → (∀ x, x * g * x⁻¹ ∉ flagM ε W) → Θ g = 0

def HarishChandraCharacters : Prop :=
  CharacterRegularity ∧ DiscreteSeriesCharacter ∧ WeylIntegrationFormula ∧ InducedCharacterSupport

theorem DiscreteSeriesCharacter.apply_torusPt (h : DiscreteSeriesCharacter) {n : ℕ} {ε : Fin n → Bool}
    {μ : Measure (UJ ε)} [μ.IsHaarMeasure] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (hl : IsHCParam lam)
    (hσ : IsDS ε lam σ) {hU : IsURepOn (UJset ε) σ} {Θ : UJ ε → ℂ} (hΘ : IsCharFn (ujMat ε) μ (ujRep hU) Θ)
    {θ : Fin n → ℝ} (hθ : IsRegSS (ujMat ε (torusPt ε θ))) : Θ (torusPt ε θ) = dsChar ε lam θ := by
  obtain ⟨Θ', h1, h2⟩ := h n ε μ V lam σ hl hσ hU
  rw [hΘ.unique isInducing_matCoord h1.1 hθ, h2 θ hθ]

theorem InducedCharacterSupport.indModule (h : InducedCharacterSupport) {n : ℕ} {ε : Fin n → Bool}
    (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (I : IndModule ε) (ha : I.a ≠ 0) : ∃ Θ, IsGlobalChar μ I.rep Θ ∧
      ∀ g, IsRegSS (ujMat ε g) → (∀ x, x * g * x⁻¹ ∉ flagM ε I.W) → Θ g = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := I.temp
  exact h n ε μ I.a I.j I.W I.flag I.pos ha I.V I.σ h3 h2 I.s I.H I.ρ I.ι I.model I.isCRepOn

theorem WeylIntegrationFormula.integral_mul (h : WeylIntegrationFormula) {n : ℕ} {ε : Fin n → Bool}
    (μ : Measure (UJ ε)) [μ.IsHaarMeasure] {𝒯 : Finset (Subgroup (UJ ε))} (h𝒯 : IsCartanSystem 𝒯)
    (dt : ∀ T : Subgroup (UJ ε), Measure T) (hdt : ∀ T ∈ 𝒯, (dt T).IsHaarMeasure) {f Θ : UJ ε → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hΘ : LocallyIntegrable Θ μ)
    (hcl : ∀ s x, IsRegSS (ujMat ε s) → Θ (x⁻¹ * s * x) = Θ s) :
    (∀ T ∈ 𝒯, Integrable (fun t : T => ‖weylDisc (ujMat ε t)‖ * Θ t * quotInt T (dt T) μ (conjFn t f)) (dt T)) ∧
      ∫ g, f g * Θ g ∂μ = ∑ T ∈ 𝒯, (weylOrder T : ℂ)⁻¹ *
        ∫ t : T, ‖weylDisc (ujMat ε t)‖ * Θ t * quotInt T (dt T) μ (conjFn t f) ∂dt T := by
  obtain ⟨-, hw, hW⟩ := h n ε
  have hb : ∀ T : Subgroup (UJ ε), ∃ b : UJ ε → ℝ≥0∞, Measurable b ∧
      (T ∈ 𝒯 → quotMeas T (dt T) μ = (μ.withDensity b).map (mk T)) := fun T => by
    by_cases hT : T ∈ 𝒯
    · have := hdt T hT
      have := (h𝒯.1 T hT).isMulRightInvariant (dt T)
      obtain ⟨b, hb, h1⟩ := exists_bruhat (h𝒯.1 T hT).isClosed (dt T)
      exact ⟨b, hb, fun _ => (isQuotMeasure_quotMeas (dt T) μ (h𝒯.1 T hT).isClosed).eq_map hb h1⟩
    · exact ⟨0, measurable_zero, fun h => absurd h hT⟩
  choose b hb hν using hb
  let d : ∀ T : Subgroup (UJ ε), T → ℝ≥0 := fun T t => (weylOrder T : ℝ≥0)⁻¹ * ‖weylDisc (ujMat ε t)‖₊
  have hd : ∀ T, Measurable (d T) := fun T => (continuous_const.mul (continuous_weylDisc
    (continuous_ujMat.comp continuous_subtype_val) fun t => det_ujMat_ne_zero _).nnnorm).measurable
  let Φ : ∀ T : Subgroup (UJ ε), T × UJ ε → UJ ε := fun T p => p.2⁻¹ * p.1 * p.2
  have hΦ : ∀ T, Measurable (Φ T) := fun T =>
    (measurable_snd.inv.mul (measurable_subtype_coe.comp measurable_fst)).mul measurable_snd
  let m : ∀ T : Subgroup (UJ ε), Measure (T × UJ ε) := fun T =>
    ((dt T).withDensity fun t => d T t).prod (μ.withDensity (b T))
  have hμ : μ = ∑ T ∈ 𝒯, (m T).map (Φ T) := by
    refine Measure.ext_of_lintegral _ fun F hF => ?_
    rw [hW μ 𝒯 h𝒯 dt hdt F hF, lintegral_finsetSum_measure]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hm : Measurable fun p => F (Φ T p) := hF.comp (hΦ T)
    rw [lintegral_map hF (hΦ T), lintegral_prod _ hm.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ (hd T).coe_nnreal_ennreal hm.lintegral_prod_right',
      ← lintegral_const_mul' _ _ (by simpa using hw T (h𝒯.1 T hT))]
    refine lintegral_congr fun t => ?_
    have hi : LeftInv T fun x => F (x⁻¹ * t * x) := fun u hu x => by
      have : (u * x)⁻¹ * t * (u * x) = x⁻¹ * (u⁻¹ * (t * u)) * x := by group
      simp only [this, ← mem_cent.1 ((h𝒯.1 T hT).le_cent t.2 hu), inv_mul_cancel_left]
    have h2 := lintegral_map (μ := μ.withDensity (b T)) (measurable_descend hi
      (hF.comp ((measurable_inv.mul_const _).mul measurable_id))) (measurable_mk (Γ := T))
    simp only [hi.descend_mk] at h2
    rw [hν T hT, ← mul_assoc]
    refine congrArg₂ _ ?_ h2
    simp [d, ENNReal.coe_inv, hw T (h𝒯.1 T hT), enorm]
  have hI : Integrable (fun g => f g * Θ g) (∑ T ∈ 𝒯, (m T).map (Φ T)) :=
    hμ ▸ hΘ.integrable_smul_left_of_hasCompactSupport hf hc
  rw [integrable_finsetSum_measure] at hI
  have key : ∀ T ∈ 𝒯, ∀ t : T, d T t • ∫ x, f (Φ T (t, x)) * Θ (Φ T (t, x)) ∂μ.withDensity (b T) =
      (weylOrder T : ℂ)⁻¹ * (‖weylDisc (ujMat ε t)‖ * Θ t * quotInt T (dt T) μ (conjFn t f)) := fun T hT t => by
    by_cases h0 : weylDisc (ujMat ε t) = 0
    · simp [d, h0]
    have hr := (weylDisc_ne_zero_iff (det_ujMat_ne_zero _)).1 h0
    have hi := leftInv_conjFn ((h𝒯.1 T hT).le_cent t.2) f
    have h2 := integral_map (μ := μ.withDensity (b T)) (measurable_mk (Γ := T)).aemeasurable (measurable_descend hi
      (hf.measurable.comp ((measurable_inv.mul_const _).mul measurable_id))).aestronglyMeasurable
    simp only [hi.descend_mk] at h2
    simp only [Φ, hcl _ _ hr, integral_mul_const]
    rw [quotInt, hν T hT, h2]
    simp only [d, conjFn, NNReal.smul_def, Complex.real_smul]
    push_cast
    ring
  have hI' : ∀ T ∈ 𝒯, Integrable (fun p => f (Φ T p) * Θ (Φ T p)) (m T) := fun T hT =>
    (integrable_map_measure (hI T hT).1 (hΦ T).aemeasurable).1 (hI T hT)
  refine ⟨fun T hT => ?_, ?_⟩
  · have h1 := (integrable_withDensity_iff_integrable_smul (hd T)).1 (hI' T hT).integral_prod_left
    simp only [key T hT] at h1
    exact (integrable_const_mul_iff (IsUnit.mk0 _ (inv_ne_zero (by exact_mod_cast hw T (h𝒯.1 T hT)))) _).1 h1
  · conv_lhs => rw [hμ]
    rw [integral_finsetSum_measure hI]
    refine Finset.sum_congr rfl fun T hT => ?_
    have := hdt T hT
    have : LocallyCompactSpace T := (h𝒯.1 T hT).isClosed.locallyCompactSpace
    rw [integral_map (hΦ T).aemeasurable (hI T hT).1, integral_prod _ (hI' T hT),
      integral_withDensity_eq_integral_smul (hd T), ← integral_const_mul]
    exact integral_congr_ae (.of_forall (key T hT))

theorem WeylIntegrationFormula.integral_mul_eq_zero (h : WeylIntegrationFormula) {n : ℕ} {ε : Fin n → Bool}
    (μ : Measure (UJ ε)) [μ.IsHaarMeasure] {f Θ : UJ ε → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hΘ : LocallyIntegrable Θ μ) (hcl : ∀ s x, IsRegSS (ujMat ε s) → Θ (x⁻¹ * s * x) = Θ s)
    (h0 : ∀ s, IsRegSS (ujMat ε s) → Θ s = 0 ∨
      ∀ (ds : Measure (cent s)) [ds.IsHaarMeasure] [ds.IsMulRightInvariant], HasOrbInt μ s ds f 0) :
    ∫ g, f g * Θ g ∂μ = 0 := by
  obtain ⟨𝒯, h𝒯⟩ := (h n ε).1
  have hdt : ∀ T : Subgroup (UJ ε), ∃ dt : Measure T, T ∈ 𝒯 → dt.IsHaarMeasure := fun T => by
    by_cases hT : T ∈ 𝒯
    · have : LocallyCompactSpace T := (h𝒯.1 T hT).isClosed.locallyCompactSpace
      exact ⟨Measure.haar, fun _ => inferInstance⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose dt hdt using hdt
  rw [(h.integral_mul μ h𝒯 dt hdt hf hc hΘ hcl).2]
  refine Finset.sum_eq_zero fun T hT => mul_eq_zero_of_right _ (integral_eq_zero_of_ae (.of_forall fun t => ?_))
  have := hdt T hT
  by_cases hd : weylDisc (ujMat ε t) = 0
  · simp [hd]
  have hr := (weylDisc_ne_zero_iff (det_ujMat_ne_zero _)).1 hd
  rcases h0 t hr with h1 | h1
  · simp [h1]
  · simp [(h𝒯.1 T hT).quotInt_eq t.2 hr (dt T) h1]

end GlobalTheory.Published
