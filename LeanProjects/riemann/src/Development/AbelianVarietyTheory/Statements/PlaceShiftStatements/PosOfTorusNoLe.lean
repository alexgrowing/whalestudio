import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo

noncomputable section

namespace GlobalTheory.UCls.Model

open NumberField Matrix GlobalTheory.AdLat ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst
open GlobalTheory.Up.Definite

section Field

theorem exists_half {E : Type} [Field E] [NumberField E] {x : E} {n m : ℕ} (hm : n + 1 = 4 * m) (hs : x ^ 2 = -(n : E)) :
    ∃ y w : 𝓞 E, y ^ 2 = -(n : 𝓞 E) ∧ 2 * w = 1 + y := by
  have hi : IsIntegral ℤ x :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (n : ℤ), by monicity!, by simp [Polynomial.eval₂_add, hs]⟩
  have hw : IsIntegral ℤ ((1 + x) / 2) := by
    set c : E := (1 + x) / 2
    have hc : c ^ 2 - c + (m : E) = 0 := by
      have e : (n : E) + 1 = 4 * (m : E) := by exact_mod_cast hm
      simp only [c]
      linear_combination (1 / 4 : E) * hs - (1 / 4 : E) * e
    exact ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap _ E y = x := ⟨⟨x, hi⟩, rfl⟩
  obtain ⟨w, hw0⟩ : ∃ w : 𝓞 E, algebraMap _ E w = (1 + x) / 2 := ⟨⟨_, hw⟩, rfl⟩
  refine ⟨y, w, ?_, ?_⟩
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_pow, map_neg, map_natCast, hy]
    exact hs
  · apply IsFractionRing.injective (𝓞 E) E
    rw [map_mul, map_add, map_one, map_ofNat, hy, hw0]
    field_simp

theorem exists_field : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E),
    Unr E ∧ ∀ u : E, IsOfFinOrder u → u = 1 ∨ u = -1 := by
  have hh : Formalism.FrobeniusOrbits.HostHyp 11 7 := ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  obtain ⟨L, _, _, ζ, a, b, h⟩ := Formalism.TwoAdicCyclotomicDecomposition.layerExists (0 + 2) 11 7
  have := Formalism.FrobeniusOrbits.isCMField_hostE hh.toHypOdd h
  refine ⟨Formalism.FrobeniusOrbits.hostE ζ a b, inferInstance, inferInstance, inferInstance, ?_, fun u hu => ?_⟩
  · have ha : Formalism.FrobeniusOrbits.aE ζ a b ^ 2 = -((11 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b) := by
      apply Subtype.ext
      exact h.2.1
    have hb : Formalism.FrobeniusOrbits.bE ζ a b ^ 2 = -((7 : ℕ) : Formalism.FrobeniusOrbits.hostE ζ a b) := by
      apply Subtype.ext
      exact h.2.2.1
    obtain ⟨y₁, w₁, h1, h2⟩ := exists_half (m := 3) (by norm_num) ha
    obtain ⟨y₂, w₂, h3, h4⟩ := exists_half (m := 2) (by norm_num) hb
    exact GlobalTheory.HostModel.unramified_of_sqrt (by norm_num : Nat.Coprime 11 7) h1 h3 h2 h4
  · exact Formalism.FrobeniusOrbits.hostMu 0 11 7 hh (by norm_num) L ζ a b h u (isOfFinOrder_iff_pow_eq_one.1 hu)

end Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem selfDual_one : SelfDualLat (1 : Matrix (Fin r) (Fin r) E) (intVec E r) := by
  refine ⟨(data E r).Gm_herm, by simp, (data E r).Λ_fg, (data E r).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩
  · rw [mem_intVec]
    intro a
    have := h _ (single_mem_intVec a)
    rw [Up.Definite.herm_one, Finset.sum_eq_single a] at this
    · simpa [cc_one] using this
    · intro b _ hb; simp [hb, cc_zero]
    · simp
  · rw [mem_intVec] at hx hy
    rw [Up.Definite.herm_one]
    exact IsIntegral.sum _ fun a _ => (hx a).mul (isIntegral_cc (hy a))

theorem pos_one (τ : E →+* ℂ) (x : Fin r → E) (hx : x ≠ 0) :
    0 < (τ (herm (1 : Matrix (Fin r) (Fin r) E) x x)).re := by
  rw [map_herm_one_self, Complex.ofReal_re]
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ _, ?_⟩
  have : τ (x a) ≠ 0 := by simpa using ha
  positivity

theorem selfDual_hyp : SelfDualLat (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) (intVec E 2) ∧
    ∃ z, z ≠ 0 ∧ herm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) z z = 0 := by
  have hh : ∀ x y : Fin 2 → E, herm (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) E) x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
    intro x y; simp [herm]
  refine ⟨⟨fun a b => ?_, by simp, (data E 2).Λ_fg, (data E 2).Λ_span, fun x => ⟨fun h => ?_, fun hx y hy => ?_⟩⟩,
    ![1, 0], by simp, by simp [hh, cc_zero]⟩
  · fin_cases a <;> fin_cases b <;> simp [cc_one, cc_zero]
  · rw [mem_intVec]
    intro a
    fin_cases a
    · simpa [hh, cc_one, cc_zero] using h _ (single_mem_intVec 1)
    · simpa [hh, cc_one, cc_zero] using h _ (single_mem_intVec 0)
  · rw [mem_intVec] at hx hy
    rw [hh]
    exact ((hx 0).mul (isIntegral_cc (hy 1))).add ((hx 1).mul (isIntegral_cc (hy 0)))

theorem not_selfDual_two : ¬ SelfDualLat ((2 : E) • (1 : Matrix (Fin 1) (Fin 1) E)) (intVec E 1) := by
  rintro ⟨-, -, -, -, h⟩
  have h1 := (mem_intVec _).1 ((h fun _ => 1 / 2).1 fun y hy => by
    have := isIntegral_cc ((mem_intVec _).1 hy 0)
    simpa [herm] using this) 0
  have h2 : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := by simpa using h1
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at h2
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h2
  have : (2 * k : ℤ) = 1 := by
    have : (2 * k : ℚ) = 1 := by simp at hk; rw [hk]; norm_num
    exact_mod_cast this
  omega

theorem cong_trivial {M : ℕ} (hM : 3 ≤ M) (γ : GL (Fin r) E) (hγ : IsUStab 1 (intVec E r) γ)
    (hc : ∀ x ∈ intVec E r, ∃ y ∈ intVec E r, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) : γ = 1 := by
  apply Units.ext
  ext a b
  obtain ⟨y, hy, he⟩ := hc _ (single_mem_intVec b)
  have hya := (mem_intVec _).1 hy a
  have e : (γ : Matrix (Fin r) (Fin r) E) a b - (1 : Matrix (Fin r) (Fin r) E) a b = M * y a := by
    have := congrFun he a
    simpa [Matrix.one_apply, Pi.single_apply] using this
  have hb : ∀ φ : E →+* ℂ, ‖φ (y a)‖ ≤ 2 / 3 := by
    intro φ
    have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
        fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
      ext a; simp
    have h1 := congrArg φ (hγ.1 (Pi.single b 1) (Pi.single b 1))
    rw [map_herm_one_self, map_herm_one_self, hcol] at h1
    have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single b] <;> simp +contextual
    have h3 := Complex.ofReal_injective h1
    rw [h2] at h3
    have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
    rw [h3] at h4
    have h5 : ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
    have h6 : ‖φ ((1 : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    have h7 := congrArg (fun z => ‖φ z‖) e
    simp only [map_sub, map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h7
    have h8 := norm_sub_le (φ ((γ : Matrix (Fin r) (Fin r) E) a b)) (φ ((1 : Matrix (Fin r) (Fin r) E) a b))
    have h9 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (y a))]
  have h0 : y a = 0 := by
    by_contra hne
    obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hne hya
      fun φ => (hb φ).trans (by norm_num)
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 := congrArg (fun z => ‖φ z‖) hp
    simp only [map_pow, norm_pow, map_one, norm_one] at h1
    have := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h1
    linarith [hb φ]
  rw [h0, mul_zero, sub_eq_zero] at e
  simpa using e

theorem component_hyp {M : ℕ} (hM : 3 ≤ M) :
    ∃ (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))),
      IsUA (IsCMField.complexConj E) (1 : Matrix (Fin r) (Fin r) E) 1 ∧ X.Gm = 1 ∧
      (X.Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) 1 (intVec E r : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ X.Γ ↔ IsUStab 1 X.Λ γ ∧
        ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧
      IsOrth X x0 ∧ IsFundSet X x0 FF := by
  have ho : IsOrth (data E r) (x0F (data E r)) := fun τ => ((data E r).signature τ).choose_spec.2
  obtain ⟨FF, hF⟩ := fundSet_holds r (data E r) _ ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r _)
  refine ⟨data E r, _, FF, (isKM_one _ _ ∅ 1).1, rfl,
    (GlobalTheory.Member.latOf_one_eq _ _ _ _ (data E r).Λ_fg (data E r).Λ_span).symm, fun γ => ⟨fun h => ?_, fun h => ?_⟩, ho, hF⟩
  · obtain rfl := Subgroup.mem_bot.1 h
    exact ⟨by simp [IsUStab], fun x _ => ⟨0, zero_mem _, by simp⟩⟩
  · exact Subgroup.mem_bot.2 (cong_trivial hM γ h.1 h.2)

theorem joint_hyp (hT : TorusBound) (r M : ℕ) (hr : 2 ≤ r) (hM : 3 ≤ M) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (h : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
      (FF : Set (V (nd X))),
      Unr E ∧ (∀ u : E, IsOfFinOrder u → u = 1 ∨ u = -1) ∧ SelfDualLat (1 : Matrix (Fin r) (Fin r) E) (intVec E r) ∧
      (∀ (τ : E →+* ℂ) (x : Fin r → E), x ≠ 0 → 0 < (τ (herm (1 : Matrix (Fin r) (Fin r) E) x x)).re) ∧
      torusNo (IsCMField.complexConj E) 1 (intVec E r : Set (Fin r → E)) M ≤ h ∧
      IsUA (IsCMField.complexConj E) (1 : Matrix (Fin r) (Fin r) E) 1 ∧ X.Gm = 1 ∧
      (X.Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) 1 (intVec E r : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ X.Γ ↔ IsUStab 1 X.Λ γ ∧
        ∀ x ∈ X.Λ, ∃ y ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧
      IsOrth X x0 ∧ IsFundSet X x0 FF := by
  obtain ⟨E, _, _, _, hU, hm⟩ := exists_field
  obtain ⟨X, x0, FF, h⟩ := component_hyp (E := E) (r := r) hM
  exact ⟨E, inferInstance, inferInstance, inferInstance, _, X, x0, FF, hU, hm, selfDual_one, pos_one,
    hT E r M 1 _ (by omega) (by omega) hU selfDual_one, h⟩

theorem pos_of_torusNo_le (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (M h : ℕ)
    (hh : torusNo (IsCMField.complexConj E) G L M ≤ h) : 0 < h := by
  rcases Nat.eq_zero_or_pos h with rfl | h0
  · exfalso
    have : Nonempty (Quot fun a b : {t // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G L M a.1 b.1) := ⟨Quot.mk _ ⟨1, by simp [IsTA]⟩⟩
    have h1 := ENat.card_pos (α := Quot fun a b : {t // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G L M a.1 b.1)
    exact absurd (lt_of_lt_of_le h1 hh) (by simp)
  · exact h0

end GlobalTheory.UCls.Model
