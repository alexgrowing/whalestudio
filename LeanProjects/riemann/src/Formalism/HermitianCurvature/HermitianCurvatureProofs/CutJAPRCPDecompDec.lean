import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompNu
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPDecompDer

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

variable {k : ℕ}

section ann

variable {T T' : ℝ}

lemma kap_ne (hT : 0 < T) (hT' : 0 < T') : kap T T' ≠ 0 := by
  unfold kap
  exact_mod_cast (mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 hT')).ne'

lemma kap_sq (hT : 0 < T) (hT' : 0 < T') : kap T T' * kap T T' = ((T * T' : ℝ) : ℂ) := by
  unfold kap
  rw [← Complex.ofReal_mul, mul_mul_mul_comm, Real.mul_self_sqrt hT.le, Real.mul_self_sqrt hT'.le]

lemma wZ_eq (ζ : ℂ) : wZ T T' ζ = -(kap T T')⁻¹ * ζ := rfl

lemma wZ_star (ζ : ℂ) : star (wZ T T' ζ) = -(kap T T')⁻¹ * conj ζ := by
  rw [wZ_eq, star_mul', star_neg, star_inv₀, kap_star]
  rfl

lemma zeta_ne (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) : ζ ≠ 0 := by
  intro h
  rw [h, map_zero] at hζ
  exact absurd hζ (not_lt.2 (mul_pos hT hT').le)

lemma ws_rel (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    wZ T T' ζ * star (wZ T T' ζ) - sZ T T' ζ * sZ T T' ζ = 1 := by
  have hk := kap_ne hT hT'
  have h1 := sig_sq hζ
  have h2 := kap_sq hT hT'
  have h3 : gg (T * T') ζ = ζ * conj ζ - ((T * T' : ℝ) : ℂ) := by
    rw [Complex.mul_conj]; unfold gg; push_cast; ring
  rw [wZ_star, wZ_eq, sZ_eq T T' hT hT' ζ hζ]
  have h4 : ζ * conj ζ - sig (T * T') ζ * sig (T * T') ζ = kap T T' * kap T T' := by rw [h1, h3, h2]; ring
  field_simp
  linear_combination h4

lemma nuI_eq (ζ : ℂ) : nuI k T T' ζ = nuG k (wZ T T' ζ) (-sZ T T' ζ) (star (wZ T T' ζ)) := by
  unfold nuI
  rw [nu_eq, star_star]

lemma nuI_mul (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') {ζ : ℂ}
    (hζ : T * T' < Complex.normSq ζ) : nuI k T T' ζ * nu k (wZ T T' ζ) (sZ T T' ζ) = 1 := by
  rw [nuI_eq, nu_eq]
  have h := nuG_mul h0 (wZ T T' ζ) (-sZ T T' ζ) (star (wZ T T' ζ)) (by linear_combination ws_rel hT hT' hζ)
  rwa [neg_neg] at h

end ann

def PSL (k : ℕ) (TT : ℝ) (C : ℂ → Mb k) : Prop := (∀ i j, PS TT (fun ζ => C ζ i j)) ∧ ∀ ζ, InL k (C ζ)

lemma psl_smul {TT : ℝ} {f : ℂ → ℂ} (hf : PS TT f) {A : Mb k} (hA : InL k A) : PSL k TT (fun ζ => f ζ • A) := by
  refine ⟨fun i j => ?_, fun ζ i => ⟨?_, ?_⟩⟩
  · exact ps_mul hf (ps_const (A i j))
  · show f ζ * A i (Fin.last k) = 0
    rw [(hA i).1, mul_zero]
  · show f ζ * A (Fin.last k) i = 0
    rw [(hA i).2, mul_zero]

lemma psl_add {TT : ℝ} {C D : ℂ → Mb k} (hC : PSL k TT C) (hD : PSL k TT D) : PSL k TT (fun ζ => C ζ + D ζ) := by
  refine ⟨fun i j => ps_add (hC.1 i j) (hD.1 i j), fun ζ i => ⟨?_, ?_⟩⟩
  · show C ζ i (Fin.last k) + D ζ i (Fin.last k) = 0
    rw [(hC.2 ζ i).1, (hD.2 ζ i).1, add_zero]
  · show C ζ (Fin.last k) i + D ζ (Fin.last k) i = 0
    rw [(hC.2 ζ i).2, (hD.2 ζ i).2, add_zero]

lemma psl_csmul {TT : ℝ} (c : ℂ) {C : ℂ → Mb k} (hC : PSL k TT C) : PSL k TT (fun ζ => c • C ζ) := by
  refine ⟨fun i j => ps_mul (ps_const c) (hC.1 i j), fun ζ i => ⟨?_, ?_⟩⟩
  · show c * C ζ i (Fin.last k) = 0
    rw [(hC.2 ζ i).1, mul_zero]
  · show c * C ζ (Fin.last k) i = 0
    rw [(hC.2 ζ i).2, mul_zero]

def Dec (k : ℕ) (T T' : ℝ) (M : Mb k) : Prop :=
  ∃ (C₁ C₂ : ℂ → Mb k) (β₁ β₂ : ℂ → ℂ), PSL k (T * T') C₁ ∧ PSL k (T * T') C₂ ∧ PS (T * T') β₁ ∧ PS (T * T') β₂ ∧
    ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      M = C₁ ζ + nuI k T T' ζ * C₂ ζ * nu k (wZ T T' ζ) (sZ T T' ζ) + β₁ ζ • H1 k T T' ζ + β₂ ζ • H2 k T T' ζ

variable {T T' : ℝ}

lemma dec_mk (M : Mb k) (f₁ f₂ β₁ β₂ : ℂ → ℂ) (A₁ A₂ : Mb k) (hA₁ : InL k A₁) (hA₂ : InL k A₂) (h1 : PS (T * T') f₁)
    (h2 : PS (T * T') f₂) (h3 : PS (T * T') β₁) (h4 : PS (T * T') β₂)
    (h : ∀ ζ : ℂ, T * T' < Complex.normSq ζ →
      M = f₁ ζ • A₁ + nuI k T T' ζ * (f₂ ζ • A₂) * nu k (wZ T T' ζ) (sZ T T' ζ) + β₁ ζ • H1 k T T' ζ +
        β₂ ζ • H2 k T T' ζ) : Dec k T T' M :=
  ⟨_, _, β₁, β₂, psl_smul h1 hA₁, psl_smul h2 hA₂, h3, h4, h⟩

lemma dec_add {M N : Mb k} (hM : Dec k T T' M) (hN : Dec k T T' N) : Dec k T T' (M + N) := by
  obtain ⟨C₁, C₂, β₁, β₂, a1, a2, a3, a4, a5⟩ := hM
  obtain ⟨D₁, D₂, γ₁, γ₂, b1, b2, b3, b4, b5⟩ := hN
  refine ⟨_, _, _, _, psl_add a1 b1, psl_add a2 b2, ps_add a3 b3, ps_add a4 b4, fun ζ hζ => ?_⟩
  conv_lhs => rw [a5 ζ hζ, b5 ζ hζ]
  rw [Matrix.mul_add, Matrix.add_mul, add_smul, add_smul]
  abel

lemma dec_smul (c : ℂ) {M : Mb k} (hM : Dec k T T' M) : Dec k T T' (c • M) := by
  obtain ⟨C₁, C₂, β₁, β₂, a1, a2, a3, a4, a5⟩ := hM
  refine ⟨_, _, _, _, psl_csmul c a1, psl_csmul c a2, ps_mul (ps_const c) a3, ps_mul (ps_const c) a4, fun ζ hζ => ?_⟩
  conv_lhs => rw [a5 ζ hζ]
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_add, smul_add, smul_smul, smul_smul]

lemma inL_Su {a b : Fin (k + 1)} (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) : InL k (Su k a b) := by
  intro i
  unfold Su
  constructor
  · rw [Matrix.single_apply, if_neg (fun h => hb h.2)]
  · rw [Matrix.single_apply, if_neg (fun h => ha h.1)]

lemma inL_zero : InL k (0 : Mb k) := fun _ => ⟨rfl, rfl⟩

lemma ps_zero {TT : ℝ} : PS TT (fun _ => (0 : ℂ)) := ps_const 0

lemma dec_LL {a b : Fin (k + 1)} (ha : a ≠ Fin.last k) (hb : b ≠ Fin.last k) : Dec k T T' (Su k a b) :=
  dec_mk _ (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (Su k a b) 0 (inL_Su ha hb) inL_zero (ps_const 1) ps_zero
    ps_zero ps_zero (fun ζ _ => by simp)

lemma dec_lm (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') (m : Fin (k + 1)) (hm0 : m ≠ 0)
    (hml : m ≠ Fin.last k) : Dec k T T' (Su k (Fin.last k) m) := by
  refine dec_mk _ (fun ζ => (-1 : ℂ) * (ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (-kap T T') * (sig (T * T') ζ)⁻¹) (fun _ => 0)
    (fun _ => 0) (Su k 0 m) (Su k 0 m) (inL_Su h0 hml) (inL_Su h0 hml) (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv))
    (ps_mul (ps_const _) ps_sigInv) ps_zero ps_zero (fun ζ hζ => ?_)
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  rw [Matrix.mul_smul, Matrix.smul_mul, nuI_eq, nu_eq, conj0m h0 _ _ _ m hm0 hml, sZ_eq T T' hT hT' ζ hζ, wZ_eq]
  match_scalars <;> field_simp <;> ring

lemma dec_ml (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T') (m : Fin (k + 1)) (hm0 : m ≠ 0)
    (hml : m ≠ Fin.last k) : Dec k T T' (Su k m (Fin.last k)) := by
  refine dec_mk _ (fun ζ => conj ζ * (sig (T * T') ζ)⁻¹) (fun ζ => kap T T' * (sig (T * T') ζ)⁻¹) (fun _ => 0)
    (fun _ => 0) (Su k m 0) (Su k m 0) (inL_Su hml h0) (inL_Su hml h0) (ps_mul ps_conj ps_sigInv)
    (ps_mul (ps_const _) ps_sigInv) ps_zero ps_zero (fun ζ hζ => ?_)
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  rw [Matrix.mul_smul, Matrix.smul_mul, nuI_eq, nu_eq, conjm0 h0 _ _ _ m hm0 hml, sZ_eq T T' hT hT' ζ hζ, wZ_star]
  match_scalars <;> field_simp <;> ring

section plane

variable (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (hT : 0 < T) (hT' : 0 < T')
include h0 hT hT'

lemma plane_facts {ζ : ℂ} (hζ : T * T' < Complex.normSq ζ) :
    sZ T T' ζ ≠ 0 ∧ (kap T T')⁻¹ ≠ 0 ∧ star (wZ T T' ζ) ≠ 0 ∧
      2 * sZ T T' ζ * ((2 * kap T T')⁻¹ * conj ζ * (sig (T * T') ζ)⁻¹) = -(kap T T')⁻¹ * star (wZ T T' ζ) ∧
      2 * sZ T T' ζ * ((2 * kap T T')⁻¹ * ζ * (sig (T * T') ζ)⁻¹) = -(kap T T')⁻¹ * wZ T T' ζ := by
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have hz := zeta_ne hT hT' hζ
  have hzc : conj ζ ≠ 0 := by simpa using hz
  refine ⟨?_, inv_ne_zero hk, ?_, ?_, ?_⟩
  · rw [sZ_eq T T' hT hT' ζ hζ]; exact mul_ne_zero (inv_ne_zero hk) hs
  · rw [wZ_star]; exact mul_ne_zero (neg_ne_zero.2 (inv_ne_zero hk)) hzc
  · rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  · rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp

lemma dec_0l : Dec k T T' (Su k 0 (Fin.last k)) := by
  refine dec_mk _ (fun ζ => (2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (-2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹))
    (fun ζ => (-1 : ℂ) * sig (T * T') ζ) (fun _ => 0) (Su k 0 0) (Su k 0 0) (inL_Su h0 h0) (inL_Su h0 h0)
    (ps_mul (ps_const _) (ps_mul ps_conj ps_sigInv)) (ps_mul (ps_const _) (ps_mul ps_conj ps_sigInv))
    (ps_mul (ps_const _) ps_sig) ps_zero (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have key := unit0l h0 _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f4
  have e1 : -(star (wZ T T' ζ) / (2 * sZ T T' ζ)) = (2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  have e2 : star (wZ T T' ζ) / (2 * sZ T T' ζ) = (-2⁻¹ : ℂ) * (conj ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_star]; field_simp
  have e3 : -(sZ T T' ζ / (kap T T')⁻¹) = (-1 : ℂ) * sig (T * T') ζ := by
    rw [sZ_eq T T' hT hT' ζ hζ]; field_simp
  rw [e1, e2, e3, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, add_zero]
  exact key

lemma decomposition_lower_corner_unit : Dec k T T' (Su k (Fin.last k) 0) := by
  refine dec_mk _ (fun ζ => (-2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹)) (fun ζ => (2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹))
    (fun _ => 0) (fun ζ => (-1 : ℂ) * sig (T * T') ζ) (Su k 0 0) (Su k 0 0) (inL_Su h0 h0) (inL_Su h0 h0)
    (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv)) (ps_mul (ps_const _) (ps_mul ps_id ps_sigInv))
    ps_zero (ps_mul (ps_const _) ps_sig) (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have hs := sig_ne hζ
  have key := unitl0 h0 _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f5
  have e1 : wZ T T' ζ / (2 * sZ T T' ζ) = (-2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp
  have e2 : -(wZ T T' ζ / (2 * sZ T T' ζ)) = (2⁻¹ : ℂ) * (ζ * (sig (T * T') ζ)⁻¹) := by
    rw [sZ_eq T T' hT hT' ζ hζ, wZ_eq]; field_simp
  have e3 : -(sZ T T' ζ / (kap T T')⁻¹) = (-1 : ℂ) * sig (T * T') ζ := by
    rw [sZ_eq T T' hT hT' ζ hζ]; field_simp
  rw [e2, e1, e3, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, add_zero]
  exact key

lemma dec_ll : Dec k T T' (Su k (Fin.last k) (Fin.last k)) := by
  refine dec_mk _ (fun _ => 0) (fun _ => 1) (fun ζ => ζ) (fun ζ => (-1 : ℂ) * conj ζ) (Su k 0 0) (Su k 0 0)
    (inL_Su h0 h0) (inL_Su h0 h0) ps_zero (ps_const 1) ps_id (ps_mul (ps_const _) ps_conj) (fun ζ hζ => ?_)
  obtain ⟨f1, f2, f3, f4, f5⟩ := plane_facts h0 hT hT' hζ
  have hk := kap_ne hT hT'
  have key := unitll h0 _ _ _ _ _ _ f1 f2 f3 (ws_rel hT hT' hζ) f4 f5
  have e1 : -(wZ T T' ζ / (kap T T')⁻¹) = ζ := by rw [wZ_eq]; field_simp
  have e2 : star (wZ T T' ζ) / (kap T T')⁻¹ = (-1 : ℂ) * conj ζ := by rw [wZ_star]; field_simp
  rw [e1, e2, ← nuI_eq, ← nu_eq] at key
  rw [zero_smul, zero_add, one_smul]
  exact key

lemma dec_unit (a b : Fin (k + 1)) : Dec k T T' (Su k a b) := by
  by_cases ha : a = Fin.last k
  · subst ha
    by_cases hb : b = Fin.last k
    · subst hb; exact dec_ll h0 hT hT'
    · by_cases hb0 : b = 0
      · subst hb0; exact decomposition_lower_corner_unit h0 hT hT'
      · exact dec_lm h0 hT hT' b hb0 hb
  · by_cases hb : b = Fin.last k
    · subst hb
      by_cases ha0 : a = 0
      · subst ha0; exact dec_0l h0 hT hT'
      · exact dec_ml h0 hT hT' a ha0 ha
    · exact dec_LL ha hb

lemma dec_all (M : Mb k) : Dec k T T' M := by
  have hz : Dec k T T' (0 : Mb k) := by
    have := dec_smul (T := T) (T' := T') 0 (dec_LL (k := k) h0 h0)
    rwa [zero_smul] at this
  rw [Matrix.matrix_eq_sum_single M]
  refine Finset.sum_induction _ _ (fun _ _ => dec_add) hz fun i _ => ?_
  refine Finset.sum_induction _ _ (fun _ _ => dec_add) hz fun j _ => ?_
  have : Matrix.single i j (M i j) = M i j • Su k i j := by
    unfold Su; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact dec_smul _ (dec_unit h0 hT hT' i j)

end plane

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
