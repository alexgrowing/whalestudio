import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordActionSquareIntegrableBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneAddNormPowLeSumLinearFormPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartzStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem per_mM {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {m : ℕ} {f : (κ → AF F) → ℂ}
    (h : Per F m f) (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : Per F m (mM F l f) := by
  intro x z hz
  have hev : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have ha : arch F (x + z) = arch F x := by
    funext i
    obtain ⟨a, ha0, -, hza⟩ := hz i
    show evI F (x i + z i) = evI F (x i)
    rw [hev, hza, hmul, ha0, mul_zero, add_zero]
  unfold mM
  rw [ha, h x z hz]

theorem norm_word_rep {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : (κ → AF F) → ℂ) (x : κ → AF F) (N : ℕ) :
    ‖word F (List.replicate N (Sum.inr l)) f x‖ = |l (arch F x)| ^ N * ‖f x‖ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ, word_cons]
    show ‖(l (arch F x) : ℂ) * word F (List.replicate N (Sum.inr l)) f x‖ = _
    rw [norm_mul, ih, Complex.norm_real, Real.norm_eq_abs, pow_succ]
    ring

theorem om_bound_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ N
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨K, l, C0, hl, hpoly⟩ := GlobalTheory.T.one_add_norm_pow_le_sum_linearForm_pow F (Fin n × Fin d) N
  obtain ⟨P, Cs, c, hsob⟩ := GlobalTheory.T.sobolev_bound_periodic_schwartz F (Fin n × Fin d) μ hμ
  obtain ⟨C1, k1, hfin⟩ := GlobalTheory.T.weilRep_finite_periodicity_polynomial_height F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C2, k2, hL2⟩ := GlobalTheory.T.word_action_square_integrable_bound F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ μ hμ (P + N)
  set A : ℝ := max (max Cs 0 * max C1 1 ^ c * max C2 0) 1 with hA
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨max C0 0 * (K + 1) * A, k1 * c + k2, fun g h x => ?_⟩
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH1 : 1 ≤ H := one_le_mul_of_one_le_of_one_le (by exact_mod_cast one_le_heightGL F g.1)
    (by exact_mod_cast one_le_heightGL F h.1)
  obtain ⟨m, hm0, hmC, hper⟩ := hfin g h

  have key : ∀ w : List (Op F (Fin n × Fin d)), w.length ≤ N → (∀ o ∈ w, ∃ l', o = Sum.inr l' ∧ ‖l'‖ ≤ 1) →
      ‖word F w (om (g, h) Φ) x‖ ≤ A * H ^ (k1 * c + k2) := by
    intro w hw hwo
    have hS : word F w (om (g, h) Φ) ∈ schA F (Fin n × Fin d) ∧ Per F m (word F w (om (g, h) Φ)) := by
      clear hw
      induction w with
      | nil => exact ⟨(hP.weil.isUSplitting).pres _ _ hΦ, hper⟩
      | cons o w ih =>
        obtain ⟨l', rfl, -⟩ := hwo o List.mem_cons_self
        obtain ⟨i1, i2⟩ := ih fun o' ho' => hwo o' (List.mem_cons_of_mem _ ho')
        exact ⟨GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F _ (Sum.inr l') _ i1, per_mM i2 l'⟩
    have hH0 : 0 ≤ H := le_trans zero_le_one hH1
    have hb : 0 ≤ max C2 0 * H ^ k2 := mul_nonneg (le_max_right _ _) (pow_nonneg hH0 _)
    have hw' : ∀ v : List (Fin n × Fin d → mixedEmbedding.mixedSpace F), v.length ≤ P → (∀ u ∈ v, ‖u‖ ≤ 1) →
        ∫⁻ y, ‖wordD F v (word F w (om (g, h) Φ)) y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (max C2 0 * H ^ k2) := by
      intro v hv hv1
      have hlen : (v.map Sum.inl ++ w).length ≤ P + N := by
        rw [List.length_append, List.length_map]; omega
      have hsz : ∀ o ∈ v.map Sum.inl ++ w, size F o ≤ 1 := by
        intro o ho
        rcases List.mem_append.1 ho with ho | ho
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ho
          exact hv1 u hu
        · obtain ⟨l', rfl, hl'⟩ := hwo o ho
          exact hl'
      have h3 := hL2 g h (v.map Sum.inl ++ w) hlen hsz
      rw [word_append] at h3
      exact h3.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)))
    have h2 := hsob m hm0 _ hS.1 hS.2 (max C2 0 * H ^ k2) hb hw' x
    have hm' : (m : ℝ) ^ c ≤ (max C1 1 * H ^ k1) ^ c :=
      pow_le_pow_left₀ (Nat.cast_nonneg _)
        (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _))) c
    have e1 : ‖word F w (om (g, h) Φ) x‖ ^ 2 ≤ A * H ^ (k1 * c + k2) := by
      refine h2.trans ?_
      calc Cs * (m : ℝ) ^ c * (max C2 0 * H ^ k2)
          ≤ max Cs 0 * (max C1 1 * H ^ k1) ^ c * (max C2 0 * H ^ k2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) hm' (by positivity) (le_max_right _ _)) hb
        _ = (max Cs 0 * max C1 1 ^ c * max C2 0) * H ^ (k1 * c + k2) := by
            rw [mul_pow, ← pow_mul, pow_add]; ring
        _ ≤ A * H ^ (k1 * c + k2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hH0 _)
    have hT : 1 ≤ A * H ^ (k1 * c + k2) := one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hH1)
    nlinarith [norm_nonneg (word F w (om (g, h) Φ) x)]
  have hx := hpoly (arch F x)
  have k0 : ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := by
    simpa using key [] (by simp) (by simp)
  have kj : ∀ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖ ≤ A * H ^ (k1 * c + k2) := fun j => by
    have h4 := key (List.replicate N (Sum.inr (l j))) (by simp)
      (fun o ho => ⟨l j, List.eq_of_mem_replicate ho, hl j⟩)
    rwa [norm_word_rep] at h4
  show ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N ≤ _
  calc ‖om (g, h) Φ x‖ * (1 + ‖arch F x‖) ^ N
      ≤ ‖om (g, h) Φ x‖ * (max C0 0 * (1 + ∑ j, |l j (arch F x)| ^ N)) :=
        mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
          (norm_nonneg _)
    _ = max C0 0 * (‖om (g, h) Φ x‖ + ∑ j, |l j (arch F x)| ^ N * ‖om (g, h) Φ x‖) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ max C0 0 * (A * H ^ (k1 * c + k2) + ∑ _j : Fin K, A * H ^ (k1 * c + k2)) :=
        mul_le_mul_of_nonneg_left (add_le_add k0 (Finset.sum_le_sum fun j _ => kj j)) (le_max_right _ _)
    _ = max C0 0 * (K + 1) * A * H ^ (k1 * c + k2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.ArchDecay
