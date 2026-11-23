import Formalism.HermitianCurvature.StatementJC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.JCx4

section maOps

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def maOp (d o : ℕ) (Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ (A : ℝ) (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ),
    CCle (A + d) (m + o) F b → CCle A m (Θ F) (K * b)) ∧
  (∀ (A : ℝ) (m : ℕ) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ), InCC (A + d) (m + o) F →
    InCC (A + d) (m + o) F' → ∀ g ∈ GV k r, Θ (F + c • F') g = Θ F g + c • Θ F' g) ∧
  (∀ (A : ℝ) (m : ℕ) (F F' : Mat k r → (Wq →L[ℂ] Wp)), InCC (A + d) (m + o) F →
    InCC (A + d) (m + o) F' → (∀ g ∈ GV k r, F g = F' g) → ∀ g ∈ GV k r, Θ F g = Θ F' g)

variable {Wp Wq}

theorem ma_inCC {d o : ℕ} {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h : maOp Wp Wq d o Θ) {A : ℝ} {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC (A + d) (m + o) F) :
    InCC A m (Θ F) := by
  obtain ⟨c, hc⟩ := hF
  obtain ⟨K, -, hK⟩ := h.1 A m
  exact ⟨K * c, hK F c hc⟩

theorem ma_inCC_lin {A : ℝ} {m : ℕ} {F F' : Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ) (hF : InCC A m F)
    (hF' : InCC A m F') : InCC A m (F + c • F') := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hF'
  exact ⟨a + ‖c‖ * b, CCle_add ha (CCle_smul c hb)⟩

theorem ma_op_congr {d o : ℕ} {Θ Θ' : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h : maOp Wp Wq d o Θ) (e : ∀ F, Θ' F = Θ F) : maOp Wp Wq d o Θ' := by
  obtain rfl : Θ' = Θ := funext e
  exact h

theorem ma_op_mono {d o d' o' : ℕ} (hd : d ≤ d') (ho : o ≤ o')
    {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)} (h : maOp Wp Wq d o Θ) : maOp Wp Wq d' o' Θ := by
  have hdr : (d : ℝ) ≤ d' := by exact_mod_cast hd
  have hdn : ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)) (b : ℝ),
      CCle (A + d') (m + o') F b → CCle (A + d) (m + o) F b := fun A m F b hF =>
    pd_ccle_mono (by linarith) (by omega) hF
  have hin : ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)),
      InCC (A + d') (m + o') F → InCC (A + d) (m + o) F := fun A m F ⟨b, hb⟩ => ⟨b, hdn A m F b hb⟩
  refine ⟨fun A m => ?_, fun A m F F' c hF hF' => h.2.1 A m F F' c (hin A m F hF) (hin A m F' hF'),
    fun A m F F' hF hF' hE => h.2.2 A m F F' (hin A m F hF) (hin A m F' hF') hE⟩
  obtain ⟨K, hK0, hK⟩ := h.1 A m
  exact ⟨K, hK0, fun F b hF => hK F b (hdn A m F b hF)⟩

theorem ma_op_comp {d₁ o₁ d₂ o₂ d o : ℕ} (hd : d₁ + d₂ ≤ d) (ho : o₁ + o₂ ≤ o)
    {Θ₁ Θ₂ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)} (h₁ : maOp Wp Wq d₁ o₁ Θ₁)
    (h₂ : maOp Wp Wq d₂ o₂ Θ₂) : maOp Wp Wq d o (fun F => Θ₁ (Θ₂ F)) := by
  have hdr : (d₁ : ℝ) + d₂ ≤ d := by exact_mod_cast hd
  have hin : ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)), InCC (A + d) (m + o) F →
      InCC (A + d₁ + d₂) (m + o₁ + o₂) F := fun A m F ⟨b, hb⟩ =>
    ⟨b, pd_ccle_mono (by linarith) (by omega) hb⟩
  refine ⟨fun A m => ?_, fun A m F F' c hF hF' g hg => ?_, fun A m F F' hF hF' hE g hg => ?_⟩
  · obtain ⟨K₁, hK₁0, hK₁⟩ := h₁.1 A m
    obtain ⟨K₂, hK₂0, hK₂⟩ := h₂.1 (A + d₁) (m + o₁)
    refine ⟨K₁ * K₂, mul_nonneg hK₁0 hK₂0, fun F b hF => ?_⟩
    rw [mul_assoc]
    exact hK₁ _ _ (hK₂ F b (pd_ccle_mono (by linarith) (by omega) hF))
  · have h2F : InCC (A + d₁) (m + o₁) (Θ₂ F) := ma_inCC h₂ (hin A m F hF)
    have h2F' : InCC (A + d₁) (m + o₁) (Θ₂ F') := ma_inCC h₂ (hin A m F' hF')
    have h2s : InCC (A + d₁) (m + o₁) (Θ₂ (F + c • F')) :=
      ma_inCC h₂ (hin A m _ (ma_inCC_lin c hF hF'))
    have hE : ∀ g ∈ GV k r, Θ₂ (F + c • F') g = (Θ₂ F + c • Θ₂ F') g := fun g hg =>
      h₂.2.1 (A + d₁) (m + o₁) F F' c (hin A m F hF) (hin A m F' hF') g hg
    show Θ₁ (Θ₂ (F + c • F')) g = Θ₁ (Θ₂ F) g + c • Θ₁ (Θ₂ F') g
    rw [h₁.2.2 A m _ _ h2s (ma_inCC_lin c h2F h2F') hE g hg]
    exact h₁.2.1 A m _ _ c h2F h2F' g hg
  · have h2F : InCC (A + d₁) (m + o₁) (Θ₂ F) := ma_inCC h₂ (hin A m F hF)
    have h2F' : InCC (A + d₁) (m + o₁) (Θ₂ F') := ma_inCC h₂ (hin A m F' hF')
    exact h₁.2.2 A m _ _ h2F h2F'
      (fun g hg => h₂.2.2 (A + d₁) (m + o₁) F F' (hin A m F hF) (hin A m F' hF') hE g hg) g hg

theorem ma_op_id : maOp Wp Wq 0 0 (fun F : Mat k r → (Wq →L[ℂ] Wp) => F) := by
  refine ⟨fun A m => ⟨1, zero_le_one, fun F b hF => ?_⟩, fun A m F F' c _ _ g _ => rfl,
    fun A m F F' _ _ hE g hg => hE g hg⟩
  rw [one_mul]
  simpa using hF

theorem ma_op_zero (d o : ℕ) :
    maOp Wp Wq d o (fun (_ : Mat k r → (Wq →L[ℂ] Wp)) (_ : Mat k r) => (0 : Wq →L[ℂ] Wp)) := by
  refine ⟨fun A m => ⟨0, le_rfl, fun F b _ => ?_⟩, fun A m F F' c _ _ g _ => by simp,
    fun A m F F' _ _ _ g _ => rfl⟩
  rw [zero_mul]
  exact CCle_zero

theorem ma_op_add {d o : ℕ} {Θ₁ Θ₂ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : maOp Wp Wq d o Θ₁) (h₂ : maOp Wp Wq d o Θ₂) : maOp Wp Wq d o (fun F g => Θ₁ F g + Θ₂ F g) := by
  refine ⟨fun A m => ?_, fun A m F F' c hF hF' g hg => ?_, fun A m F F' hF hF' hE g hg => ?_⟩
  · obtain ⟨K₁, hK₁, h1⟩ := h₁.1 A m
    obtain ⟨K₂, hK₂, h2⟩ := h₂.1 A m
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, fun F b hF => ?_⟩
    rw [add_mul]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add (h1 F b hF) (h2 F b hF)
  · show Θ₁ (F + c • F') g + Θ₂ (F + c • F') g = (Θ₁ F g + Θ₂ F g) + c • (Θ₁ F' g + Θ₂ F' g)
    rw [h₁.2.1 A m F F' c hF hF' g hg, h₂.2.1 A m F F' c hF hF' g hg, smul_add]
    abel
  · show Θ₁ F g + Θ₂ F g = Θ₁ F' g + Θ₂ F' g
    rw [h₁.2.2 A m F F' hF hF' hE g hg, h₂.2.2 A m F F' hF hF' hE g hg]

theorem ma_op_smul {d o : ℕ} (a : ℂ) {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h : maOp Wp Wq d o Θ) : maOp Wp Wq d o (fun F g => a • Θ F g) := by
  refine ⟨fun A m => ?_, fun A m F F' c hF hF' g hg => ?_, fun A m F F' hF hF' hE g hg => ?_⟩
  · obtain ⟨K, hK0, hK⟩ := h.1 A m
    refine ⟨‖a‖ * K, mul_nonneg (norm_nonneg a) hK0, fun F b hF => ?_⟩
    rw [mul_assoc]
    exact CCle_smul a (hK F b hF)
  · show a • Θ (F + c • F') g = a • Θ F g + c • (a • Θ F' g)
    rw [h.2.1 A m F F' c hF hF' g hg, smul_add, smul_comm a c]
  · show a • Θ F g = a • Θ F' g
    rw [h.2.2 A m F F' hF hF' hE g hg]

theorem ma_op_neg {d o : ℕ} {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h : maOp Wp Wq d o Θ) : maOp Wp Wq d o (fun F g => -Θ F g) := by
  refine ⟨fun A m => ?_, fun A m F F' c hF hF' g hg => ?_, fun A m F F' hF hF' hE g hg => ?_⟩
  · obtain ⟨K, hK0, hK⟩ := h.1 A m
    refine ⟨K, hK0, fun F b hF => ?_⟩
    have h1 := CCle_smul (-1 : ℂ) (hK F b hF)
    simpa using h1
  · show -Θ (F + c • F') g = -Θ F g + c • -Θ F' g
    rw [h.2.1 A m F F' c hF hF' g hg, smul_neg, neg_add]
  · show -Θ F g = -Θ F' g
    rw [h.2.2 A m F F' hF hF' hE g hg]

theorem ma_op_sum {d o : ℕ} {ι : Type*} (s : Finset ι)
    (Θ : ι → (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ i ∈ s, maOp Wp Wq d o (Θ i)) : maOp Wp Wq d o (fun F g => ∑ i ∈ s, Θ i F g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ma_op_congr (ma_op_zero d o) (fun F => by funext g; simp)
  | @insert i s hi ih =>
    have hadd := ma_op_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact ma_op_congr hadd (fun F => by funext g; simp only [Finset.sum_insert hi])

theorem ma_op_coef {d d' o d'' : ℕ} (hd : d + d' ≤ d'') {c : Mat k r → ℂ} (hc : pdGood Wp Wq d c)
    {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)} (h : maOp Wp Wq d' o Θ) :
    maOp Wp Wq d'' o (fun F g => c g • Θ F g) := by
  have hdr : (d : ℝ) + d' ≤ d'' := by exact_mod_cast hd
  have hin : ∀ (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)), InCC (A + d'') (m + o) F →
      InCC (A + d + d') (m + o) F := fun A m F ⟨b, hb⟩ => ⟨b, pd_ccle_mono (by linarith) le_rfl hb⟩
  refine ⟨fun A m => ?_, fun A m F F' a hF hF' g hg => ?_, fun A m F F' hF hF' hE g hg => ?_⟩
  · obtain ⟨Kc, hKc0, hKc⟩ := hc.2 A m
    obtain ⟨K, hK0, hK⟩ := h.1 (A + d) m
    refine ⟨Kc * K, mul_nonneg hKc0 hK0, fun F b hF => ?_⟩
    rw [mul_assoc]
    exact hKc _ _ (hK F b (pd_ccle_mono (by linarith) le_rfl hF))
  · show c g • Θ (F + a • F') g = c g • Θ F g + a • (c g • Θ F' g)
    rw [h.2.1 (A + d) m F F' a (hin A m F hF) (hin A m F' hF') g hg, smul_add, smul_comm (c g) a]
  · show c g • Θ F g = c g • Θ F' g
    rw [h.2.2 (A + d) m F F' (hin A m F hF) (hin A m F' hF') hE g hg]

theorem ma_op_ite {d o : ℕ} (P : Prop) [Decidable P] {Θ : (Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)}
    (h : P → maOp Wp Wq d o Θ) : maOp Wp Wq d o (fun F g => if P then Θ F g else 0) := by
  by_cases hP : P
  · exact ma_op_congr (h hP) (fun F => by funext g; simp [hP])
  · exact ma_op_congr (ma_op_zero d o) (fun F => by funext g; simp [hP])

theorem finite_class_locally_C1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ} {F : Mat k r → E}
    (hF : InCC A (m + 1) F) {g : Mat k r} (hg : g ∈ GV k r) : Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc 1 F g := by
  obtain ⟨b, hb⟩ := hF
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hb.1 g hg
  refine Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono (m' := ((m + 1 : ℕ) : ℕ∞)) ?_ ⟨U, f', hU, hgU, hc, he⟩
  exact_mod_cast Nat.le_add_left 1 m

theorem ma_op_RdV {X : Mat k r} (hX : unitLie k r X) : maOp Wp Wq 0 1 (RdV X) := by
  refine ⟨fun A m => ?_, fun A m F F' c hF hF' g hg => ?_, fun A m F F' hF hF' hE g hg => ?_⟩
  · refine ⟨1, zero_le_one, fun F b hF => ?_⟩
    have hXl : ∀ Y ∈ [X], unitLie k r Y := by simpa using hX
    have := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw (m := m) hXl (by simpa using hF)
    simpa [Rw] using this
  · exact Formalism.FourierDecayAlt.P.LieDecompositionLocal.rdV_fun_add (finite_class_locally_C1 hF hg) (finite_class_locally_C1 hF' hg) hg hX.1 c
  · have hc : ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ GV k r := fun t => by
      have := Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_mem (x := (false, X)) hX.1 hg t
      simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv] using this
    show deriv (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
      deriv (fun t : ℝ => F' (g * NormedSpace.exp ((t : ℂ) • X))) 0
    congr 1
    funext t
    exact hE _ (hc t)

end maOps

section maTL

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx2

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem ma_op_EH (a b : Fin (2 * r + k + 1)) : maOp Wp Wq 0 1 (Q.EH k r a b) :=
  ma_op_congr (ma_op_add (ma_op_RdV (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xa_unit a b))
    (ma_op_smul Complex.I (ma_op_RdV (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Xb_unit a b)))) (fun _ => rfl)

theorem ma_op_Top (u : ℂ) (a b : Fin (2 * r + k + 1)) : maOp Wp Wq 0 1 (Top (Q.EH k r) u a b) := by
  have h1 : maOp Wp Wq 0 1 (fun (F : Mat k r → (Wq →L[ℂ] Wp)) g => if a = b then u • F g else 0) :=
    ma_op_ite (a = b) (fun _ => ma_op_mono le_rfl zero_le_one (ma_op_smul u ma_op_id))
  exact ma_op_congr (ma_op_add h1 (ma_op_EH a b)) (fun F => rfl)

theorem ma_op_foldr (l : List ((Mat k r → (Wq →L[ℂ] Wp)) → Mat k r → (Wq →L[ℂ] Wp)))
    (hl : ∀ T ∈ l, maOp Wp Wq 0 1 T) : maOp Wp Wq 0 l.length (fun F => l.foldr (fun T h => T h) F) := by
  induction l with
  | nil => exact ma_op_congr ma_op_id (fun F => rfl)
  | cons T l ih =>
    have hT := hl T (List.mem_cons.2 (Or.inl rfl))
    have hl' := ih (fun T' hT' => hl T' (List.mem_cons.2 (Or.inr hT')))
    exact ma_op_congr (ma_op_comp (by norm_num) (by simp only [List.length_cons]; omega) hT hl') (fun F => rfl)

theorem ma_op_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    maOp Wp Wq 0 t (qminorOp (Q.EH k r) a b u) := by
  have hT : ∀ σ : Equiv.Perm (Fin t), maOp Wp Wq 0 t (fun F => (List.ofFn fun i : Fin t =>
      Top (Q.EH k r) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i)).foldr (fun T h => T h) F) := by
    intro σ
    have h1 := ma_op_foldr (Wp := Wp) (Wq := Wq) (List.ofFn fun i : Fin t =>
      Top (Q.EH k r) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i)) (by
        intro T hT
        rw [List.mem_ofFn] at hT
        obtain ⟨i, rfl⟩ := hT
        exact ma_op_Top _ _ _)
    simpa only [List.length_ofFn] using h1
  have hs := ma_op_sum (Wp := Wp) (Wq := Wq) (d := 0) (o := t) Finset.univ
    (fun σ F g => (((Equiv.Perm.sign σ : ℤ) : ℂ)) • (List.ofFn fun i : Fin t =>
      Top (Q.EH k r) (u - ((i : ℕ) : ℂ)) (a (σ i)) (b i)).foldr (fun T h => T h) F g)
    (fun σ _ => ma_op_smul _ (hT σ))
  refine ma_op_congr hs (fun F => ?_)
  funext g
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]

theorem ma_op_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) :
    maOp Wp Wq 2 (2 * r + k + 1) (Q.tL k r z z' 0 Y a b) := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  have hyv : ∀ j, pdGood Wp Wq 1 (fun g => Q.yv k r z 0 g j) := fun j => pd_good_inv _ _
  have hybv : ∀ j, pdGood Wp Wq 1 (fun g => Q.ybv k r z 0 g j) := fun j => pd_good_herm _ _
  have base : ∀ {t : ℕ} (P Q' : Fin t → Fin (2 * r + k + 1)) (u : ℂ), t ≤ 2 * r + k + 1 →
      maOp Wp Wq 0 (2 * r + k + 1) (qminorOp (Q.EH k r) P Q' u) :=
    fun P Q' u ht => ma_op_mono le_rfl ht (ma_op_qminorOp P Q' u)
  fin_cases a <;> fin_cases b
  · exact ma_op_mono (Nat.zero_le 2) (by rw [hm]) (ma_op_qminorOp _ _ _)
  · refine ma_op_congr (ma_op_neg (ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      ma_op_coef (d := 2) (by omega)
        (c := fun x => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * Q.ybv k r z 0 x i * Q.xv k r z' 0 j)
        (pd_good_mul (d₁ := 2) (d₂ := 0) (by omega)
          (pd_good_mul (d₁ := 0) (d₂ := 1) (by omega) (pd_good_const 0 _) (hybv i)) (pd_good_const 0 _))
        (base (Q.posL k r 0 ∘ Q.skip1 i) (Q.posL k r 0 ∘ Q.skip1 j) (Q.uC k r 0 Y - 1)
          (by rw [hm]; omega)))) (fun f => rfl)
  · refine ma_op_congr (ma_op_neg (ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      ma_op_coef (d := 2) (by omega)
        (c := fun x => (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * Q.xbv k r z' 0 i * Q.yv k r z 0 x j)
        (pd_good_mul (d₁ := 0) (d₂ := 1) (by omega) (pd_good_const 0 _) (hyv j))
        (base (Q.posL k r 0 ∘ Q.skip1 i) (Q.posL k r 0 ∘ Q.skip1 j) (Q.uC k r 0 Y)
          (by rw [hm]; omega)))) (fun f => rfl)
  · refine ma_op_congr (ma_op_neg (ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i _ =>
      ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun i' _ =>
      ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j _ =>
      ma_op_sum (Finset.univ : Finset (Fin (Q.mdim k r 0))) _ fun j' _ =>
      ma_op_ite (i < i' ∧ j < j') fun _ => ma_op_coef (d := 2) (by omega) (c := fun x =>
        ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) *
          (Q.ybv k r z 0 x i * Q.xbv k r z' 0 i' - Q.ybv k r z 0 x i' * Q.xbv k r z' 0 i) *
          (Q.yv k r z 0 x j * Q.xv k r z' 0 j' - Q.yv k r z 0 x j' * Q.xv k r z' 0 j)))
        (pd_good_mul (d₁ := 1) (d₂ := 1) (by omega)
          (pd_good_mul (d₁ := 0) (d₂ := 1) (by omega) (pd_good_const 0 _)
            (pd_good_sub (pd_good_mul (d₁ := 1) (d₂ := 0) (by omega) (hybv i) (pd_good_const 0 _))
              (pd_good_mul (d₁ := 1) (d₂ := 0) (by omega) (hybv i') (pd_good_const 0 _))))
          (pd_good_sub (pd_good_mul (d₁ := 1) (d₂ := 0) (by omega) (hyv j) (pd_good_const 0 _))
            (pd_good_mul (d₁ := 1) (d₂ := 0) (by omega) (hyv j') (pd_good_const 0 _))))
        (base (Q.posL k r 0 ∘ Q.skip2 i i') (Q.posL k r 0 ∘ Q.skip2 j j') (Q.uC k r 0 Y - 1)
          (by rw [hm]; omega)))) (fun f => rfl)

def maS (N : ℕ) (Θ : D.Op (Mat k r → (Wq →L[ℂ] Wp))) : Prop :=
  maOp Wp Wq (2 * N) ((2 * r + k + 1) * N) Θ

theorem ma_S_gr : sqGr (maS (k := k) (r := r) (Wp := Wp) (Wq := Wq)) where
  zero N := ma_op_congr (ma_op_zero _ _) (fun F => rfl)
  one := ma_op_congr (ma_op_mono (Nat.zero_le _) (Nat.zero_le _) ma_op_id) (fun F => rfl)
  add N a b ha hb := ma_op_congr (ma_op_add ha hb) (fun F => rfl)
  mul N M a b ha hb := ma_op_congr (ma_op_comp (by ring_nf; omega) (by ring_nf; omega) ha hb) (fun F => rfl)
  cop c := ma_op_congr (ma_op_mono (Nat.zero_le _) (Nat.zero_le _) (ma_op_smul c ma_op_id)) (fun F => rfl)
  mono N a ha := ma_op_mono (by omega) (by ring_nf; omega) ha

theorem ma_S_tL (z z' : Fin (2 * r + k + 1) → ℂ) (s Y : ℂ) (a b : Fin 2) :
    maS (Wp := Wp) (Wq := Wq) 1 ((fun f => s • Q.tL k r z z' 0 Y a b f : D.Op (Mat k r → (Wq →L[ℂ] Wp)))) := by
  exact ma_op_congr (ma_op_mono (by norm_num) (le_of_eq (Nat.mul_one _).symm)
    (ma_op_smul s (ma_op_tL z z' Y a b))) (fun F => rfl)

end maTL

section maForm

open Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx2
open scoped ComplexConjugate

theorem ma_hS {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) :
    ∀ a b, maS (k := P0.k) (r := P0.r - j) (Wp := Wp) (Wq := Wq) w.length (D.RRlev T s j w a b) := by
  have h := sq_rrop (S := maS (k := P0.k) (r := P0.r - ↑j) (Wp := Wp) (Wq := Wq)) ma_S_gr (D.QQlev T s j)
    (fun Y p q => ma_S_tL (T.bs j).z (T.bs j).z' s Y p q) (D.positionted w)
  have hlen : (D.positionted w).length = w.length := by simp [D.positionted]
  rw [hlen] at h
  exact h

theorem ma_actOp_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)
    (v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (a : Wd.Ix (Fin w.length)) :
    D.actOp (D.RRlev T s j w) v a = fun g => ∑ b, (D.RRlev T s j w a b) (v b) g := by
  funext g
  simp [D.actOp, D.ap, Finset.sum_apply]

theorem formLev_sesq_core {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ) (mm : ℕ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) (hmm : P5.mmUser P0 w.length ≤ mm)
    (x x' y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : ∀ a, InCC A mm (x a)) (hx' : ∀ a, InCC A mm (x' a)) (hy : ∀ a, InCC A mm (y a)) :
    D.formLev T s j w (x + c • x') y = D.formLev T s j w x y + c * D.formLev T s j w x' y ∧
      D.formLev T s j w y (x + c • x') = D.formLev T s j w y x + starRingEnd ℂ c * D.formLev T s j w y x' := by
  have hS := ma_hS P0 T s j w

  have hAB : AB P0.k (P0.r - ↑j) ≤ A - 2 * (w.length : ℝ) := by
    have h1 := pd_thr_AB P0 j w.length A hA
    linarith
  have hm5 : 5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _

  have hin : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ) + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - ↑j) + P0.k + 1) * w.length) F :=
    fun h => sq_inCC_mono (by push_cast; linarith) hm5 h

  have hvec : ∀ v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp),
      (∀ a, InCC A mm (v a)) → ∀ a,
        InCC (A - 2 * (w.length : ℝ)) 5 (D.actOp (D.RRlev T s j w) v a) := by
    intro v hv a
    rw [ma_actOp_eq]
    exact sq_inCC_sum Finset.univ (fun b => (D.RRlev T s j w a b) (v b)) (fun b _ => ma_inCC (hS a b) (hin (hv b)))
  have hlow : ∀ {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}, InCC A mm F →
      InCC (A - 2 * (w.length : ℝ)) 5 F := fun h =>
    sq_inCC_mono (by linarith) (by omega) h
  refine ⟨?_, ?_⟩
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) (x + c • x') a) (y a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x a) (y a) +
        c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) x' a) (y a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hGV : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T s j w) (x + c • x') a g =
        (D.actOp (D.RRlev T s j w) x a + c • D.actOp (D.RRlev T s j w) x' a) g := by
      intro g hg
      show (∑ b, D.ap (D.RRlev T s j w a b) ((x + c • x') b)) g =
        (∑ b, D.ap (D.RRlev T s j w a b) (x b) + c • ∑ b, D.ap (D.RRlev T s j w a b) (x' b)) g
      rw [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      exact (hS a b).2.1 _ _ (x b) (x' b) c (hin (hx b)) (hin (hx' b)) g hg
    rw [sq_beta_congr (T.bs j) hGV]
    exact (sq_beta_sesq (T.bs j) hAB (hvec x hx a) (hvec x' hx' a) (hlow (hy a)) c).1
  · show ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) ((x + c • x') a) =
      ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x a) +
        conj c * ∑ a, beta (T.bs j) (D.actOp (D.RRlev T s j w) y a) (x' a)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact (sq_beta_sesq (T.bs j) hAB (hlow (hx a)) (hlow (hx' a)) (hvec y hy a) c).2

theorem formLev_bound_mm {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (A : ℝ)
    (hA : P5.Auser P0 w.length + 1 ≤ A) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (u v : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (cu cv : ℝ),
      (∀ b, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (u b) cu) →
      (∀ a, CCle (A - 1 - 2 * (w.length : ℝ)) 5 (v a) cv) →
      ‖D.formLev T s j w u v‖ ≤ Cf * cu * cv := by
  have hR := ma_hS P0 T s j w
  set A'' : ℝ := A - 1 - 2 * (w.length : ℝ) with hA''
  have hop : ∀ a b, ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (c : ℝ),
      CCle (A'' + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - j) + P0.k + 1) * w.length) F c →
      CCle A'' 5 (D.RRlev T s j w a b F) (K * c) := fun a b => (hR a b).1 A'' 5
  choose K hK0 hK using hop
  set KK : ℝ := ∑ a, ∑ b, K a b with hKK
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hK0 a b
  have hKab : ∀ a, ∑ b, K a b ≤ KK := fun a =>
    Finset.single_le_sum (f := fun a => ∑ b, K a b) (fun a _ => Finset.sum_nonneg fun b _ => hK0 a b)
      (Finset.mem_univ a)
  have hAB : AB P0.k (P0.r - j) ≤ A'' := pd_thr_AB P0 j w.length A hA
  obtain ⟨_, _, _, hB1, _, _, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi P0.k (P0.r - j) Wp Wq (T.bs j) A'' hAB
  obtain ⟨Cβ, hCβ⟩ := hB1
  have hA2 : A'' + ((2 * w.length : ℕ) : ℝ) = A - 1 := by rw [hA'']; push_cast; ring
  set card : ℝ := (Fintype.card (Wd.Ix (Fin w.length)) : ℝ)
  have hcard : 0 ≤ card := Nat.cast_nonneg _
  refine ⟨card * (|Cβ| * KK), mul_nonneg hcard (mul_nonneg (abs_nonneg _) hKK0), ?_⟩
  intro u v cu cv hcu hcv
  have hcu0 : 0 ≤ cu := pd_ccle_nonneg (hcu (Classical.arbitrary _))
  have hcv0 : 0 ≤ cv := pd_ccle_nonneg (hcv (Classical.arbitrary _))
  have hu' : ∀ b, CCle (A'' + ((2 * w.length : ℕ) : ℝ)) (5 + (2 * (P0.r - j) + P0.k + 1) * w.length) (u b) cu :=
    fun b => pd_ccle_mono (le_of_eq hA2) le_rfl (hcu b)
  have hRu : ∀ a, CCle A'' 5 (D.actOp (D.RRlev T s j w) u a) (KK * cu) := by
    intro a
    rw [ma_actOp_eq]
    refine pd_ccle_mono_c (pd_ccle_sum Finset.univ (fun b => D.RRlev T s j w a b (u b)) (fun b => K a b * cu)
      fun b _ => hK a b (u b) cu (hu' b)) ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hKab a) hcu0
  unfold D.formLev
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ a, ‖B.beta (T.bs j) (D.actOp (D.RRlev T s j w) u a) (v a)‖ ≤ |Cβ| * (KK * cu) * cv := by
    intro a
    have h := (hCβ _ _ _ _ ⟨_, hRu a⟩ ⟨_, hcv a⟩ (pd_ccle_mono le_rfl (by norm_num) (hRu a))
      (pd_ccle_mono le_rfl (by norm_num) (hcv a))).2.2
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hKK0 hcu0)) hcv0
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply le_of_eq
  ring

end maForm

end Formalism.FourierDecayAlt.P.JCx4

namespace Formalism.FourierDecayAlt.P.JCx4

section partB

open Formalism.FourierDecayAlt.P.BetaSesquilinearity

abbrev mbV (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def mb_e (k r : ℕ) : mbV k r ≃ₗᵢ[ℝ] Mat k r :=
  { toLinearEquiv := Matrix.ofLinearEquiv ℝ
    norm_map' := fun _ => rfl }

noncomputable def mb_L (x : Bool × Mat k r) : mbV k r →L[ℝ] mbV k r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => (mb_e k r).symm (dirv x (mb_e k r v))
      map_add' := fun a b => by
        obtain ⟨b0, X⟩ := x
        cases b0 <;> simp [dirv, Matrix.mul_add, Matrix.add_mul, map_add] <;> abel
      map_smul' := fun c a => by
        obtain ⟨b0, X⟩ := x
        cases b0 <;> simp [dirv, map_smul] }

theorem mb_L_apply (x : Bool × Mat k r) (v : mbV k r) :
    mb_L x v = (mb_e k r).symm (dirv x (mb_e k r v)) := rfl

theorem mb_dirv_norm (x : Bool × Mat k r) (hx : ‖x.2‖ ≤ 1) (g : Mat k r) :
    ‖dirv x g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ := by
  obtain ⟨b0, X⟩ := x
  cases b0
  · show ‖g * X‖ ≤ _
    calc ‖g * X‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ * ‖X‖ := Formalism.FourierDecayAlt.P.JCx2.mn_norm_mul_le g X
      _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ * 1 := by gcongr
      _ = _ := by ring
  · show ‖-X * g‖ ≤ _
    calc ‖-X * g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖-X‖ * ‖g‖ := Formalism.FourierDecayAlt.P.JCx2.mn_norm_mul_le (-X) g
      _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * 1 * ‖g‖ := by rw [norm_neg]; gcongr
      _ = _ := by ring

theorem mb_L_norm (x : Bool × Mat k r) (hx : ‖x.2‖ ≤ 1) :
    ‖mb_L x‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  rw [mb_L_apply, LinearIsometryEquiv.norm_map]
  have h1 := mb_dirv_norm x hx (mb_e k r v)
  rwa [LinearIsometryEquiv.norm_map] at h1

theorem mb_L_iter (x : Bool × Mat k r) (hx : ‖x.2‖ ≤ 1) (j : ℕ) (g : mbV k r) :
    ‖iteratedFDeriv ℝ j (mb_L x) g‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (1 + ‖g‖) := by
  have hL := mb_L_norm x hx
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  have hg : 0 ≤ ‖g‖ := norm_nonneg g
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    calc ‖mb_L x g‖ ≤ ‖mb_L x‖ * ‖g‖ := (mb_L x).le_opNorm g
      _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * ‖g‖ := by gcongr
      _ ≤ _ := by nlinarith
  | succ j =>
    rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (mb_L x) = fun _ => mb_L x := funext fun y => (mb_L x).fderiv
    rw [e]
    cases j with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      calc ‖mb_L x‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) := hL
        _ ≤ _ := by nlinarith
    | succ j =>
      rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
      positivity

noncomputable def mb_DxV (x : Bool × Mat k r) (F : mbV k r → E) : mbV k r → E :=
  fun v => fderiv ℝ F v (mb_L x v)

noncomputable def mb_DwV (w : List (Bool × Mat k r)) (F : mbV k r → E) : mbV k r → E := w.foldr mb_DxV F

theorem mb_DxV_contDiff (x : Bool × Mat k r) {N : ℕ} {F : mbV k r → E}
    (hF : ContDiff ℝ (((N + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (mb_DxV x F) := by
  unfold mb_DxV
  have h1 : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by norm_cast)
  exact h1.clm_apply (mb_L x).contDiff

theorem mb_DwV_contDiff (w : List (Bool × Mat k r)) (j : ℕ) {F : mbV k r → E}
    (hF : ContDiff ℝ (((w.length + j : ℕ) : ℕ∞) : WithTop ℕ∞) F) :
    ContDiff ℝ ((j : ℕ∞) : WithTop ℕ∞) (mb_DwV w F) := by
  induction w generalizing j with
  | nil => simpa [mb_DwV] using hF
  | cons x w ih =>
    have e : (x :: w).length + j = w.length + (j + 1) := by simp only [List.length_cons]; omega
    rw [e] at hF
    exact mb_DxV_contDiff x (ih (j + 1) hF)

theorem mb_letter (x : Bool × Mat k r) (hx : ‖x.2‖ ≤ 1) (i : ℕ) {F : mbV k r → E}
    (hF : ContDiff ℝ (((i + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F) (g : mbV k r) :
    ‖iteratedFDeriv ℝ i (mb_DxV x F) g‖ ≤
      (((i : ℝ) + 1) * 2 ^ i * ((2 * r + k + 1 : ℕ) : ℝ)) * (1 + ‖g‖) *
        ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l F g‖ := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  set S : ℝ := ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l F g‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : ContDiff ℝ ((i : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) := hF.fderiv_right (by push_cast; exact le_rfl)
  have h2 : ContDiff ℝ ((i : ℕ∞) : WithTop ℕ∞) (mb_L x) := (mb_L x).contDiff
  have hB : ‖ContinuousLinearMap.id ℝ (mbV k r →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have key := (ContinuousLinearMap.id ℝ (mbV k r →L[ℝ] E)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    h1 h2 g (n := i) (by exact_mod_cast le_rfl) hB
  simp only [ContinuousLinearMap.id_apply] at key
  refine key.trans ?_
  have hterm : ∀ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fderiv ℝ F) g‖ *
      ‖iteratedFDeriv ℝ (i - l) (mb_L x) g‖ ≤ 2 ^ i * (n * (1 + ‖g‖)) * S := by
    intro l hl
    have hl' : l + 1 < i + 2 := by simp at hl; omega
    have c1 : (i.choose l : ℝ) ≤ 2 ^ i := by exact_mod_cast Nat.choose_le_two_pow i l
    have c2 : ‖iteratedFDeriv ℝ l (fderiv ℝ F) g‖ ≤ S := by
      rw [norm_iteratedFDeriv_fderiv]
      exact Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l F g‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.2 hl')
    have c3 := mb_L_iter x hx (i - l) g
    calc (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fderiv ℝ F) g‖ * ‖iteratedFDeriv ℝ (i - l) (mb_L x) g‖
        ≤ 2 ^ i * S * (n * (1 + ‖g‖)) := by gcongr
      _ = 2 ^ i * (n * (1 + ‖g‖)) * S := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  nlinarith [hS0, hn0, norm_nonneg g, pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) i]

theorem mb_sum_mono (F : mbV k r → E) (g : mbV k r) {a b : ℕ} (h : a ≤ b) :
    ∑ l ∈ Finset.range a, ‖iteratedFDeriv ℝ l F g‖ ≤ ∑ l ∈ Finset.range b, ‖iteratedFDeriv ℝ l F g‖ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) (fun _ _ _ => norm_nonneg _)

theorem word_derivative_polynomial_bound (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : List (Bool × Mat k r), (∀ x ∈ w, ‖x.2‖ ≤ 1) →
    w.length ≤ N → ∀ F : mbV k r → E, ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) F → ∀ g : mbV k r,
      ‖mb_DwV w F g‖ ≤ C * (1 + ‖g‖) ^ N * ∑ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ i F g‖ := by
  induction N with
  | zero =>
    refine ⟨1, zero_le_one, fun w _ hw F _ g => ?_⟩
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    show ‖F g‖ ≤ _
    simp [norm_iteratedFDeriv_zero]
  | succ N ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
    have hn0 : 0 ≤ n := by positivity
    refine ⟨max 1 (C * (((N : ℝ) + 1) ^ 2 * 2 ^ N * n)), le_trans zero_le_one (le_max_left _ _), ?_⟩
    intro w hw hl F hF g
    have hg1 : 1 ≤ 1 + ‖g‖ := by linarith [norm_nonneg g]
    have hg0 : 0 ≤ 1 + ‖g‖ := by linarith
    set S : ℝ := ∑ i ∈ Finset.range (N + 1 + 1), ‖iteratedFDeriv ℝ i F g‖ with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hpow : 1 ≤ (1 + ‖g‖) ^ (N + 1) := one_le_pow₀ hg1
    rcases List.eq_nil_or_concat w with h | ⟨w', x, rfl⟩
    · subst h
      have e1 : ‖mb_DwV [] F g‖ ≤ S := by
        show ‖F g‖ ≤ S
        rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
        exact Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l F g‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
      calc ‖mb_DwV [] F g‖ ≤ 1 * 1 * S := by simpa using e1
        _ ≤ max 1 (C * (((N : ℝ) + 1) ^ 2 * 2 ^ N * n)) * (1 + ‖g‖) ^ (N + 1) * S := by
          gcongr
          exact le_max_left _ _
    · simp only [List.concat_eq_append] at hw hl ⊢
      have hx : ‖x.2‖ ≤ 1 := hw x (by simp)
      have hw' : ∀ y ∈ w', ‖y.2‖ ≤ 1 := fun y hy => hw y (by simp [hy])
      have hl' : w'.length ≤ N := by simp at hl; omega
      have e : mb_DwV (w' ++ [x]) F = mb_DwV w' (mb_DxV x F) := by
        simp [mb_DwV, List.foldr_append]
      rw [e]
      have hF' : ContDiff ℝ ((N : ℕ∞) : WithTop ℕ∞) (mb_DxV x F) := mb_DxV_contDiff x hF
      have b1 := hC w' hw' hl' (mb_DxV x F) hF' g
      have b2 : ∀ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ i (mb_DxV x F) g‖ ≤
          (((N : ℝ) + 1) * 2 ^ N * n) * (1 + ‖g‖) * S := by
        intro i hi
        have hi' : i ≤ N := by simp at hi; omega
        have hFi : ContDiff ℝ (((i + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F := hF.of_le (by norm_cast; omega)
        refine (mb_letter x hx i hFi g).trans ?_
        have q1 : ((i : ℝ) + 1) * 2 ^ i * n ≤ ((N : ℝ) + 1) * 2 ^ N * n := by
          have : (i : ℝ) ≤ N := by exact_mod_cast hi'
          have : (2 : ℝ) ^ i ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hi'
          gcongr
        have q2 : ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l F g‖ ≤ S := mb_sum_mono F g (by omega)
        have q3 : 0 ≤ ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l F g‖ :=
          Finset.sum_nonneg fun _ _ => norm_nonneg _
        calc ((i : ℝ) + 1) * 2 ^ i * n * (1 + ‖g‖) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l F g‖
            ≤ ((N : ℝ) + 1) * 2 ^ N * n * (1 + ‖g‖) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l F g‖ := by
              gcongr
          _ ≤ _ := by gcongr
      have b3 : ∑ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ i (mb_DxV x F) g‖ ≤
          ((N : ℝ) + 1) * ((((N : ℝ) + 1) * 2 ^ N * n) * (1 + ‖g‖) * S) := by
        refine (Finset.sum_le_sum b2).trans ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        exact le_refl _
      calc ‖mb_DwV w' (mb_DxV x F) g‖
          ≤ C * (1 + ‖g‖) ^ N * ∑ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ i (mb_DxV x F) g‖ := b1
        _ ≤ C * (1 + ‖g‖) ^ N * (((N : ℝ) + 1) * ((((N : ℝ) + 1) * 2 ^ N * n) * (1 + ‖g‖) * S)) := by
          gcongr
        _ = (C * (((N : ℝ) + 1) ^ 2 * 2 ^ N * n)) * (1 + ‖g‖) ^ (N + 1) * S := by ring
        _ ≤ max 1 (C * (((N : ℝ) + 1) ^ 2 * 2 ^ N * n)) * (1 + ‖g‖) ^ (N + 1) * S := by
          gcongr
          exact le_max_right _ _

theorem Dx_comp_mb_e_symm (x : Bool × Mat k r) {G : mbV k r → E} (hG : Differentiable ℝ G) (g : Mat k r) :
    Dx x (fun M : Mat k r => G ((mb_e k r).symm M)) g = mb_DxV x G ((mb_e k r).symm g) := by
  refine (Dx_eq x _ g).trans ?_
  have h1 := crv_hasDerivAt x g
  have h1' : HasDerivAt (fun t => (mb_e k r).symm (crv x g t)) ((mb_e k r).symm (dirv x g)) 0 :=
    (mb_e k r).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have e0 : crv x g 0 = g := crv_zero x g
  have h2 : HasFDerivAt G (fderiv ℝ G ((mb_e k r).symm g)) ((mb_e k r).symm (crv x g 0)) := by
    rw [e0]
    exact (hG _).hasFDerivAt
  have h3 := (h2.comp_hasDerivAt (0 : ℝ) h1').deriv
  refine h3.trans ?_
  show fderiv ℝ G ((mb_e k r).symm g) ((mb_e k r).symm (dirv x g)) =
    fderiv ℝ G ((mb_e k r).symm g) ((mb_e k r).symm (dirv x (mb_e k r ((mb_e k r).symm g))))
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem mb_bridge (f : Mat k r → E) (w : List (Bool × Mat k r)) (j : ℕ)
    (hf : ContDiff ℝ (((w.length + j : ℕ) : ℕ∞) : WithTop ℕ∞) (fun v : mbV k r => f (mb_e k r v))) :
    ∀ g : Mat k r, Dw w f g = mb_DwV w (fun v : mbV k r => f (mb_e k r v)) ((mb_e k r).symm g) := by
  induction w generalizing j with
  | nil =>
    intro g
    show f g = f (mb_e k r ((mb_e k r).symm g))
    rw [LinearIsometryEquiv.apply_symm_apply]
  | cons x w ih =>
    intro g
    have ih' := ih (j + 1) (by
      have e : w.length + (j + 1) = (x :: w).length + j := by simp; omega
      rw [e]; exact hf)
    have hfun : Dw w f = fun M : Mat k r =>
        mb_DwV w (fun v : mbV k r => f (mb_e k r v)) ((mb_e k r).symm M) := funext ih'
    have hd : Differentiable ℝ (mb_DwV w (fun v : mbV k r => f (mb_e k r v))) := by
      have hc := mb_DwV_contDiff w (j + 1) (by
        have e : w.length + (j + 1) = (x :: w).length + j := by simp; omega
        rw [e]; exact hf)
      exact hc.differentiable (by norm_cast)
    show Dx x (Dw w f) g = mb_DxV x (mb_DwV w (fun v : mbV k r => f (mb_e k r v))) ((mb_e k r).symm g)
    rw [hfun]
    exact Dx_comp_mb_e_symm x hd g

end partB

theorem dlr_bound {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Mat k r → E, ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) f →
      ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) → u.length + v.length ≤ m →
        ∀ g : Mat k r, ‖dLR u v f g‖ ≤
          C * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i f g‖ := by
  obtain ⟨C, hC0, hC⟩ := word_derivative_polynomial_bound (k := k) (r := r) (E := E) m
  refine ⟨C, hC0, fun f hf u v hu hv hl g => ?_⟩
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
  have hunit : ∀ X : Mat k r, unitLie k r X → ‖X‖ ≤ 1 := fun X hX =>
    (Matrix.norm_le_iff zero_le_one).2 hX.2
  set w := Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v with hwdef
  have hlet : ∀ x ∈ w, ‖x.2‖ ≤ 1 := by
    intro x hx
    simp only [hwdef, List.mem_append, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact hunit X (hu X hX)
    · exact hunit X (hv X hX)
  have hlen : w.length ≤ m := by
    simp [hwdef, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR]; omega
  have hF : ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) (fun v : mbV k r => f (mb_e k r v)) :=
    hf.comp (mb_e k r).contDiff
  have hF' : ContDiff ℝ (((w.length + (m - w.length) : ℕ) : ℕ∞) : WithTop ℕ∞)
      (fun v : mbV k r => f (mb_e k r v)) := by
    have e : w.length + (m - w.length) = m := by omega
    rw [e]; exact hF
  rw [mb_bridge f w (m - w.length) hF' g]
  have hb := hC w hlet hlen _ hF ((mb_e k r).symm g)
  have hn : ‖(mb_e k r).symm g‖ = ‖g‖ := LinearIsometryEquiv.norm_map _ g
  have hi : ∀ i, ‖iteratedFDeriv ℝ i (fun v : mbV k r => f (mb_e k r v)) ((mb_e k r).symm g)‖ =
      ‖iteratedFDeriv ℝ i f g‖ := by
    intro i
    have := (mb_e k r).norm_iteratedFDeriv_comp_right f ((mb_e k r).symm g) i
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    exact this
  rw [hn] at hb
  simp only [hi] at hb
  exact hb

end Formalism.FourierDecayAlt.P.JCx4

namespace Formalism.FourierDecayAlt.P.JCx4

section partC

open MeasureTheory
open scoped Convolution

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem mc_precompR_lsmul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR V =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (V →L[ℝ] F) →L[ℝ] (V →L[ℝ] F)) := by
  ext a f v
  simp [ContinuousLinearMap.precompR]

theorem mc_fderiv_conv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (ρ : V → ℝ) (hρ : Continuous ρ) (h : V → F) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h) =
      ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] (fderiv ℝ h) := by
  funext x
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := Measure.addHaar)
    hρ.locallyIntegrable hh x
  rw [hd.fderiv, mc_precompR_lsmul]

theorem mc_iter (n : ℕ) : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (h : V → F),
    ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) h → HasCompactSupport h → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ φ : ContDiffBump (0 : V), φ.rOut < δ → ∀ x,
        ‖iteratedFDeriv ℝ n (fun x =>
          (φ.normed (Measure.addHaar : Measure V) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h) x
            - h x) x‖ ≤ η := by
  induction n with
  | zero =>
    intro F _ _ _ h hh hc η hη
    have huc : UniformContinuous h := hc.uniformContinuous_of_continuous hh.continuous
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.1 huc η hη
    refine ⟨δ, hδ, fun φ hφ x => ?_⟩
    rw [norm_iteratedFDeriv_zero, ← dist_eq_norm]
    refine dist_convolution_le (μ := (Measure.addHaar : Measure V)) hη.le
      (φ.support_normed_eq (μ := Measure.addHaar)).subset (φ.nonneg_normed) φ.integral_normed
      hh.continuous.aestronglyMeasurable fun x' hx' => ?_
    refine (hδ' ?_).le
    rw [Metric.mem_ball] at hx'
    exact hx'.trans hφ
  | succ n ih =>
    intro F _ _ _ h hh hc η hη
    have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hfd : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fderiv ℝ h) :=
      hh.fderiv_right (by push_cast; exact le_rfl)
    obtain ⟨δ, hδ, hδ'⟩ := ih (V →L[ℝ] F) (fderiv ℝ h) hfd (hc.fderiv ℝ) η hη
    refine ⟨δ, hδ, fun φ hφ x => ?_⟩
    set ρ := φ.normed (Measure.addHaar : Measure V) with hρ
    have hρc : Continuous ρ := φ.continuous_normed
    have hdy : Differentiable ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h) := fun x =>
      (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := Measure.addHaar)
        hρc.locallyIntegrable hh1 x).differentiableAt
    have hdh : Differentiable ℝ h := hh1.differentiable one_ne_zero
    have e : fderiv ℝ (fun x => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h) x - h x) =
        fun x => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] (fderiv ℝ h)) x - fderiv ℝ h x := by
      funext y
      have hd : HasFDerivAt (fun x => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h) x - h x)
          (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h) y - fderiv ℝ h y) y :=
        (hdy y).hasFDerivAt.sub (hdh y).hasFDerivAt
      rw [hd.fderiv, mc_fderiv_conv ρ hρc h hh1 hc]
    rw [← norm_iteratedFDeriv_fderiv, e]
    exact hδ' φ hφ x

theorem mc_mollify_gen {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (m : ℕ)
    (h : V → F) (hh : ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) h) (hc : HasCompactSupport h) (η δ₀ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ₀) :
    ∃ y : V → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y ∧ HasCompactSupport y ∧
      (∀ g, y g ≠ 0 → ∃ g', dist g g' < δ₀ ∧ h g' ≠ 0) ∧
      ∀ i ≤ m, ∀ g, ‖iteratedFDeriv ℝ i y g - iteratedFDeriv ℝ i h g‖ ≤ η := by
  have hall : ∀ m' ≤ m, ∃ δ : ℝ, 0 < δ ∧ ∀ φ : ContDiffBump (0 : V), φ.rOut < δ → ∀ i ≤ m', ∀ x,
      ‖iteratedFDeriv ℝ i (fun x =>
        (φ.normed (Measure.addHaar : Measure V) ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (Measure.addHaar : Measure V)] h) x - h x) x‖ ≤ η := by
    intro m' hm'
    induction m' with
    | zero =>
      obtain ⟨δ, hδ0, H⟩ := mc_iter 0 F h (hh.of_le (by exact_mod_cast Nat.zero_le m)) hc η hη
      refine ⟨δ, hδ0, fun φ hφ i hi x => ?_⟩
      obtain rfl : i = 0 := by omega
      exact H φ hφ x
    | succ m' ih =>
      obtain ⟨δ1, hδ1, H1⟩ := ih (by omega)
      obtain ⟨δ2, hδ2, H2⟩ := mc_iter (m' + 1) F h (hh.of_le (by exact_mod_cast hm')) hc η hη
      refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun φ hφ i hi x => ?_⟩
      rcases Nat.lt_or_ge i (m' + 1) with hlt | hge
      · exact H1 φ (lt_of_lt_of_le hφ (min_le_left _ _)) i (by omega) x
      · obtain rfl : i = m' + 1 := by omega
        exact H2 φ (lt_of_lt_of_le hφ (min_le_right _ _)) x
  obtain ⟨δ, hδ0, H⟩ := hall m le_rfl
  set d : ℝ := min δ δ₀ with hd
  have hd0 : 0 < d := lt_min hδ0 hδ
  let φ : ContDiffBump (0 : V) := ⟨d / 4, d / 2, by positivity, by linarith⟩
  have hφr : φ.rOut = d / 2 := rfl
  set ρ := φ.normed (Measure.addHaar : Measure V) with hρ
  set y := ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure V)] h with hy
  have hys : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y :=
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) φ.hasCompactSupport_normed
      φ.contDiff_normed hh.continuous.locallyIntegrable
  refine ⟨y, hys, ?_, ?_, ?_⟩
  · exact HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := Measure.addHaar)
      φ.hasCompactSupport_normed hc
  · intro g hg
    by_contra hne
    push Not at hne
    apply hg
    rw [hy, convolution_def]
    have hz : (fun t => (ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (h (g - t))) = fun _ => (0 : F) := by
      funext t
      by_cases ht : ρ t = 0
      · simp [ht]
      · have hts : t ∈ Function.support ρ := ht
        rw [hρ, φ.support_normed_eq, Metric.mem_ball, dist_zero_right] at hts
        have hdist : dist g (g - t) < δ₀ := by
          rw [dist_eq_norm, sub_sub_cancel]
          have : d / 2 < δ₀ := by
            have := min_le_right δ δ₀
            linarith
          exact lt_trans (hφr ▸ hts) this
        simp [hne _ hdist]
    rw [hz, integral_zero]
  · intro i hi g
    have hφ : φ.rOut < δ := by
      rw [hφr]
      have := min_le_left δ δ₀
      linarith
    rw [← iteratedFDeriv_sub_apply ((hys.of_le (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).contDiffAt)
      ((hh.of_le (by exact_mod_cast hi)).contDiffAt)]
    exact H φ hφ i hi g

end partC

section partC2

theorem mollify {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : ℕ)
    (h : Mat k r → E) (hh : ContDiff ℝ ((m : ℕ∞) : WithTop ℕ∞) h) (hc : HasCompactSupport h) (η δ₀ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ₀) :
    ∃ y : Mat k r → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) y ∧ HasCompactSupport y ∧
      (∀ g, y g ≠ 0 → ∃ g', dist g g' < δ₀ ∧ h g' ≠ 0) ∧
      ∀ i ≤ m, ∀ g, ‖iteratedFDeriv ℝ i y g - iteratedFDeriv ℝ i h g‖ ≤ η :=
  @mc_mollify_gen (Mat k r) _ _ _ (borel (Mat k r)) (@BorelSpace.mk (Mat k r) _ (borel (Mat k r)) rfl) E _ _ _
    m h hh hc η δ₀ hη hδ

end partC2

end Formalism.FourierDecayAlt.P.JCx4

namespace Formalism.FourierDecayAlt.P.JCx4

section partD

theorem md_glue {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ∞) (K S : Set V) (hK : IsCompact K) (x : V → E) (Q : V → Prop)
    (loc : ∀ g₀ ∈ K, ∃ U : Set V, ∃ f : V → E, IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ (n : WithTop ℕ∞) f U ∧
      (∀ g ∈ U, g ∈ S → x g = f g) ∧ ∀ g ∈ U, f g ≠ 0 → Q g) :
    ∃ X : V → E, ContDiff ℝ (n : WithTop ℕ∞) X ∧ (∀ g ∈ K, g ∈ S → X g = x g) ∧ ∀ g, X g ≠ 0 → Q g := by
  classical
  choose! U f hU hgU hf hfx hfQ using loc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun g : K => U g) (fun g => hU g g.2)
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, hgU g hg⟩)
  have hcov : K ⊆ ⋃ i : {i // i ∈ t}, U i.1.1 := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hgi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (modelWithCornersSelf ℝ V) hK.isClosed
    (fun i : {i // i ∈ t} => U i.1.1) (fun i => hU _ i.1.2) hcov
  have hρs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ρ i) := fun i => contMDiff_iff_contDiff.1 (ρ i).contMDiff
  have hsub : ∀ i g, ρ i g ≠ 0 → g ∈ U i.1.1 := fun i g h => hρ i (subset_tsupport _ h)
  refine ⟨fun g => ∑ i : {i // i ∈ t}, ρ i g • f i.1.1 g, ?_, ?_, ?_⟩
  · refine ContDiff.sum fun i _ => contDiff_iff_contDiffAt.2 fun g => ?_
    by_cases hg : g ∈ U i.1.1
    · exact (((hρs i).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt).smul
        ((hf _ i.1.2).contDiffAt ((hU _ i.1.2).mem_nhds hg))
    · have hz : (fun g => ρ i g • f i.1.1 g) =ᶠ[nhds g] fun _ => (0 : E) := by
        have h1 : g ∉ tsupport (ρ i) := fun h => hg (hρ i h)
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h1] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro g hgK hgS
    have h1 : ∀ i : {i // i ∈ t}, ρ i g • f i.1.1 g = ρ i g • x g := by
      intro i
      by_cases h0 : ρ i g = 0
      · simp [h0]
      · rw [hfx _ i.1.2 g (hsub i g h0) hgS]
    simp only [h1]
    rw [← Finset.sum_smul]
    have h2 := ρ.sum_eq_one hgK
    rw [finsum_eq_sum_of_fintype] at h2
    rw [h2, one_smul]
  · intro g hg
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    have h0 : ρ i g ≠ 0 := fun h => hi (by simp [h])
    have hf0 : f i.1.1 g ≠ 0 := fun h => hi (by simp [h])
    exact hfQ _ i.1.2 g (hsub i g h0) hf0

theorem extend {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (mm : ℕ) (x : Mat k r → E)
    (hx : CkOn (mm : ℕ∞) (GV k r) x) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) (hε : 0 < ε)
    (hsupp : ∀ g ∈ GV k r, x g ≠ 0 → ε ≤ Gf k r z z' g) (R : ℝ) (hR : 0 < R) :
    ∃ X : Mat k r → E, ContDiff ℝ ((mm : ℕ∞) : WithTop ℕ∞) X ∧ HasCompactSupport X ∧
      (∀ g ∈ GV k r, X g = Formalism.FourierDecayAlt.P.JCx2.pdPhi (R⁻¹ • g) • x g) ∧ ∀ g, X g ≠ 0 → ε / 2 < Gf k r z z' g := by
  have hGf : Continuous fun g : Mat k r => Gf k r z z' g := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z'
  set K : Set (Mat k r) := GV k r ∩ {g | Formalism.FourierDecayAlt.P.JCx2.pdSq g ≤ (2 * R) ^ 2} with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((Formalism.FourierDecayAlt.P.B2x2.closedG k r).closed.inter (isClosed_le Formalism.FourierDecayAlt.P.JCx2.pd_sq_cd.continuous continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : Mat k r)) (r := 2 * R)).subset fun M hM => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Formalism.FourierDecayAlt.P.JCx2.mn_norm_le_gN M).trans (Formalism.FourierDecayAlt.P.JCx2.pd_gN_le_of_sq (by positivity) hM.2)
  obtain ⟨Y, hY, hYx, hYQ⟩ := md_glue (V := Mat k r) (E := E) (mm : ℕ∞) K (GV k r) hKc x
    (fun g => ε / 2 < Gf k r z z' g) (by
      intro g₀ hg₀
      by_cases hlt : Gf k r z z' g₀ < ε
      · refine ⟨{g | Gf k r z z' g < ε}, fun _ => 0, isOpen_lt hGf continuous_const, hlt, contDiffOn_const,
          fun g hg hgS => ?_, fun g _ h => (h rfl).elim⟩
        by_contra hne
        exact absurd (hsupp g hgS fun h => hne (by simp [h])) (not_le.2 hg)
      · obtain ⟨U, f', hU, hgU, hf', hff⟩ := hx g₀ hg₀.1
        refine ⟨U ∩ {g | ε / 2 < Gf k r z z' g}, f', hU.inter (isOpen_lt continuous_const hGf),
          ⟨hgU, by show ε / 2 < Gf k r z z' g₀; linarith [not_lt.1 hlt]⟩, hf'.mono Set.inter_subset_left,
          fun g hg hgS => hff g hg.1 hgS, fun g hg _ => hg.2⟩)
  have hphi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Mat k r => Formalism.FourierDecayAlt.P.JCx2.pdPhi (R⁻¹ • g)) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_phi_cd.comp (contDiff_const_smul R⁻¹)
  refine ⟨fun g => Formalism.FourierDecayAlt.P.JCx2.pdPhi (R⁻¹ • g) • Y g, ?_, ?_, ?_, ?_⟩
  · exact (hphi.of_le (WithTop.coe_le_coe.2 le_top)).smul hY
  · exact (Formalism.FourierDecayAlt.P.JCx2.pd_phi_support.comp_smul (inv_ne_zero hR.ne')).smul_right
  · intro g hg
    by_cases hK : Formalism.FourierDecayAlt.P.JCx2.pdSq g ≤ (2 * R) ^ 2
    · show Formalism.FourierDecayAlt.P.JCx2.pdPhi (R⁻¹ • g) • Y g = _
      rw [hYx g ⟨hg, hK⟩ hg]
    · have h4 : 4 ≤ Formalism.FourierDecayAlt.P.JCx2.pdSq (R⁻¹ • g) := by
        rw [Formalism.FourierDecayAlt.P.JCx2.pd_sq_smul, inv_pow, le_inv_mul_iff₀ (by positivity)]
        nlinarith [not_le.1 hK]
      show Formalism.FourierDecayAlt.P.JCx2.pdPhi (R⁻¹ • g) • Y g = Formalism.FourierDecayAlt.P.JCx2.pdPhi (R⁻¹ • g) • x g
      simp [Formalism.FourierDecayAlt.P.JCx2.pdPhi, Formalism.FourierDecayAlt.P.JCx2.pd_chi_zero h4]
  · intro g hg
    exact hYQ g fun h => hg (by simp [h])

end partD

end Formalism.FourierDecayAlt.P.JCx4

namespace Formalism.FourierDecayAlt.P.JCx4

section partE

open Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.BetaSesquilinearity

theorem me_approx_one {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (mm m0 : ℕ) (hm0 : m0 ≤ mm) (A' : ℝ) (hA' : 0 ≤ A') (F : Mat k r → E) (hF : CkOn (mm : ℕ∞) (GV k r) F)
    (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) (hε : 0 < ε) (hsupp : ∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g)
    (R τ : ℝ) (hR : 0 < R) (hτ : 0 < τ) :
    ∃ y : Mat k r → E, CkOn (⊤ : ℕ∞) (GV k r) y ∧ (∀ (A'' : ℝ) (m' : ℕ), InCC A'' m' y) ∧
      (∀ g ∈ GV k r, y g ≠ 0 → ε / 4 ≤ Gf k r z z' g) ∧
      CCle A' m0 (fun g => pdPhi (R⁻¹ • g) • F g - y g) τ := by
  haveI : ProperSpace (Mat k r) := FiniteDimensional.proper_real _
  obtain ⟨X, hXc, hXs, hXe, hXQ⟩ := extend mm F hF z z' ε hε hsupp R hR
  obtain ⟨Cb, hCb0, hCb⟩ := dlr_bound (k := k) (r := r) (E := E) m0
  obtain ⟨ρX, hρX⟩ : ∃ ρX : ℝ, ∀ g, X g ≠ 0 → ‖g‖ ≤ ρX := by
    obtain ⟨ρ, hρ⟩ := hXs.isCompact.isBounded.subset_closedBall (0 : Mat k r)
    exact ⟨ρ, fun g hg => by simpa using hρ (subset_tsupport _ hg)⟩
  have hBc : IsCompact (Metric.closedBall (0 : Mat k r) (ρX + 1)) := isCompact_closedBall _ _
  have hGf : Continuous fun g : Mat k r => Gf k r z z' g := Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z'
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuousOn_iff.1
    (hBc.uniformContinuousOn_of_continuous hGf.continuousOn) (ε / 4) (by positivity)
  have hgN : Continuous fun g : Mat k r => gN g := by unfold gN; fun_prop
  have hWc : Continuous fun g : Mat k r => gN g ^ A' * (1 + ‖g‖) ^ m0 :=
    ((Real.continuous_rpow_const hA').comp hgN).mul (by fun_prop)
  obtain ⟨W₀, hW₀⟩ := hBc.exists_bound_of_continuousOn hWc.continuousOn
  set W : ℝ := max W₀ 0 with hWdef
  have hW : 0 ≤ W := le_max_right _ _
  have hden : 0 < Cb * W * (m0 + 1) + 1 := by
    have : 0 ≤ Cb * W * ((m0 : ℝ) + 1) := mul_nonneg (mul_nonneg hCb0 hW) (by positivity)
    linarith
  set η : ℝ := τ / (Cb * W * (m0 + 1) + 1) with hηdef
  have hη : 0 < η := div_pos hτ hden
  have hCbη : Cb * W * (m0 + 1) * η ≤ τ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ hden]
    nlinarith
  have hm0' : ((m0 : ℕ∞) : WithTop ℕ∞) ≤ ((mm : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (by exact_mod_cast hm0)
  have htop : ∀ n : ℕ, ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun n => WithTop.coe_le_coe.2 le_top
  obtain ⟨y, hys, hyc, hysupp, hyd⟩ := mollify m0 X (hXc.of_le hm0') hXs η (min 1 δ₁) hη (lt_min one_pos hδ₁)
  have hyB : ∀ g, y g ≠ 0 → ‖g‖ < ρX + 1 := by
    intro g hg
    obtain ⟨g', hd, hX'⟩ := hysupp g hg
    have h1 := hρX g' hX'
    have h2 : ‖g‖ ≤ ‖g'‖ + ‖g - g'‖ := by
      have := norm_add_le g' (g - g')
      simpa using this
    rw [dist_eq_norm] at hd
    have h3 : ‖g - g'‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    linarith
  refine ⟨y, fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩, ?_, ?_, ?_⟩
  · intro A'' m'
    refine Formalism.FourierDecayAlt.P.compact_support_finite_class k r E y (Metric.closedBall 0 (ρX + 1))
      (fun g₀ _ => ⟨Set.univ, y, isOpen_univ, trivial, hys.contDiffOn, fun _ _ _ => rfl⟩) hBc (fun g hg => ?_) A'' m'
    by_contra h
    exact hg (mem_closedBall_zero_iff.2 (le_of_lt (hyB g h)))
  · intro g _ hy0
    obtain ⟨g', hd, hX'⟩ := hysupp g hy0
    have h1 := hXQ g' hX'
    have hg'B : g' ∈ Metric.closedBall (0 : Mat k r) (ρX + 1) :=
      mem_closedBall_zero_iff.2 (by linarith [hρX g' hX'])
    have hgB : g ∈ Metric.closedBall (0 : Mat k r) (ρX + 1) := mem_closedBall_zero_iff.2 (le_of_lt (hyB g hy0))
    have h2 := hδ₁' g hgB g' hg'B (lt_of_lt_of_le hd (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h2
    linarith [h2.2]
  · have hXY : CCle A' m0 (fun g => X g - y g) τ := by
      have hcd : ContDiff ℝ ((m0 : ℕ∞) : WithTop ℕ∞) (fun g => X g - y g) := (hXc.of_le hm0').sub (hys.of_le (htop m0))
      refine ⟨fun g₀ _ => ⟨Set.univ, fun g => X g - y g, isOpen_univ, trivial, hcd.contDiffOn, fun _ _ _ => rfl⟩, ?_⟩
      intro u v hu hv hl g _
      have hb := hCb (fun g => X g - y g) hcd u v hu hv hl g
      have hgN0 : 0 ≤ gN g ^ A' := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      by_cases hgB : ‖g‖ ≤ ρX + 1
      · have hi : ∀ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ η := by
          intro i hi
          have hi' : i ≤ m0 := by simpa [Nat.lt_succ_iff] using hi
          have e1 : iteratedFDeriv ℝ i (fun g => X g - y g) g = iteratedFDeriv ℝ i X g - iteratedFDeriv ℝ i y g :=
            iteratedFDeriv_sub_apply ((hXc.of_le (le_trans (WithTop.coe_le_coe.2 (by exact_mod_cast hi')) hm0')).contDiffAt)
              ((hys.of_le (htop i)).contDiffAt)
          rw [e1, norm_sub_rev]
          exact hyd i hi' g
        have hsum : ∑ i ∈ Finset.range (m0 + 1), ‖iteratedFDeriv ℝ i (fun g => X g - y g) g‖ ≤ (m0 + 1) * η := by
          have := Finset.sum_le_card_nsmul _ _ _ hi
          simpa [Finset.card_range, nsmul_eq_mul] using this
        have hWg : gN g ^ A' * (1 + ‖g‖) ^ m0 ≤ W := by
          have := hW₀ g (mem_closedBall_zero_iff.2 hgB)
          exact le_trans (le_abs_self _) (le_trans (by simpa [Real.norm_eq_abs] using this) (le_max_left _ _))
        have h1p : 0 ≤ (1 + ‖g‖) ^ m0 := by positivity
        calc gN g ^ A' * ‖dLR u v (fun g => X g - y g) g‖
            ≤ gN g ^ A' * (Cb * (1 + ‖g‖) ^ m0 * ((m0 + 1) * η)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hCb0 h1p))) hgN0
          _ = Cb * (gN g ^ A' * (1 + ‖g‖) ^ m0) * (m0 + 1) * η := by ring
          _ ≤ Cb * W * (m0 + 1) * η := by
              have : 0 ≤ ((m0 : ℝ) + 1) * η := by positivity
              nlinarith [mul_le_mul_of_nonneg_left hWg hCb0]
          _ ≤ τ := hCbη
      · have hev : (fun g => X g - y g) =ᶠ[nhds g] fun _ => (0 : E) := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds (not_le.1 hgB)] with g' hg'
          have hX0 : X g' = 0 := by
            by_contra h
            have := hρX g' h
            have hg'' : ρX + 1 < ‖g'‖ := hg'
            linarith
          have hy0 : y g' = 0 := by
            by_contra h
            have := hyB g' h
            have hg'' : ρX + 1 < ‖g'‖ := hg'
            linarith
          simp [hX0, hy0]
        have hz : ∀ i, iteratedFDeriv ℝ i (fun g => X g - y g) g = 0 := by
          intro i
          rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds]
          simp
        simp only [hz, norm_zero, Finset.sum_const_zero, mul_zero] at hb
        have : ‖dLR u v (fun g => X g - y g) g‖ = 0 := le_antisymm hb (norm_nonneg _)
        rw [this, mul_zero]
        exact hτ.le
    exact Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => by simp only [hXe g hg]) hXY

end partE

end Formalism.FourierDecayAlt.P.JCx4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.JCx2 Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JCx4

theorem level_form_sesquilinear_moderate : Formalism.FourierDecayAlt.JC.FormLevSesqMM := by
  unfold Formalism.FourierDecayAlt.JC.FormLevSesqMM
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε _ hA hmm x x' y c hx hx' hy
  exact formLev_sesq_core P0 T s j w A mm hA hmm x x' y c (fun a => (hx a).2.1) (fun a => (hx' a).2.1)
    (fun a => (hy a).2.1)

theorem positive_density_moderate_growth : Formalism.FourierDecayAlt.JC.PosDensityMM := by
  intro Wp Wq _ _ _ _ _ _ P0 T s j w A mm ε hε hA hmm H x hx
  have hm0 : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm := pd_thr_mm P0 j w.length mm hmm
  have hAB := pd_thr_AB P0 j w.length A hA
  have hN0 : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have hAB0 : 0 < AB P0.k (P0.r - (j : ℕ)) := by unfold AB; positivity
  have hA1 : 0 ≤ A - 1 := by linarith

  choose cx hcx using fun a => (hx a).2.1
  have hcx0 : ∀ a, 0 ≤ cx a := fun a => pd_ccle_nonneg (hcx a)
  set c0 : ℝ := ∑ a, cx a with hc0def
  have hc0 : 0 ≤ c0 := Finset.sum_nonneg fun a _ => hcx0 a
  have hX : ∀ a, CCle A mm (x a) c0 := fun a => pd_ccle_mono_c (hcx a)
    (Finset.single_le_sum (f := cx) (fun b _ => hcx0 b) (Finset.mem_univ a))
  obtain ⟨Cf, hCf0, hCf⟩ := formLev_bound_mm P0 T s j w A hA
  obtain ⟨Kc, hKc0, hKc⟩ := pd_cut_ccle (k := P0.k) (r := P0.r - j) (E := Wq →L[ℂ] Wp) mm
  refine pd_nonneg_of_approx _ (Cf * (2 * c0 + 1)) fun R hR1 => ?_
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  set τ : ℝ := 1 / R with hτdef
  have hτ : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτdef, div_le_one hR0]; exact hR1
  set R' : ℝ := max 1 (2 * Kc * c0 / τ) with hR'def
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hcut : Kc * c0 / R' ≤ τ / 2 := by
    rw [div_le_iff₀ hR']
    have h1 : 2 * Kc * c0 / τ ≤ R' := le_max_right _ _
    rw [div_le_iff₀ hτ] at h1
    nlinarith
  have happ := fun a => me_approx_one mm _ hm0 (A - 1) hA1 (x a) (hx a).1 (T.bs j).z (T.bs j).z' ε hε (hx a).2.2
    R' (τ / 2) hR' (by positivity)
  choose y hyck hyin hysupp hycc using happ
  have hpos := H (ε / 4) (by positivity) y fun a => ⟨hyck a, hyin a, hysupp a⟩
  set e : Wd.Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := x - y with hedef
  have he : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (e a) τ := by
    intro a
    have h1 := pd_ccle_mono le_rfl hm0 (hKc R' hR' A (x a) c0 (hX a))
    have h2 := CCle_add h1 (hycc a)
    have e2 : (fun g => pdPsi R' g • x a g + (pdPhi (R'⁻¹ • g) • x a g - y a g)) = e a := by
      funext g
      simp only [hedef, Pi.sub_apply, pdPsi, sub_smul, one_smul]
      abel
    rw [e2] at h2
    exact pd_ccle_mono_c h2 (by linarith)
  have hx1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x a) c0 :=
    fun a => pd_ccle_mono (by linarith) hm0 (hX a)
  have hy1 : ∀ a, CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (y a) (c0 + τ) := by
    intro a
    have h := CCle_add (hx1 a) (CCle_smul (-1) (he a))
    have e3 : (fun g => x a g + (-1 : ℂ) • e a g) = y a := by
      funext g
      simp only [hedef, Pi.sub_apply, neg_smul, one_smul]
      abel
    rw [e3] at h
    simpa using h
  have hv : ∀ {F : Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} {c : ℝ},
      CCle (A - 1) (5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) F c →
      CCle (A - 1 - 2 * (w.length : ℝ)) 5 F c := fun h => pd_ccle_mono (by linarith) (by omega) h

  have hxI : ∀ a, InCC A mm (x a) := fun a => (hx a).2.1
  have hyI : ∀ a, InCC A mm (y a) := fun a => hyin a A mm
  have heI : ∀ a, InCC A mm (e a) := by
    intro a
    obtain ⟨c1, h1⟩ := hxI a
    obtain ⟨c2, h2⟩ := hyI a
    have h := CCle_add h1 (CCle_smul (-1) h2)
    have e4 : (fun g => x a g + (-1 : ℂ) • y a g) = e a := by
      funext g
      simp only [hedef, Pi.sub_apply, neg_smul, one_smul]
      abel
    rw [e4] at h
    exact ⟨_, h⟩
  have hsplit : y + (1 : ℂ) • e = x := by
    funext a g
    simp only [hedef, Pi.add_apply, Pi.sub_apply, one_smul]
    abel
  have hS1 := (formLev_sesq_core P0 T s j w A mm hA hmm y e x 1 hyI heI hxI).1
  have hS2 := (formLev_sesq_core P0 T s j w A mm hA hmm y e y 1 hyI heI hyI).2
  rw [hsplit] at hS1 hS2
  refine ⟨D.formLev T s j w y y, hpos, ?_⟩
  have hb1 := hCf y e (c0 + τ) τ hy1 fun a => hv (he a)
  have hb2 := hCf e x τ c0 he fun a => hv (hx1 a)
  rw [hS1, hS2, map_one, one_mul, one_mul]
  have e5 : D.formLev T s j w y y + D.formLev T s j w y e + D.formLev T s j w e x - D.formLev T s j w y y =
      D.formLev T s j w y e + D.formLev T s j w e x := by ring
  rw [e5]
  calc ‖D.formLev T s j w y e + D.formLev T s j w e x‖
      ≤ ‖D.formLev T s j w y e‖ + ‖D.formLev T s j w e x‖ := norm_add_le _ _
    _ ≤ Cf * (c0 + τ) * τ + Cf * τ * c0 := add_le_add hb1 hb2
    _ ≤ Cf * (2 * c0 + 1) * τ := by nlinarith [mul_nonneg hCf0 hτ.le]
    _ = Cf * (2 * c0 + 1) / R := by rw [hτdef]; ring

end Formalism.FourierDecayAlt.P
