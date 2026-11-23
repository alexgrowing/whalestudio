import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThetaFacCompl

open scoped ComplexConjugate

section Abstract

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (Z : Submodule ℂ M) (q : M → M → ℂ)

theorem q_zero_left (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c) {c : M} (hc : c ∈ Z) :
    q 0 c = 0 := by
  have := hsmul 0 Z.zero_mem c hc 0
  simpa using this

theorem q_add_right (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) {a b c : M} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) :
    q c (a + b) = q c a + q c b := by
  rw [hherm _ (Z.add_mem ha hb) _ hc, hadd a ha b hb c hc, map_add, ← hherm a ha c hc, ← hherm b hb c hc]

theorem q_smul_right (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) {a c : M} (ha : a ∈ Z) (hc : c ∈ Z) (t : ℂ) :
    q c (t • a) = conj t * q c a := by
  rw [hherm _ (Z.smul_mem t ha) _ hc, hsmul a ha c hc t, map_mul, ← hherm a ha c hc]

theorem q_sub_right (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) {a b c : M} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) :
    q c (a - b) = q c a - q c b := by
  have e : a - b = a + (-1 : ℂ) • b := by simp [sub_eq_add_neg]
  rw [e, q_add_right Z q hadd hherm ha (Z.smul_mem _ hb) hc, q_smul_right Z q hsmul hherm hb hc]
  simp [sub_eq_add_neg]

theorem q_span_left (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c) {S : Set M} (hS : S ⊆ Z) {r : M} (hr : r ∈ Z)
    (h : ∀ u ∈ S, q u r = 0) : ∀ n ∈ Submodule.span ℂ S, q n r = 0 := by
  have hle : Submodule.span ℂ S ≤ Z := Submodule.span_le.2 hS
  intro n hn
  induction hn using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact q_zero_left Z q hsmul hr
  | add x y hx hy ihx ihy => rw [hadd x (hle hx) y (hle hy) r hr, ihx, ihy, add_zero]
  | smul t x hx ihx => rw [hsmul x (hle hx) r hr t, ihx, mul_zero]

theorem exists_orth (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) (hpos : ∀ a ∈ Z, q a a = 0 → a = 0) :
    ∀ S : Finset M, (↑S : Set M) ⊆ Z → ∀ x ∈ Z, ∃ n ∈ Submodule.span ℂ (S : Set M), ∀ u ∈ S, q u (x - n) = 0 := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ x _; exact ⟨0, Submodule.zero_mem _, by simp⟩
  | insert a s ha ih =>
    intro hS x hx
    have haZ : a ∈ Z := hS (by simp)
    have hsZ : (↑s : Set M) ⊆ Z := fun y hy => hS (by simp [hy])
    have hspZ : Submodule.span ℂ (↑s : Set M) ≤ Z := Submodule.span_le.2 hsZ
    obtain ⟨n1, hn1, h1⟩ := ih hsZ x hx
    obtain ⟨n2, hn2, h2⟩ := ih hsZ a haZ
    have hrZ : x - n1 ∈ Z := Z.sub_mem hx (hspZ hn1)
    have hsZ' : a - n2 ∈ Z := Z.sub_mem haZ (hspZ hn2)
    have hspan_le : Submodule.span ℂ (↑s : Set M) ≤ Submodule.span ℂ (↑(insert a s) : Set M) :=
      Submodule.span_mono (by simp [Finset.coe_insert])
    have ha_mem : a ∈ Submodule.span ℂ (↑(insert a s) : Set M) := Submodule.subset_span (by simp)
    by_cases hss : q (a - n2) (a - n2) = 0
    · have han2 : a = n2 := sub_eq_zero.1 (hpos _ hsZ' hss)
      refine ⟨n1, hspan_le hn1, fun u hu => ?_⟩
      rcases Finset.mem_insert.1 hu with rfl | hu
      · rw [han2]; exact q_span_left Z q hadd hsmul hsZ hrZ h1 n2 hn2
      · exact h1 u hu
    · set t : ℂ := conj (q (a - n2) (x - n1) / q (a - n2) (a - n2)) with ht
      have hct : conj t = q (a - n2) (x - n1) / q (a - n2) (a - n2) := by rw [ht, Complex.conj_conj]
      have hts : t • (a - n2) ∈ Z := Z.smul_mem t hsZ'
      have hx' : x - (n1 + t • (a - n2)) = (x - n1) - t • (a - n2) := by abel
      have horth : ∀ u ∈ Z, q u (x - n1) = 0 → q u (a - n2) = 0 → q u ((x - n1) - t • (a - n2)) = 0 := by
        intro u hu e1 e2
        rw [q_sub_right Z q hadd hsmul hherm hrZ hts hu, q_smul_right Z q hsmul hherm hsZ' hu, e1, e2]; simp
      have hs : ∀ u ∈ s, q u ((x - n1) - t • (a - n2)) = 0 := fun u hu => horth u (hsZ hu) (h1 u hu) (h2 u hu)
      refine ⟨n1 + t • (a - n2), add_mem (hspan_le hn1) (Submodule.smul_mem _ _ (sub_mem ha_mem (hspan_le hn2))),
        fun u hu => ?_⟩
      rw [hx']
      rcases Finset.mem_insert.1 hu with rfl | hu
      · have hself : q (u - n2) ((x - n1) - t • (u - n2)) = 0 := by
          rw [q_sub_right Z q hadd hsmul hherm hrZ hts hsZ', q_smul_right Z q hsmul hherm hsZ' hsZ', hct]
          field_simp; ring
        have hn2o : q n2 ((x - n1) - t • (u - n2)) = 0 :=
          q_span_left Z q hadd hsmul hsZ (Z.sub_mem hrZ hts) hs n2 hn2
        have e := hadd _ hsZ' _ (hspZ hn2) _ (Z.sub_mem hrZ hts)
        rw [sub_add_cancel] at e
        rw [e, hself, hn2o, add_zero]
      · exact hs u hu

theorem exists_of_mem_span_image {N : Type*} [AddCommGroup N] [Module ℂ N] (D A : Submodule ℂ M) (T : M → N)
    (hT : ∀ x ∈ D, ∀ y ∈ D, ∀ c : ℂ, T (x + c • y) = T x + c • T y) (hA : A ≤ D) {f : N}
    (hf : f ∈ Submodule.span ℂ (T '' (A : Set M))) : ∃ w ∈ A, T w = f := by
  have h0 : T 0 = 0 := by
    have := hT 0 D.zero_mem 0 D.zero_mem 1
    simpa using this
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨w, hw, rfl⟩ := hx; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, A.zero_mem, h0⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨w1, hw1, rfl⟩ := ihx
    obtain ⟨w2, hw2, rfl⟩ := ihy
    exact ⟨w1 + w2, A.add_mem hw1 hw2, by simpa using hT w1 (hA hw1) w2 (hA hw2) 1⟩
  | smul c x _ ihx =>
    obtain ⟨w, hw, rfl⟩ := ihx
    exact ⟨c • w, A.smul_mem c hw, by simpa [h0] using hT 0 D.zero_mem w (hA hw) c⟩

end Abstract

end GlobalTheory.ThetaFacCompl

namespace GlobalTheory.ThetaFacCompl

open scoped ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_transl (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (h x : UA σ W.J) :
    M.I om (om (1, h) Φ) x = M.I om Φ (x * h) := by
  unfold Model.I theta
  congr 1
  funext g
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem mat_inv_mul (g : UA σ W.J) : mat g⁻¹ * mat g = 1 := by
  simp [mat]

theorem mat_mul_inv (g : UA σ W.J) : mat g * mat g⁻¹ = 1 := by
  simp [mat]

theorem inv_mem_UAt {R : Type} [Zero R] (ev : AF F → R) {h : UA σ W.J} (hh : h ∈ UAt σ W ev) :
    h⁻¹ ∈ UAt σ W ev := by
  intro u hu
  have e : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by
    rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hh u hu, Matrix.mul_zero, neg_zero]

theorem inv_mem_KInf (τ : ∀ w : InfinitePlace F, EmbOver E w) {k : UA σ W.J} (hk : k ∈ KInf σ W τ) :
    k⁻¹ ∈ KInf σ W τ := by
  refine ⟨inv_mem_UAt _ hk.1, fun w => ?_⟩
  set A := (mat k).map (piInf (τ w))
  set A' := (mat k⁻¹).map (piInf (τ w))
  have h1 : A' * A = 1 := by
    simp only [A, A', ← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : A * A' = 1 := by
    simp only [A, A', ← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : A * W.θ w = W.θ w * A := hk.2 w
  show A' * W.θ w = W.θ w * A'
  calc A' * W.θ w = A' * W.θ w * (A * A') := by rw [h2, Matrix.mul_one]
    _ = A' * (A * W.θ w) * A' := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = (A' * A) * W.θ w * A' := by simp only [Matrix.mul_assoc]
    _ = W.θ w * A' := by rw [h1, Matrix.one_mul]

theorem mul_conj_polar (z w : ℂ) :
    z * conj w = ((‖z + w‖ ^ 2 : ℝ) - (‖z + (-1 : ℂ) * w‖ ^ 2 : ℝ) + Complex.I * (‖z + Complex.I * w‖ ^ 2 : ℝ)
      - Complex.I * (‖z + (-Complex.I) * w‖ ^ 2 : ℝ)) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;> simp <;> ring

end GlobalTheory.ThetaFacCompl

end
