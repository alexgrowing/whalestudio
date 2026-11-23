import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.Reduction

open NumberField IsDedekindDomain Set Matrix
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem siegel_le_pow_mul {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) :
    ∀ (k : ℕ) (m l : Fin n), (l : ℕ) = m + k → ρ l ≤ (max 1 t⁻¹) ^ k * ρ m
  | 0, m, l, h => by
    have : l = m := Fin.ext (by simpa using h)
    simp [this]
  | k + 1, m, l, h => by
    have hp : (m : ℕ) + k < n := by omega
    set p : Fin n := ⟨m + k, hp⟩
    have h1 : ρ l ≤ max 1 t⁻¹ * ρ p := by
      have := hs p l (by simp only [p]; omega)
      calc ρ l = t⁻¹ * (t * ρ l) := by field_simp
        _ ≤ t⁻¹ * ρ p := mul_le_mul_of_nonneg_left this (inv_nonneg.2 ht.le)
        _ ≤ max 1 t⁻¹ * ρ p := mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ p).le
    have h2 := siegel_le_pow_mul ht hρ hs k m p rfl
    calc ρ l ≤ max 1 t⁻¹ * ρ p := h1
      _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ k * ρ m) :=
          mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one (le_max_left _ _))
      _ = (max 1 t⁻¹) ^ (k + 1) * ρ m := by ring

theorem siegel_div_le_mul {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {R : ℝ} (hR1 : 1 ≤ R)
    (hR : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) (l m : Fin n) :
    ρ l / ρ m ≤ (max 1 t⁻¹) ^ n * R := by
  have hc : 1 ≤ (max 1 t⁻¹) ^ n := one_le_pow₀ (le_max_left _ _)
  rcases lt_trichotomy l m with h | h | h
  · calc ρ l / ρ m ≤ R := hR l m h
      _ ≤ (max 1 t⁻¹) ^ n * R := le_mul_of_one_le_left (by linarith) hc
  · subst h
    rw [div_self (hρ l).ne']
    nlinarith
  · have hlm : (m : ℕ) < l := h
    have := siegel_le_pow_mul ht hρ hs ((l : ℕ) - m) m l (by omega)
    rw [div_le_iff₀ (hρ m)]
    calc ρ l ≤ (max 1 t⁻¹) ^ ((l : ℕ) - m) * ρ m := this
      _ ≤ (max 1 t⁻¹) ^ n * ρ m := by
          have := l.isLt
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (le_max_left _ _) (by omega))
            (hρ m).le
      _ ≤ (max 1 t⁻¹) ^ n * R * ρ m :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hR1) (hρ m).le

theorem exists_norm_infAt_entry_le {S : Set (AdelicGLn.AdelicGL K n)} (hS : IsCompact S) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ g ∈ S, ∀ w : InfinitePlace K, ∀ i j : Fin n,
      ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β := by
  have hc : Continuous fun g : AdelicGLn.AdelicGL K n =>
      ∑ w : InfinitePlace K, ∑ i : Fin n, ∑ j : Fin n,
        ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j‖ := by
    refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => ?_
    exact (((continuous_apply j).comp (continuous_apply i)).comp
      (Units.continuous_val.comp (continuous_infAt w))).norm
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun g hg w i j => ?_⟩
  have h1 := hC g hg
  rw [Real.norm_of_nonneg (by positivity)] at h1
  refine le_trans ?_ (h1.trans (le_max_left _ _))
  calc ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j‖
      ≤ ∑ j' : Fin n, ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i j'‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin n, ∑ j' : Fin n, ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin n,
          ‖(infAt w g : Matrix (Fin n) (Fin n) w.Completion) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ w' : InfinitePlace K, ∑ i' : Fin n, ∑ j' : Fin n,
          ‖(infAt w' g : Matrix (Fin n) (Fin n) w'.Completion) i' j'‖ :=
        Finset.single_le_sum (f := fun w' : InfinitePlace K => ∑ i' : Fin n, ∑ j' : Fin n,
          ‖(infAt w' g : Matrix (Fin n) (Fin n) w'.Completion) i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (Finset.mem_univ w)

theorem norm_infAt_conj_le (w : InfinitePlace K) (b q : AdelicGLn.AdelicGL K n) (ρ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) {β₁ β₂ β₃ L : ℝ}
    (h1 : ∀ i j, ‖(infAt w b : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β₁)
    (h2 : ∀ i j, ‖(infAt w q : Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β₂)
    (h3 : ∀ i j, ‖(((infAt w b)⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion)
      i j‖ ≤ β₃)
    (hL : ∀ l m, ρ l / ρ m ≤ L) (hβ₁ : 0 ≤ β₁) (i j : Fin n) :
    ‖(infAt w (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * q *
      (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b⁻¹) :
        Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ (n : ℝ) ^ 2 * (β₁ * (L * β₂) * β₃) := by
  set d : Fin n → w.Completion := fun l =>
    ((GroundTheory.Global.posRealToUnits w ⟨ρ l ^ w.mult, pow_pos (hρ l) _⟩ : (w.Completion)ˣ) :
      w.Completion) with hd_def
  set d' : Fin n → w.Completion := fun l =>
    (((GroundTheory.Global.posRealToUnits w ⟨ρ l ^ w.mult, pow_pos (hρ l) _⟩)⁻¹ : (w.Completion)ˣ) :
      w.Completion) with hd'_def
  have hd : ∀ l, ‖d l‖ = ρ l := fun l => norm_posRealToUnits w (hρ l)
  have hd' : ∀ l, ‖d' l‖ = (ρ l)⁻¹ := fun l => by
    simp only [d', Units.val_inv_eq_inv_val, norm_inv]
    rw [norm_posRealToUnits w (hρ l)]
  set B := (infAt w b : Matrix (Fin n) (Fin n) w.Completion)
  set B' := (((infAt w b)⁻¹ : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion)
  set Qm := (infAt w q : Matrix (Fin n) (Fin n) w.Completion)
  have hmat : (infAt w (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * q *
      (diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)))⁻¹ * b⁻¹) :
        Matrix (Fin n) (Fin n) w.Completion) = B * (diagonal d * Qm * diagonal d') * B' := by
    rw [infAt_mul, infAt_mul, infAt_mul, infAt_mul, infAt_inv w (diagUnits n _), infAt_inv w b,
      infAt_diagUnits_posIdele, ← map_inv (diagUnits n)]
    simp only [Units.val_mul, coe_diagUnits, Pi.inv_apply, mul_assoc]
    rfl
  have hE : ∀ l m, (diagonal d * Qm * diagonal d') l m = d l * Qm l m * d' m := by
    intro l m
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hEn : ∀ l m, ‖(diagonal d * Qm * diagonal d') l m‖ ≤ L * β₂ := by
    intro l m
    rw [hE, norm_mul, norm_mul, hd, hd']
    calc ρ l * ‖Qm l m‖ * (ρ m)⁻¹ = ρ l / ρ m * ‖Qm l m‖ := by ring
      _ ≤ L * β₂ := mul_le_mul (hL l m) (h2 l m) (norm_nonneg _)
          ((div_pos (hρ l) (hρ m)).le.trans (hL l m))
  rw [hmat, Matrix.mul_apply]
  calc ‖∑ m, (B * (diagonal d * Qm * diagonal d')) i m * B' m j‖
      ≤ ∑ m : Fin n, ∑ l : Fin n, β₁ * (L * β₂) * β₃ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul, Matrix.mul_apply]
        have hterm : ∀ l, ‖B i l * (diagonal d * Qm * diagonal d') l m‖ ≤ β₁ * (L * β₂) := by
          intro l
          rw [norm_mul]
          exact mul_le_mul (h1 i l) (hEn l m) (norm_nonneg _) hβ₁
        have hnn : ∀ l, 0 ≤ β₁ * (L * β₂) := fun l => (norm_nonneg _).trans (hterm l)
        calc ‖∑ l, B i l * (diagonal d * Qm * diagonal d') l m‖ * ‖B' m j‖
            ≤ (∑ l : Fin n, β₁ * (L * β₂)) * β₃ :=
              mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm l)) (h3 m j)
                (norm_nonneg _) (Finset.sum_nonneg fun l _ => hnn l)
          _ = ∑ l : Fin n, β₁ * (L * β₂) * β₃ := Finset.sum_mul _ _ _
    _ = (n : ℝ) ^ 2 * (β₁ * (L * β₂) * β₃) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem exists_encard_le_siegel {ω : Set (AdelicGLn.AdelicGL K n)} (hω : IsCompact ω) {t : ℝ}
    (ht : 0 < t) {Q : Set (normOneGL K n)} (hQ : IsCompact Q) :
    ∃ (C : ℝ) (N : ℕ), ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
      (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
      ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL K n,
      (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * k →
      ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
      ∃ m : ℕ, (m : ℝ) ≤ C * R ^ N ∧ ∀ z : normOneGL K n,
        {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}.encard ≤ m := by
  classical
  set Q' : Set (AdelicGLn.AdelicGL K n) :=
    (fun p : AdelicGLn.AdelicGL K n × normOneGL K n × normOneGL K n =>
      p.1 * (p.2.1 : AdelicGLn.AdelicGL K n) * (p.2.2 : AdelicGLn.AdelicGL K n)⁻¹ * p.1⁻¹) ''
      (((maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)) ×ˢ
        (Q ×ˢ Q)) with hQ'_def
  have hQ' : IsCompact Q' := by
    refine (isCompact_maxCompact.prod (hQ.prod hQ)).image ?_
    exact (((continuous_fst.mul (continuous_subtype_val.comp (continuous_fst.comp
      continuous_snd))).mul (continuous_subtype_val.comp (continuous_snd.comp
        continuous_snd)).inv).mul continuous_fst.inv)
  set 𝒦 : Set (FiniteAdeleRing (𝓞 K) K) := ⋃ i : Fin n, ⋃ j : Fin n,
    (fun p : AdelicGLn.AdelicGL K n × AdelicGLn.AdelicGL K n =>
      ((AdelicGLn.prodEquiv K n (p.1 * p.2 * p.1⁻¹)).2 :
        Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j) '' (ω ×ˢ Q') with h𝒦_def
  have h𝒦 : IsCompact 𝒦 := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => (hω.prod hQ').image ?_
    exact ((continuous_apply j).comp (continuous_apply i)).comp (Units.continuous_val.comp
      (continuous_snd.comp ((AdelicGLn.prodEquiv K n).continuous.comp
        ((continuous_fst.mul continuous_snd).mul continuous_fst.inv))))
  obtain ⟨C₀, N, hC₀⟩ := exists_ncard_ratGLBox_le n h𝒦
  obtain ⟨β₁, hβ₁0, hβ₁⟩ := exists_norm_infAt_entry_le hω
  obtain ⟨β₂, hβ₂0, hβ₂⟩ := exists_norm_infAt_entry_le hQ'
  obtain ⟨β₃, hβ₃0, hβ₃⟩ := exists_norm_infAt_entry_le (hω.image continuous_inv)
  set c := (max 1 t⁻¹) ^ n
  have hc0 : 0 ≤ c := by positivity
  set A := (n : ℝ) ^ 2 * (β₁ * (c * β₂) * β₃)
  have hA : 0 ≤ A := by positivity
  refine ⟨max C₀ 0 * (1 + A) ^ N, N, ?_⟩
  intro b hb ρ hρ hs k hk x hx R hR1 hR
  set a := diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) with ha_def
  set Y : Set (GL (Fin n) K) :=
    {γ | ∃ q ∈ Q', AdelicGLn.diagonal K n γ = b * a * q * a⁻¹ * b⁻¹} with hY_def
  have hT : 0 ≤ A * R := mul_nonneg hA (by linarith)
  have hYbox : Y ⊆ ratGLBox n 𝒦 (A * R) := by
    rintro γ ⟨q, hq, hγ⟩ i j
    refine ⟨?_, fun w => ?_⟩
    · have e1 : algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) =
          (((b * a * q * a⁻¹ * b⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j).2 := by
        rw [← hγ, AdelicGLn.diagonal_apply]
        rfl
      have e2 : (((b * a * q * a⁻¹ * b⁻¹ : AdelicGLn.AdelicGL K n) :
          Matrix (Fin n) (Fin n) 𝔸[K]) i j).2 =
          ((AdelicGLn.prodEquiv K n (b * q * b⁻¹)).2 :
            Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) i j := by
        rw [← AdelicGLn.prodEquiv_apply_snd]
        simp only [map_mul, map_inv, Prod.snd_mul, Prod.snd_inv, ha_def,
          prodEquiv_diagUnits_posIdele_snd, mul_one, inv_one]
      rw [e1, e2]
      exact mem_iUnion₂.2 ⟨i, j, (b, q), ⟨hb, hq⟩, rfl⟩
    · have e1 : w ((γ : Matrix (Fin n) (Fin n) K) i j) =
          ‖(infAt w (b * a * q * a⁻¹ * b⁻¹) : Matrix (Fin n) (Fin n) w.Completion) i j‖ := by
        rw [infAt_apply, ← hγ, AdelicGLn.diagonal_apply, ← GroundTheory.Global.norm_algebraMap_apply]
        rfl
      rw [e1]
      have hL : ∀ l m, ρ l / ρ m ≤ c * R := siegel_div_le_mul ht hρ hs hR1 hR
      have h3 : ∀ i j, ‖(((infAt w b)⁻¹ : GL (Fin n) w.Completion) :
          Matrix (Fin n) (Fin n) w.Completion) i j‖ ≤ β₃ := fun i j => by
        rw [← infAt_inv]
        exact hβ₃ _ ⟨b, hb, rfl⟩ w i j
      calc ‖(infAt w (b * a * q * a⁻¹ * b⁻¹) : Matrix (Fin n) (Fin n) w.Completion) i j‖
          ≤ (n : ℝ) ^ 2 * (β₁ * (c * R * β₂) * β₃) :=
            norm_infAt_conj_le w b q ρ hρ (hβ₁ b hb w) (hβ₂ q hq w) h3 hL hβ₁0 i j
        _ = A * R := by simp only [A]; ring
  obtain ⟨hfin, hcard⟩ := hC₀ (A * R) hT
  have hYfin : Y.Finite := hfin.subset hYbox
  refine ⟨Y.ncard, ?_, fun z => ?_⟩
  · calc (Y.ncard : ℝ) ≤ ((ratGLBox n 𝒦 (A * R)).ncard : ℝ) := by
          exact_mod_cast Set.ncard_le_ncard hYbox hfin
      _ ≤ C₀ * (1 + A * R) ^ N := hcard
      _ ≤ max C₀ 0 * ((1 + A) * R) ^ N := by
          gcongr
          · exact le_max_left _ _
          · nlinarith
      _ = max C₀ 0 * (1 + A) ^ N * R ^ N := by rw [mul_pow]; ring
  · set S := {γ : rationalGLOne K n | γ • z ∈ (fun y => x * y) '' Q}
    rcases eq_empty_or_nonempty S with h | ⟨γ₀, hγ₀⟩
    · rw [h, encard_empty]
      simp
    have hrat : ∀ δ : rationalGLOne K n, ∃ γ : GL (Fin n) K,
        AdelicGLn.diagonal K n γ = ((δ : normOneGL K n) : AdelicGLn.AdelicGL K n) := fun δ =>
      Subgroup.mem_subgroupOf.1 δ.2
    set f : rationalGLOne K n → GL (Fin n) K := fun δ => Function.invFun (AdelicGLn.diagonal K n)
      (((δ * γ₀⁻¹ : rationalGLOne K n) : normOneGL K n) : AdelicGLn.AdelicGL K n)
    have hf : ∀ δ, AdelicGLn.diagonal K n (f δ) =
        (((δ * γ₀⁻¹ : rationalGLOne K n) : normOneGL K n) : AdelicGLn.AdelicGL K n) := fun δ =>
      Function.invFun_eq (hrat _)
    have hmaps : MapsTo f S Y := by
      intro δ hδ
      obtain ⟨q₁, hq₁, h₁⟩ := hδ
      obtain ⟨q₂, hq₂, h₂⟩ := hγ₀
      have e : ((δ * γ₀⁻¹ : rationalGLOne K n) : normOneGL K n) = x * q₁ * q₂⁻¹ * x⁻¹ := by
        have h₁'' : x * q₁ = (δ : normOneGL K n) * z := h₁
        have h₂'' : x * q₂ = (γ₀ : normOneGL K n) * z := h₂
        have h₁' : (δ : normOneGL K n) = x * q₁ * z⁻¹ := by rw [h₁'', mul_inv_cancel_right]
        have h₂' : (γ₀ : normOneGL K n) = x * q₂ * z⁻¹ := by rw [h₂'', mul_inv_cancel_right]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, h₁', h₂']
        group
      refine ⟨k * (q₁ : AdelicGLn.AdelicGL K n) * (q₂ : AdelicGLn.AdelicGL K n)⁻¹ * k⁻¹,
        ⟨(k, q₁, q₂), ⟨hk, hq₁, hq₂⟩, rfl⟩, ?_⟩
      rw [hf, e]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx]
      group
    have hinj : InjOn f S := by
      intro δ₁ _ δ₂ _ h
      have := congrArg (AdelicGLn.diagonal K n) h
      rw [hf, hf] at this
      exact mul_right_cancel (Subtype.ext (Subtype.ext this))
    calc S.encard ≤ Y.encard := encard_le_encard_of_injOn hmaps hinj
      _ = Y.ncard := hYfin.cast_ncard_eq.symm

end CuspidalSpectrum

end

end GroundTheory.Automorphic
