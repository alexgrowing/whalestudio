import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd
open NumberField IsDedekindDomain GlobalTheory.JSW
open scoped ENNReal

noncomputable section
namespace GlobalTheory.RSPole.EulerPole

open Filter Topology GlobalTheory.RSPole

theorem schurAt_const_zero {n : ℕ} (a : Fin n → ℂ) : GlobalTheory.JSW.schurAt (fun _ => 0) a = 1 := by
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem one_le_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) : 1 ≤ schurDir q a x := by
  unfold schurDir
  refine le_trans ?_ (ENNReal.le_tsum ⟨fun _ => 0, antitone_const⟩)
  simp [schurAt_const_zero]

theorem hasProd_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) :
    HasProd f (⨆ s : Finset I, ∏ i ∈ s, f i) :=
  tendsto_atTop_iSup fun _ _ hst => Finset.prod_le_prod_of_subset_of_one_le' hst fun i _ _ => hf i

theorem finset_prod_le_tprod {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (s : Finset I) :
    ∏ i ∈ s, f i ≤ ∏' i, f i := by
  rw [(hasProd_of_one_le f hf).tprod_eq]; exact le_iSup (fun s : Finset I => ∏ i ∈ s, f i) s

theorem le_tprod_of_one_le {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (i : I) : f i ≤ ∏' i, f i := by
  simpa using finset_prod_le_tprod f hf {i}

theorem hasProd_toReal {I : Type} (f : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfin : ∏' i, f i ≠ ⊤) :
    HasProd (fun i => (f i).toReal) (∏' i, f i).toReal := by
  have h := hasProd_of_one_le f hf
  rw [← h.tprod_eq] at h
  have := (ENNReal.tendsto_toReal hfin).comp h
  simpa [HasProd, Function.comp_def, ENNReal.toReal_prod] using this

theorem schurAt_conj {n : ℕ} (l : Fin n → ℕ) (a : Fin n → ℂ) :
    GlobalTheory.JSW.schurAt l (fun i => starRingEnd ℂ (a i)) = starRingEnd ℂ (GlobalTheory.JSW.schurAt l a) := by
  rw [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schurAt, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole

def schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) : ℝ :=
  ‖GlobalTheory.JSW.schurAt l.1 a‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x))

theorem schurTerm_nonneg (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (l) : 0 ≤ schurTerm q a x l := by
  unfold schurTerm; positivity

theorem schurDir_eq (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    schurDir q a x = ∑' l, ENNReal.ofReal (schurTerm q a x l) := rfl

theorem summable_schurTerm (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    Summable (schurTerm q a x) := by
  rw [schurDir_eq] at hfin
  exact (ENNReal.summable_toReal hfin).congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) :
    (schurDir q a x).toReal = ∑' l, schurTerm q a x l := by
  rw [schurDir_eq, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun l => ENNReal.toReal_ofReal (schurTerm_nonneg q a x l)

theorem term_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo le_rfl l.1) (fun i => (α i : ℂ)) *
      GlobalTheory.JSW.schurAt l.1 (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) = ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ) := by
  rw [GlobalTheory.JSW.padTo_self]
  have h1 : (fun j => (((Units.map (starRingEnd ℂ).toMonoidHom ∘ α) j : ℂˣ) : ℂ)) =
      fun j => starRingEnd ℂ (α j : ℂ) := by
    funext j; simp
  rw [h1, schurAt_conj, Complex.mul_conj']
  have h2 : (q : ℂ) ^ (-(x : ℂ)) = (((q : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]; push_cast; rfl
  have h3 : (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) = ((q : ℝ) ^ (-x)) ^ (∑ i, l.1 i) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]; ring_nf
  rw [h2, schurTerm, h3]
  push_cast
  ring

theorem locL_eq (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) (x : ℝ) (hfin : schurDir q (fun i => (α i : ℂ)) x ≠ ⊤) :
    locL q (Finset.univ.val.map α) ((Finset.univ.val.map α).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) =
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
  have hs := summable_schurTerm q _ x hfin
  rw [Multiset.map_map]
  have key := cauchy_locL le_rfl α (Units.map (starRingEnd ℂ).toMonoidHom ∘ α) q (x : ℂ) (hs.congr fun l => by
    rw [← norm_pow, ← norm_mul, term_eq, Complex.norm_real, Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)])
  have h2 : HasSum (fun l => ((schurTerm q (fun i => (α i : ℂ)) x l : ℝ) : ℂ))
      (((schurDir q (fun i => (α i : ℂ)) x).toReal : ℝ) : ℂ) := by
    rw [toReal_schurDir]; exact Complex.hasSum_ofReal.mpr hs.hasSum
  simp only [term_eq] at key
  exact key.unique h2

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Filter Topology GlobalTheory.RSPole Set

theorem schurTerm_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) (l) :
    schurTerm q a y l ≤ schurTerm q a x l := by
  unfold schurTerm
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) ?_) (by positivity)
  have : (0 : ℝ) ≤ ((∑ i, l.1 i : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem schurDir_anti (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) {x y : ℝ} (hxy : x ≤ y) :
    schurDir q a y ≤ schurDir q a x := by
  rw [schurDir_eq, schurDir_eq]
  exact ENNReal.tsum_le_tsum fun l => ENNReal.ofReal_le_ofReal (schurTerm_anti q hq a hxy l)

theorem continuousOn_toReal_schurDir (q : ℕ) (hq : 1 ≤ q) {n : ℕ} (a : Fin n → ℂ) (x₀ : ℝ)
    (hfin : schurDir q a x₀ ≠ ⊤) : ContinuousOn (fun x => (schurDir q a x).toReal) (Ici x₀) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : ContinuousOn (fun x => ∑' l, schurTerm q a x l) (Ici x₀) := by
    refine continuousOn_tsum (u := schurTerm q a x₀) (fun l => ?_) (summable_schurTerm q a x₀ hfin) ?_
    · unfold schurTerm
      exact (continuous_const.mul (continuous_const.rpow (by fun_prop) fun _ => Or.inl hqpos.ne')).continuousOn
    · intro l x hx
      rw [Real.norm_of_nonneg (schurTerm_nonneg _ _ _ _)]
      exact schurTerm_anti q hq a hx l
  exact hc.congr fun x _ => toReal_schurDir q a x

theorem one_le_toReal_schurDir (q : ℕ) {n : ℕ} (a : Fin n → ℂ) (x : ℝ) (hfin : schurDir q a x ≠ ⊤) :
    1 ≤ (schurDir q a x).toReal := by
  have := ENNReal.toReal_mono hfin (one_le_schurDir q a x)
  simpa using this

section
variable {I : Type} (q : I → ℕ) {n : ℕ} (a : I → Fin n → ℂ)

theorem schurDir_ne_top (x : ℝ) (h : eulD q a x ≠ ⊤) (w : I) : schurDir (q w) (a w) x ≠ ⊤ :=
  ne_top_of_le_ne_top h (le_tprod_of_one_le (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) w)

theorem hasProd_eulD (x : ℝ) (h : eulD q a x ≠ ⊤) :
    HasProd (fun w => (schurDir (q w) (a w) x).toReal) (eulD q a x).toReal :=
  hasProd_toReal (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) h

theorem summable_log (x : ℝ) (h : eulD q a x ≠ ⊤) :
    Summable fun w => Real.log (schurDir (q w) (a w) x).toReal := by
  have h1 : ∀ w, 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w)
  refine summable_of_sum_le (c := Real.log (eulD q a x).toReal) (fun w => Real.log_nonneg (h1 w)) fun s => ?_
  rw [← Real.log_prod (fun w _ => (zero_lt_one.trans_le (h1 w)).ne')]
  refine Real.log_le_log (Finset.prod_pos fun w _ => zero_lt_one.trans_le (h1 w)) ?_
  rw [← ENNReal.toReal_prod]
  exact ENNReal.toReal_mono h (finset_prod_le_tprod (fun w => schurDir (q w) (a w) x)
    (fun w => one_le_schurDir _ _ _) s)

theorem toReal_eulD_eq_exp (x : ℝ) (h : eulD q a x ≠ ⊤) :
    (eulD q a x).toReal = Real.exp (∑' w, Real.log (schurDir (q w) (a w) x).toReal) := by
  have h1 : ∀ w, 0 < (schurDir (q w) (a w) x).toReal :=
    fun w => zero_lt_one.trans_le (one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x h w))
  exact (hasProd_eulD q a x h).unique (Real.hasProd_of_hasSum_log h1 (summable_log q a x h).hasSum)

theorem continuousOn_toReal_eulD (hq : ∀ w, 1 ≤ q w) (x₀ : ℝ) (hall : ∀ x, x₀ ≤ x → eulD q a x ≠ ⊤) :
    ContinuousOn (fun x => (eulD q a x).toReal) (Ici x₀) := by
  have hx₀ := hall x₀ le_rfl
  have hF : ∀ w x, x₀ ≤ x → 1 ≤ (schurDir (q w) (a w) x).toReal :=
    fun w x hx => one_le_toReal_schurDir _ _ _ (schurDir_ne_top q a x (hall x hx) w)
  have hc : ContinuousOn (fun x => ∑' w, Real.log (schurDir (q w) (a w) x).toReal) (Ici x₀) := by
    refine continuousOn_tsum (u := fun w => Real.log (schurDir (q w) (a w) x₀).toReal) (fun w => ?_)
      (summable_log q a x₀ hx₀) ?_
    · exact (continuousOn_toReal_schurDir (q w) (hq w) (a w) x₀ (schurDir_ne_top q a x₀ hx₀ w)).log
        fun x hx => (zero_lt_one.trans_le (hF w x hx)).ne'
    · intro w x hx
      rw [Real.norm_of_nonneg (Real.log_nonneg (hF w x hx))]
      refine Real.log_le_log (zero_lt_one.trans_le (hF w x hx)) ?_
      exact ENNReal.toReal_mono (schurDir_ne_top q a x₀ hx₀ w) (schurDir_anti (q w) (hq w) (a w) hx)
  exact (Real.continuous_exp.comp_continuousOn hc).congr fun x hx => toReal_eulD_eq_exp q a x (hall x hx)
end

end GlobalTheory.RSPole.EulerPole

namespace GlobalTheory.RSPole.EulerPole
open Set

theorem eulD_hasProd_locL : ∀ (I : Type) (q : I → ℕ) (n : ℕ) (α : I → Fin n → ℂˣ), (∀ w, 2 ≤ q w) →
    (∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤) →
    (∀ x : ℝ, 1 < x →
      HasProd (fun w => locL (q w) (Finset.univ.val.map (α w))
          ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
        (((GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) ∧
      1 ≤ (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) ∧
    ContinuousOn (fun x => (GlobalTheory.RSPole.eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal) (Set.Ioi 1) := by
  intro I q n α hq hfin
  set a : I → Fin n → ℂ := fun w i => ((α w i : ℂˣ) : ℂ) with ha
  have hq1 : ∀ w, 1 ≤ q w := fun w => le_trans (by norm_num) (hq w)
  refine ⟨fun x hx => ⟨?_, ?_⟩, ?_⟩
  · have h := (hasProd_eulD q a x (hfin x hx)).map Complex.ofRealHom Complex.continuous_ofReal
    have he : (fun w => locL (q w) (Finset.univ.val.map (α w))
        ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) =
        Complex.ofRealHom ∘ fun w => (schurDir (q w) (a w) x).toReal := by
      funext w
      exact locL_eq (q w) (α w) x (schurDir_ne_top q a x (hfin x hx) w)
    rw [he]; exact h
  · have h1 : (1 : ℝ≥0∞) ≤ eulD q a x := by
      simpa [eulD] using finset_prod_le_tprod (fun w => schurDir (q w) (a w) x) (fun w => one_le_schurDir _ _ _) ∅
    simpa using ENNReal.toReal_mono (hfin x hx) h1
  · intro x hx
    have hx' : (1 + x) / 2 < x := by simp only [mem_Ioi] at hx; linarith
    have h := continuousOn_toReal_eulD q a hq1 ((1 + x) / 2) fun y hy => hfin y (by simp only [mem_Ioi] at hx; linarith)
    exact (h.continuousAt (Ici_mem_nhds hx')).continuousWithinAt

end GlobalTheory.RSPole.EulerPole
