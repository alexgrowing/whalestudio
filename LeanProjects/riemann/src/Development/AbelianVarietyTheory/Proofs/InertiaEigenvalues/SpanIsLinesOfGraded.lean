import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.SenLines.SplitFil

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def lineMap {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) : (Fin r → F⟦X⟧) →ₗ[F] (ℤ → M) where
  toFun c := ∑ k, serLine (u k) (d k) (c k)
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.add_apply]
    split_ifs <;> simp [add_smul]
  map_smul' a c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext m
    simp only [serLine, Pi.smul_apply]
    split_ifs <;> simp [mul_smul]

theorem smul_serMul (a : F) (f : F⟦X⟧) {y : ℤ → M} (hy : IsLaurent y) :
    a • serMul f y = serMul (a • f) y := by
  funext m
  simp only [Pi.smul_apply, serMul]
  rw [smul_finsum' a (serMul_finite f hy m)]
  refine finsum_congr fun j => ?_
  simp [mul_smul]

theorem mem_serSpan_iff {N : Type} (L : N → ℤ → M) (hL : ∀ x, IsLaurent (L x)) (y : ℤ → M) :
    y ∈ serSpan F (Set.range L) ↔
      ∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j)) := by
  constructor
  · intro hy
    obtain ⟨n, c, g, h⟩ := Submodule.mem_span_set'.mp hy
    have hg : ∀ i, ∃ (f : F⟦X⟧) (x : N), (g i : ℤ → M) = serMul f (L x) := fun i => by
      obtain ⟨f, w, ⟨x, rfl⟩, -, h⟩ := (g i).2
      exact ⟨f, x, h⟩
    choose f x hg using hg
    refine ⟨n, x, fun i => c i • f i, ?_⟩
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg, smul_serMul _ _ (hL _)]
    rfl
  · rintro ⟨s, x, f, rfl⟩
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.subset_span ⟨f j, L (x j), ⟨x j, rfl⟩, hL _, rfl⟩

theorem exists_coef {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (a : ℤ) (z : M)
    (hz : z ∈ Submodule.span F (d '' {k | a ≤ u k})) :
    ∃ c : Fin r → F, (∀ k, u k < a → c k = 0) ∧ z = ∑ k, c k • d k := by
  classical
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨Pi.single k 1, fun k' hk' => Pi.single_eq_of_ne ?_ _, ?_⟩
    · rintro rfl
      exact absurd hk (not_le.mpr hk')
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    exact ⟨c + c', fun k hk => by simp [hc k hk, hc' k hk],
      by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul b x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨b • c, fun k hk => by simp [hc k hk], by simp [mul_smul, Finset.smul_sum]⟩

theorem gradedSer_eq_range {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M)
    (hA : ∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) :
    gradedSer A = LinearMap.range (lineMap (F := F) u d) := by
  apply le_antisymm
  · refine iSup_le fun a y hy => ?_
    obtain ⟨hy0, hy1⟩ := hy
    have hex : ∀ m : ℤ, ∃ c : Fin r → F, (∀ k, m + u k < 0 → c k = 0) ∧
        y m = ∑ k, c k • d k := fun m => by
      by_cases hm : m < -a
      · exact ⟨0, fun _ _ => rfl, by simp [hy0 m hm]⟩
      · obtain ⟨c, hc, h⟩ := exists_coef u d a (y m) (hA a ▸ hy1 m)
        exact ⟨c, fun k hk => hc k (by omega), h⟩
    choose c hc hyc using hex
    refine ⟨fun k => PowerSeries.mk fun j => c ((j : ℤ) - u k) k, ?_⟩
    funext m
    change (∑ k, serLine (u k) (d k) (PowerSeries.mk fun j => c ((j : ℤ) - u k) k)) m = y m
    rw [Finset.sum_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold serLine
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc m k (not_le.mp h), zero_smul]
  · rintro _ ⟨c, rfl⟩
    change (∑ k, serLine (u k) (d k) (c k)) ∈ _
    refine Submodule.sum_mem _ fun k _ => ?_
    refine Submodule.mem_iSup_of_mem (u k) ⟨fun m hm => ?_, fun m => ?_⟩
    · unfold serLine
      rw [if_neg (by omega)]
    · unfold serLine
      split_ifs
      · rw [hA]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, le_refl (u k), rfl⟩)
      · exact Submodule.zero_mem _

theorem spanIsLines_of_graded : ∀ {F M N : Type} [Field F] [AddCommGroup M] [Module F M] (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M), (∀ x, GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent (L x)) → (∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serSpan F (Set.range L) = GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.gradedSer A → GlobalTheory.SenLines.SpanIsLines L u d F := by
  intro F M N _ _ _ L r u d A hL hA h y
  rw [← mem_serSpan_iff L hL, h, gradedSer_eq_range u d A hA]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

end GlobalTheory.SenLines.SplitFil
