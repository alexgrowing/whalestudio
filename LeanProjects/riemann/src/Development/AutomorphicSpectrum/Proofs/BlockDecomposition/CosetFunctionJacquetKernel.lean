import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem cosetFn_zero_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) :
    cosetFn t hc a (0 : Z) = 0 := by
  apply Subtype.ext
  funext v
  show (cosetSet t c a).indicator (fun _ => (0 : Z)) v = 0
  exact congrFun (Set.indicator_zero Z (cosetSet t c a)) v

theorem cosetFn_add_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z w : Z) :
    cosetFn t hc a (z + w) = cosetFn t hc a z + cosetFn t hc a w := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => z + w) v =
    (cosetSet t c a).indicator (fun _ => z) v + (cosetSet t c a).indicator (fun _ => w) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, add_zero]

theorem cosetFn_smul_val (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (r : ℂ) (z : Z) :
    cosetFn t hc a (r • z) = r • cosetFn t hc a z := by
  apply Subtype.ext
  funext v
  classical
  show (cosetSet t c a).indicator (fun _ => r • z) v =
    r • (cosetSet t c a).indicator (fun _ => z) v
  by_cases hv : v ∈ cosetSet t c a
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, smul_zero]

def topCol (i t : ℕ) (x : Fin i → k) : Multiplicative (Fin (i + t) → k) :=
  Multiplicative.ofAdd (topV k i t x)

theorem topPart_topCol (i t : ℕ) (x : Fin i → k) : topP i t (topCol i t x).toAdd = x := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_topColumn (i t : ℕ) (x : Fin i → k) : middlePart i t (topCol i t x).toAdd = 0 := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_topCol {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    {c : k} (hc : c ≠ 0) (x : Multiplicative (Fin i → k)) (w : Z) :
    fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w) = cosetFn t hc 0 (ρ₀ x w) := by
  apply Subtype.ext
  funext v
  classical
  have h1 : (fibAct t ρ₀ (topCol i t x.toAdd) (cosetFn t hc 0 w)).1 v =
      ρ₀ (Multiplicative.ofAdd (topP i t (topCol i t x.toAdd).toAdd))
        ((cosetFn t hc 0 w).1 (v + middlePart i t (topCol i t x.toAdd).toAdd)) :=
    fibAct_apply t ρ₀ _ _ v
  have h2 : Multiplicative.ofAdd (topP i t (topCol (k := k) i t x.toAdd).toAdd) = x := by
    rw [topPart_topCol]
    rfl
  rw [h1, h2, middlePart_topColumn, add_zero]
  show ρ₀ x ((cosetSet t c 0).indicator (fun _ => w) v) =
    (cosetSet t c 0).indicator (fun _ => ρ₀ x w) v
  by_cases hv : v ∈ cosetSet t c 0
  · simp only [Set.indicator_of_mem hv]
  · simp only [Set.indicator_of_notMem hv, map_zero]

theorem cosetFn_mem_twKer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z)
    (hz : z ∈ twKer ρ₀ ⊤ 1) : cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩,
      cosetFn t hc 0 v, ?_⟩
    have hsub : ρ₀ (n : Multiplicative (Fin i → k)) v - ((1 : (⊤ : Subgroup (Multiplicative (Fin i → k))) →* ℂˣ) n : ℂ) • v =
        ρ₀ (n : Multiplicative (Fin i → k)) v + (-1 : ℂ) • v := by
      simp [sub_eq_add_neg]
    have hrhs : fibAct t ρ₀ (topCol i t (n : Multiplicative (Fin i → k)).toAdd) (cosetFn t hc 0 v) -
        ((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ) ⟨topCol i t (n : Multiplicative (Fin i → k)).toAdd, trivial⟩ : ℂ) • cosetFn t hc 0 v =
        cosetFn t hc 0 (ρ₀ (n : Multiplicative (Fin i → k)) v) + (-1 : ℂ) • cosetFn t hc 0 v := by
      rw [fibAct_topCol]
      simp [sub_eq_add_neg]
    rw [hsub, cosetFn_add_val, cosetFn_smul_val]
    exact hrhs.symm
  | zero => rw [cosetFn_zero_val]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [cosetFn_add_val]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [cosetFn_smul_val]; exact Submodule.smul_mem _ r ha

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer

end
