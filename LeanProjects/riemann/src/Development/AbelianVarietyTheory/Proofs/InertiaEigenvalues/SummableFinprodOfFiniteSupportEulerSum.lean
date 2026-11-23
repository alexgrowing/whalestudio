import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem summable_finprod_of_finite_support_euler : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v)
    (a : ∀ v, X v → ℝ) (s : ι → ℝ), (∀ v x, 0 ≤ a v x) → (∀ v, a v (x0 v) = 1) → Summable s →
    (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, a v x ≤ s v) →
    Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ∏ᶠ v, a v (f.1 v)) := by
  intro ι _ X x0 a s ha h1 hs hC
  classical
  have hs0 : ∀ v, 0 ≤ s v := fun v => by simpa using hC v ∅ (Finset.notMem_empty _)
  refine summable_of_sum_le (c := Real.exp (∑' v, s v)) (fun f => finprod_nonneg fun v => ha v _) ?_
  intro u
  set S : Finset ι := u.biUnion (fun f => f.2.toFinset) with hSdef
  have hsub : ∀ f ∈ u, ∀ w, f.1 w ≠ x0 w → w ∈ S := by
    intro f hf w hw
    exact Finset.mem_biUnion.2 ⟨f, hf, by simpa using hw⟩
  have hval : ∀ f ∈ u, ∏ᶠ v, a v (f.1 v) = ∏ x ∈ S.attach, a x.1 (f.1 x.1) := by
    intro f hf
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · exact (Finset.prod_attach S (fun v => a v (f.1 v))).symm
    · intro w hw
      by_contra hwS
      apply hw
      have : f.1 w = x0 w := by
        by_contra hne; exact hwS (hsub f hf w hne)
      simp [this, h1]
  let C : ∀ v, Finset (X v) := fun v => u.image (fun f => f.1 v)
  let φ : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} → (∀ v ∈ S, X v) := fun f v _ => f.1 v
  have hφinj : Set.InjOn φ u := by
    intro f hf g hg hfg
    apply Subtype.ext
    funext w
    by_cases hw : w ∈ S
    · exact congrFun (congrFun hfg w) hw
    · have hf' : f.1 w = x0 w := by by_contra h; exact hw (hsub f hf w h)
      have hg' : g.1 w = x0 w := by by_contra h; exact hw (hsub g hg w h)
      rw [hf', hg']
  have step1 : ∑ f ∈ u, ∏ᶠ v, a v (f.1 v) = ∑ p ∈ u.image φ, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) := by
    rw [Finset.sum_image hφinj]
    exact Finset.sum_congr rfl hval
  have himg : u.image φ ⊆ S.pi C := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_pi.2 fun v hv => Finset.mem_image_of_mem _ hf
  have step2 : ∑ p ∈ u.image φ, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) ≤
      ∑ p ∈ S.pi C, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ => Finset.prod_nonneg fun x _ => ha _ _
  have hCv : ∀ v, ∑ x ∈ C v, a v x ≤ 1 + s v := by
    intro v
    calc ∑ x ∈ C v, a v x ≤ ∑ x ∈ insert (x0 v) ((C v).erase (x0 v)), a v x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_erase_subset _ _) fun x _ _ => ha v x
      _ = 1 + ∑ x ∈ (C v).erase (x0 v), a v x := by
          rw [Finset.sum_insert (Finset.notMem_erase _ _), h1]
      _ ≤ 1 + s v := by gcongr; exact hC v _ (Finset.notMem_erase _ _)
  calc ∑ f ∈ u, ∏ᶠ v, a v (f.1 v) ≤ ∑ p ∈ S.pi C, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) := step1 ▸ step2
    _ = ∏ v ∈ S, ∑ x ∈ C v, a v x := (Finset.prod_sum S C a).symm
    _ ≤ ∏ v ∈ S, Real.exp (s v) := Finset.prod_le_prod (fun v _ => Finset.sum_nonneg fun x _ => ha v x)
          fun v _ => (hCv v).trans (by linarith [Real.add_one_le_exp (s v)])
    _ = Real.exp (∑ v ∈ S, s v) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' v, s v) := Real.exp_le_exp.2 (hs.sum_le_tsum _ (fun v _ => hs0 v))

end GlobalTheory
