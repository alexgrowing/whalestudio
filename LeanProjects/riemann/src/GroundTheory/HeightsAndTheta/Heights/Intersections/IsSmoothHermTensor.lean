import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_tensor {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) :=
  ContDiffOn.mul hA hB

theorem allSmooth_update {n : ℕ} {L : Fin n → HermLine ι} (hL : AllSmooth L) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : AllSmooth (Function.update L j X) := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simpa using hX
  · simpa [Function.update_of_ne h] using hL i

theorem allSmooth_snoc {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A : HermLine ι} (hA : IsSmoothHerm A) : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa using hA
  · simpa using hL i

theorem isSec_iff (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P := by
  constructor
  · rintro ⟨a, hs, ha, hP⟩
    exact ⟨a, fun k => (ha k).symm, hs, hP⟩
  · rintro ⟨a, ha, hs, hP⟩
    exact ⟨a, hs, fun k => (ha k).symm, hP⟩

theorem IsFamily.equiv_of_rhsR (I : Family ι)
    (hR : ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
      rhsR I P L A s = recR I P L A s) :
    IsFamily I ↔ IsIntersectionFamily I := by
  constructor
  · rintro ⟨hsym, hadd, hrec⟩
    refine ⟨fun P n L σ hP hL => hsym P n L σ trivial hP hL, ?_, ?_⟩
    · intro P n L A B hP hL hA hB
      have hLA : AllSmooth (Fin.snoc L A : Fin (n + 1) → HermLine ι) := allSmooth_snoc hL hA
      have h := hadd P (n + 1) (Fin.snoc L A) (Fin.last n) A B trivial hP hLA hA hB
      simpa only [Fin.update_snoc_last] using h
    · intro P n L A s a hP hL hA ha hs hsP
      have h := hrec P n (Fin.snoc L A) s trivial hP (allSmooth_snoc hL hA)
        (by simpa only [Fin.snoc_last] using (isSec_iff P A s).2 ⟨a, ha, hs, hsP⟩)
      rw [h, Fin.init_snoc, Fin.snoc_last, hR]
  · rintro ⟨hsym, hadd, hrec⟩
    refine ⟨fun P n L σ _ hP hL => hsym P n L σ hP hL, ?_, ?_⟩
    · intro P n L j A B _ hP hL hA hB
      cases n with
      | zero => exact j.elim0
      | succ m =>
        set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap j (Fin.last m) with hσ
        have key : ∀ X : HermLine ι, IsSmoothHerm X →
            I P (m + 1) (Function.update L j X) = I P (m + 1) (Fin.snoc (Fin.init (L ∘ σ)) X) := by
          intro X hX
          have e : Function.update L j X ∘ σ = Fin.snoc (Fin.init (L ∘ σ)) X := by
            rw [Function.update_comp_equiv, hσ, Equiv.symm_swap, Equiv.swap_apply_left]
            conv_lhs => rw [← Fin.snoc_init_self (L ∘ ⇑(Equiv.swap j (Fin.last m)))]
            exact Fin.update_snoc_last _ _ _
          rw [← e, hsym P (m + 1) _ σ hP (allSmooth_update hL j hX)]
        have hL' : ∀ i, IsSmoothHerm (Fin.init (L ∘ σ) i) := fun i => hL _
        rw [key _ (isSmoothHerm_tensor hA hB), key A hA, key B hB]
        exact hadd P m _ A B hP hL' hA hB
    · intro P n L s _ hP hL hs
      obtain ⟨a, ha, hsm, hsP⟩ := (isSec_iff P _ s).1 hs
      have h := hrec P n (Fin.init L) (L (Fin.last n)) s a hP (fun i => hL _) (hL _) ha hsm hsP
      rw [Fin.snoc_init_self] at h
      rw [h, hR]

theorem IsFamily.equiv (I : Family ι) : IsFamily I ↔ IsIntersectionFamily I :=
  IsFamily.equiv_of_rhsR I fun P _ L A s => rhsR.equiv I P L A s

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
