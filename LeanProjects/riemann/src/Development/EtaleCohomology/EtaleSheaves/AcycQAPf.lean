import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.AcycQAPf

def MVHyp (q : ℕ) (i n : ℤ) : Prop := ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) → ∀ f g : S,
  Ideal.span {f, g} = ⊤ → ∀ c : Ht q (sp (Localization.Away (f * g))) n i,
    ∃ a b, c = pull _ (spMap (rL f g)) _ n a - pull _ (spMap (rR f g)) _ n b

def Deg0 : Prop := QAClosed → EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions → LCSplit → A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ), MVHyp q i 0

def Cover : Prop := QAClosed → MV → A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ), MVHyp q i n → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
  ∀ x : Ht q (sp S) (n + 1) i, (∀ p : PrimeSpectrum S, ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0) → x = 0

theorem step (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hC : Cover) (h1 : A1) (b1 : B1) (b2 : B2) (q : ℕ) [NeZero q] (i : ℤ) :
    ∀ k : ℕ, MVHyp q i k → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
      Subsingleton (Ht q (sp S) ((k : ℤ) + 1) i) := by
  intro k hk S _ hS hq
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine hC hQ hM h1 q i k hk S hS hq x fun p => ?_
  exact hZ b1 b2 q S (hQ S hS).1 hq _ i (by omega) x p

theorem AcycQA_of (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hH : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hL : LCSplit) (hD : Deg0) (hC : Cover) :
    AcycQA := by
  intro h1 h9 b1 b2 q _ S _ hS hq
  have key : ∀ k : ℕ, MVHyp q 0 k ∧ ∀ (i : ℤ), MVHyp q i k := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hD hQ hH hL h9 q 0, fun i => by simpa using hD hQ hH hL h9 q i⟩
    | succ k ih =>
      have hv : ∀ (i : ℤ), MVHyp q i ((k + 1 : ℕ) : ℤ) := by
        intro i S' _ hS' hq' f g _ c
        have hfg : QA (Localization.Away (f * g)) := (hQ S' hS').2.1 (f * g)
        have hqfg : IsUnit (q : Localization.Away (f * g)) := by
          simpa using hq'.map (algebraMap S' (Localization.Away (f * g)))
        have hs := step hQ hZ hM hC h1 b1 b2 q i k (ih.2 i) _ hfg hqfg
        refine ⟨0, 0, ?_⟩
        have : c = 0 := by
          have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
          revert c; rw [e]; intro c; exact Subsingleton.elim _ _
        simp [this]
      exact ⟨hv 0, hv⟩
  intro n i hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  exact step hQ hZ hM hC h1 b1 b2 q i k ((key k).2 i) S hS hq

end LateralTheory.E.AcycQAPf
