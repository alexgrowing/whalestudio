import Formalism.SharpRestriction.InertJacobiLevels.AsmLed

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

def errPrimes (D : D7) : Finset ℕ :=
  haveI := D.wordFin
  ({D.host.g 0, D.host.g 1, D.host.d} : Finset ℕ) ∪ Finset.univ.image (fun u : D.what₂.Word => (D.mem u).A.T) ∪
    Finset.univ.biUnion (fun u : D.what₂.Word => (D.mem u).C.DGam.primeFactors)

open Classical in

def errSupp (D : D7) (sc : Scale) : Finset D.what₂.places.Pl :=
  (finite_resChar_le D (sc.X'' D.R.n)).toFinset ∪ (finite_resChar_mem D (errPrimes D)).toFinset

theorem Eval_off {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : G.Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ)
    (w : D.what₂.places.Pl) (hw : w ∉ errSupp D L.sc) : Eval L X K c u j w = 0 := by
  classical
  let _ := D.wordFin
  rw [errSupp, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hw
  have h1 : ¬ ((D.what₂.places.resChar w : ℕ) : ℝ) ≤ L.sc.X'' D.R.n := hw.1
  have h2 : D.what₂.places.resChar w ∉ errPrimes D := hw.2
  refine Eval_above L X K c u j w (not_le.1 h1) ?_ ?_ ?_ ?_
  · intro h
    exact h2 (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨u, Finset.mem_univ _, h.symm⟩)))
  · intro h
    refine h2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    rw [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h <;> simp [h]
  · intro h
    refine h2 (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
    simp [h]
  · intro h
    refine h2 (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, Finset.mem_univ _, ?_⟩))
    exact Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, (D.mem u).C.DGam_pos.ne'⟩

variable {D : D7} {sc : Scale} {aT bT : D.host.TT → ℤ} {η Cc Ct CGam : ℝ} {j0 : ℕ}

def baseZ (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : SizeData₂ D :=
  baseL h Nu ∅ (fun _ _ _ => 0) (fun _ _ _ _ => rfl)

open Classical in

def baseE (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) : SizeData₂ D :=
  baseL h Nu (errSupp D sc ∪ S1) (Eval (baseZ h Nu) X K c)
    (fun u j w hw => Eval_off (baseZ h Nu) X K c u j w (fun h' => hw (Finset.mem_union_left _ h')))

open Classical in

theorem subset_supp_baseE (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) : S1 ⊆ (baseE h Nu S1 X K c).supp :=
  fun _ hw => Finset.mem_union_right _ hw

theorem edef_of_keeps (h : LedHyp D sc aT bT η Cc Ct CGam j0) (Nu : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V)
    (S1 : Finset D.what₂.places.Pl) (X : ErrX D) (K : G.Consts) (c : ErrC) (L : SizeData₂ D) (h1 : L.sc = (baseE h Nu S1 X K c).sc)
    (h2 : L.etaSz = (baseE h Nu S1 X K c).etaSz) (h3 : L.Sc = (baseE h Nu S1 X K c).Sc)
    (h4 : L.E = (baseE h Nu S1 X K c).E) : L.EDef X K c := by
  intro u j _ w
  rw [h4]
  show Eval (baseZ h Nu) X K c u j w = Eval L X K c u j w
  unfold Eval EatG EatC EatI EatX
  rw [h1, h2, h3]
  rfl

end Formalism.MainNotions.Inhab

end
