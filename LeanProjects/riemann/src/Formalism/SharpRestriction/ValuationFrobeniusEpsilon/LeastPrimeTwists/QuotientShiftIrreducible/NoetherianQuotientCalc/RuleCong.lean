import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

namespace Cong

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem lsmul_eq (F : GMod B R k) {s s' : R} (h : s - s' ∈ F.Ann) :
    LinearMap.lsmul R F.M s = LinearMap.lsmul R F.M s' := by
  ext x
  have hx : (s - s') • x = 0 := Module.mem_annihilator.1 h x
  rw [sub_smul, sub_eq_zero] at hx
  exact hx

theorem quot_eq (F : GMod B R k) {s s' : R} (h : s - s' ∈ F.Ann) : F.quot s = F.quot s' := by
  unfold GMod.quot
  rw [lsmul_eq F h]

theorem ann_eq (F : GMod B R k) {s s' : R} (d : Deg k) (h : s - s' ∈ F.Ann) :
    F.ann s d = F.ann s' d := by
  unfold GMod.ann
  rw [lsmul_eq F h]

theorem ann_le_quot (F : GMod B R k) (s : R) : F.Ann ≤ (F.quot s).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro y
  obtain ⟨x, rfl⟩ := (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ_surjective y
  exact (map_smul (LinearMap.range (LinearMap.lsmul R F.M s)).mkQ a x).symm.trans
    ((congrArg _ (ha x)).trans (map_zero _))

theorem ann_le_ann (F : GMod B R k) (s : R) (d : Deg k) : F.Ann ≤ (F.ann s d).Ann := by
  intro a ha
  rw [GMod.Ann, Module.mem_annihilator] at *
  intro x
  exact Subtype.ext (ha x.1)

theorem chi_cong {ts ts' : List (Deg k × R)} : ∀ (F : GMod B R k),
    List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2 - q.2 ∈ F.Ann) ts ts' →
      ∀ m, chi ts F m = chi ts' F m := by
  induction ts generalizing ts' with
  | nil =>
    intro F h m
    cases h
    rfl
  | cons p ts ih =>
    intro F h m
    cases h with
    | @cons _ q _ ts'' hpq hrest =>
      obtain ⟨d, s⟩ := p
      obtain ⟨d', s'⟩ := q
      obtain ⟨hd, hs⟩ := hpq
      have hd' : d = d' := hd
      subst hd'
      have hs' : s - s' ∈ F.Ann := hs
      show chi ts (F.quot s) m - chi ts (F.ann s d) m =
        chi ts'' (F.quot s') m - chi ts'' (F.ann s' d) m
      rw [← quot_eq F hs', ← ann_eq F d hs',
        ih (F.quot s) (hrest.imp fun _ _ h => ⟨h.1, ann_le_quot F s h.2⟩) m,
        ih (F.ann s d) (hrest.imp fun _ _ h => ⟨h.1, ann_le_ann F s d h.2⟩) m]

end Cong

end Formalism.MainNotions.V.Pf.V2.Calc
