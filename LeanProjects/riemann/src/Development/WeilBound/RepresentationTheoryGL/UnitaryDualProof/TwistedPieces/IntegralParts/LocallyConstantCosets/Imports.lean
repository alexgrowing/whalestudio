import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.UnifLC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem dec (hZ : CR Z) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) {t : kˣ}
    (ht : nabs k t < 1) {F : Sp k n → ℂ} (hF : F ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ (j : ℕ) (S : Finset (Matrix (Fin n) (Fin n) k)), (∀ c ∈ S, c ∈ Z) ∧
      ∀ p ∈ OO Z, F p = ∑ c ∈ S, psi Z ((fun a => a + c) '' ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set _))
        (fun q => F (tr c q)) p := by
  classical
  obtain ⟨W, hW, hWF⟩ := unifLC hF.1
  obtain ⟨j, hj⟩ := lat_small hL ht hW
  have hLat' : IsLat Z ((((t ^ j : kˣ) : k) • L : AddSubgroup (Matrix (Fin n) (Fin n) k))) := isLat_smul hL (t ^ j)
  set L' : AddSubgroup (Matrix (Fin n) (Fin n) k) := (((t ^ j : kˣ) : k) • L) with hLe
  have hL'W : ∀ w ∈ L', w ∈ W := fun w hw => hj (by rw [← AddSubgroup.coe_pointwise_smul]; exact hw)
  obtain ⟨U, hUo, hU0, hUZ⟩ := hLat'.nhd
  have hK : IsCompact (Prod.fst '' tsupport F) := hF.1.2.image continuous_fst
  obtain ⟨S0, hS0, hS0Z, hS0K⟩ := exists_cpt hZ hK
  obtain ⟨S1, hS1⟩ := hS0.elim_finite_subcover (fun c : S0 => (fun a => a + (c : Matrix (Fin n) (Fin n) k)) '' U)
    (fun c => isOpenMap_add_right _ U hUo) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, 0, hU0, zero_add s⟩)
  let g : Matrix (Fin n) (Fin n) k → Matrix (Fin n) (Fin n) k :=
    fun c => Quotient.out (QuotientAddGroup.mk c : Matrix (Fin n) (Fin n) k ⧸ L')
  have hg : ∀ c, g c - c ∈ L' := by
    intro c
    have h1 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk c : Matrix (Fin n) (Fin n) k ⧸ L'))
    have h2 : g c - c = -(-(g c) + c) := by abel
    rw [h2]
    exact L'.neg_mem h1
  have hgeq : ∀ c c', c - c' ∈ L' → g c = g c' := by
    intro c c' h
    show Quotient.out _ = Quotient.out _
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    rw [show -c + c' = -(c - c') by abel]
    exact L'.neg_mem h
  have hgg : ∀ a a', g a - g a' ∈ L' → g a = g a' := by
    intro a a' h
    apply hgeq
    have e : a - a' = (g a - g a') - (g a - a) + (g a' - a') := by abel
    rw [e]
    exact L'.add_mem (L'.sub_mem h (hg a)) (hg a')
  have hmemI : ∀ z c, z ∈ (fun a => a + c) '' (L' : Set (Matrix (Fin n) (Fin n) k)) ↔ z - c ∈ L' := by
    intro z c
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - c, hz, by simp⟩
  refine ⟨j, S1.image (fun c : S0 => g (c : Matrix (Fin n) (Fin n) k)), ?_, ?_⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc
    have e : g (i : Matrix (Fin n) (Fin n) k) = (i : Matrix (Fin n) (Fin n) k) + (g i - i) := by abel
    rw [e]
    exact Z.add_mem (hS0Z i.2) (hLat'.sub (hg _))
  · rintro ⟨x, v⟩ hp
    have hx : x ∈ CC Z := hp.1
    simp only [psi_of_mem (p := (x, v)) hx, tr]
    by_cases hA : ∃ c ∈ S1.image (fun c : S0 => g (c : Matrix (Fin n) (Fin n) k)), zpart Z x - c ∈ L'
    · obtain ⟨c, hcS, hcz⟩ := hA
      rw [Finset.sum_eq_single c]
      · rw [Set.indicator_of_mem ((hmemI _ _).2 hcz), Pi.one_apply, one_mul]
        have e : x - zpart Z x + c = x + (c - zpart Z x) := by abel
        rw [e]
        have hw : c - zpart Z x ∈ L' := by
          rw [show c - zpart Z x = -(zpart Z x - c) by abel]
          exact L'.neg_mem hcz
        exact (hWF _ (hL'W _ hw) (x, v)).symm
      · intro c' hc' hne
        rw [Set.indicator_of_notMem, zero_mul]
        intro h'
        apply hne
        obtain ⟨a', _, rfl⟩ := Finset.mem_image.1 hc'
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hcS
        apply hgg
        have e : g (a' : Matrix (Fin n) (Fin n) k) - g a = (zpart Z x - g a) - (zpart Z x - g a') := by abel
        rw [e]
        exact L'.sub_mem hcz ((hmemI _ _).1 h')
      · intro h
        exact absurd hcS h
    · push_neg at hA
      rw [Finset.sum_eq_zero]
      · by_contra hne
        have hsupp : (x, v) ∈ tsupport F := subset_tsupport F hne
        have hz := hS0K x ⟨⟨(x, v), hsupp, rfl⟩, hx⟩
        obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hS1 hz)
        obtain ⟨u, hu, hue⟩ := hzi
        simp only at hue
        have huZ : u ∈ Z := by
          have e : u = zpart Z x - i := by rw [← hue]; abel
          rw [e]
          exact Z.sub_mem (hS0Z hz) (hS0Z i.2)
        have huL : u ∈ L' := hUZ ⟨hu, huZ⟩
        apply hA (g i) (Finset.mem_image.2 ⟨i, hi, rfl⟩)
        have e : zpart Z x - g i = u - (g i - i) := by rw [← hue]; abel
        rw [e]
        exact L'.sub_mem huL (hg _)
      · intro c hc
        rw [Set.indicator_of_notMem, zero_mul]
        intro h'
        exact hA c hc ((hmemI _ _).1 h')

end PositivityTheory.RgUd.TP.Nil.Fib2

end
