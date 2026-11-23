import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

open Classical in
private lemma cyc_eq_sum {S Y : Scheme.{0}} (c : Corr S Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y) (AF : Finset (gp Ω ⟶ c.Z)) (hAF : ∀ s, s ∈ AF ↔ s ≫ c.p = x) :
    c.cyc Ω x y = ∑ s ∈ AF with s ≫ c.f = y, c.w Ω s := by
  have hs : {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y} = ↑(AF.filter (fun s => s ≫ c.f = y)) := by
    ext z
    simp [hAF]
  show (∑ᶠ (z : gp Ω ⟶ c.Z) (_ : z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}), c.w Ω z) = _
  rw [hs, finsum_mem_coe_finset]

theorem UpperTheory.Gal.TranscendenceTraces.cycComp_of :
    FibFin → CycComp := by
  classical
  intro hF S Y X c d e a b pb hp hf hw Ω _ _ x y
  haveI := c.fin
  haveI := d.fin
  haveI := e.fin
  let A := (hF c.p Ω x).toFinset
  have hAm : ∀ s, s ∈ A ↔ s ≫ c.p = x := fun s => by simp [A, fib]
  let B : (gp Ω ⟶ Y) → Finset (gp Ω ⟶ d.Z) := fun t => (hF d.p Ω t).toFinset
  have hBm : ∀ t u, u ∈ B t ↔ u ≫ d.p = t := fun t u => by simp [B, fib]
  let E := (hF e.p Ω x).toFinset
  have hEm : ∀ z, z ∈ E ↔ z ≫ e.p = x := fun z => by simp [E, fib]
  have hR : (∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y) =
      ∑ s ∈ A, c.w Ω s * d.cyc Ω (s ≫ c.f) y := by
    rw [finsum_eq_sum_of_support_subset (s := A.image (· ≫ c.f))]
    · rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := A.image (· ≫ c.f)) (g := (· ≫ c.f))
          (fun s hs => Finset.mem_image_of_mem _ hs)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.1 hs).2]
    · intro t ht
      rw [Function.mem_support] at ht
      by_contra hn
      apply ht
      rw [cyc_eq_sum c Ω x t A hAm, Finset.sum_eq_zero, zero_mul]
      intro s hs
      exact absurd (Finset.mem_coe.2 (Finset.mem_image.2
        ⟨s, (Finset.mem_filter.1 hs).1, (Finset.mem_filter.1 hs).2⟩)) hn
  have hmaps : ∀ z ∈ E.filter (fun z => z ≫ e.f = y), z ≫ b ∈ A := by
    intro z hz
    rw [hAm, Category.assoc, ← hp]
    exact (hEm z).1 (Finset.mem_filter.1 hz).1
  rw [hR, cyc_eq_sum e Ω x y E hEm, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [cyc_eq_sum d Ω (s ≫ c.f) y (B (s ≫ c.f)) (hBm _), Finset.mul_sum]
  refine Finset.sum_bij' (fun z _ => z ≫ a)
    (fun u hu => pb.lift u s ((hBm _ u).1 (Finset.mem_filter.1 hu).1)) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, hEm, hBm] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pb.w, ← Category.assoc, hz.2]
    · rw [Category.assoc, ← hf, hz.1.2]
  · intro u hu
    have hu' := Finset.mem_filter.1 hu
    simp only [Finset.mem_filter, hEm]
    refine ⟨⟨?_, ?_⟩, pb.lift_snd _ _ _⟩
    · rw [hp, ← Category.assoc, pb.lift_snd]
      exact (hAm s).1 hs
    · rw [hf, ← Category.assoc, pb.lift_fst]
      exact hu'.2
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    apply pb.hom_ext
    · rw [pb.lift_fst]
    · rw [pb.lift_snd, hz'.2]
  · intro u hu
    exact pb.lift_fst _ _ _
  · intro z hz
    have hz' := Finset.mem_filter.1 hz
    rw [hw]
    show d.w Ω (z ≫ a) * c.w Ω (z ≫ b) = c.w Ω s * d.w Ω (z ≫ a)
    rw [hz'.2, mul_comm]
