import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem exists_fac {Ω : Type} [Field Ω] {S : Scheme.{0}} (x : gp Ω ⟶ S) (s : S) (h : pt x = s) :
    ∃ a : gp Ω ⟶ Spec (S.residueField s), a ≫ S.fromSpecResidueField s = x := by
  obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective x
  have hx : (Scheme.SpecToEquivOfField Ω S).symm ⟨t, a⟩ = Spec.map a ≫ S.fromSpecResidueField t := by
    simp [Scheme.SpecToEquivOfField]
  rw [hx] at h ⊢
  have hs : s ∈ Set.range (S.fromSpecResidueField t) := ⟨pt (Spec.map a), by rw [← pt_comp, h]⟩
  rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hs
  subst hs
  exact ⟨Spec.map a, rfl⟩

theorem UpperTheory.Gal.TranscendenceTraces.multPt_of :
    WtFlat → WtPt → MultBC → MultPt := by
  intro hflat hpt hbc Z S p _ Ω Ω' _ _ _ _ z z' hzz
  obtain ⟨s, hs⟩ : ∃ s, p (pt z) = s := ⟨_, rfl⟩
  have hpb := IsPullback.of_hasPullback p (S.fromSpecResidueField s)
  have hw := hpt (pullback.snd p (S.fromSpecResidueField s))
    (mult (pullback.snd p (S.fromSpecResidueField s))) (hflat _)
  have hm := hbc _ _ _ _ hpb
  obtain ⟨a, ha⟩ := exists_fac (z ≫ p) s (by rw [pt_comp, hs])
  obtain ⟨a', ha'⟩ := exists_fac (z' ≫ p) s (by rw [pt_comp, ← hzz, hs])
  obtain ⟨z1, e1⟩ : ∃ z1 : gp Ω ⟶ pullback p (S.fromSpecResidueField s),
      z1 ≫ pullback.fst _ _ = z := ⟨pullback.lift z a ha.symm, pullback.lift_fst _ _ _⟩
  obtain ⟨z1', e1'⟩ : ∃ z1' : gp Ω' ⟶ pullback p (S.fromSpecResidueField s),
      z1' ≫ pullback.fst _ _ = z' := ⟨pullback.lift z' a' ha'.symm, pullback.lift_fst _ _ _⟩
  have hp1 : pt z1 = pt z1' := by
    apply (IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecResidueField s))).injective
    rw [← pt_comp z1, ← pt_comp z1', e1, e1']
    exact hzz
  have key := hw Ω Ω' z1 z1' hp1
  rw [hm] at key
  simpa [Wt.comap, e1, e1'] using key
