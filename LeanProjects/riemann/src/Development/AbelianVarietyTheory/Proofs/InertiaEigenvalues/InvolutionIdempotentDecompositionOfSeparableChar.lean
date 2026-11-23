import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsReducedOfSeparableMarkedCharpoly
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

section Generic

variable {R : Type} [CommRing R]

def FieldIdem (f : R) : Prop :=
  IsIdempotentElem f ∧ f ≠ 0 ∧ ∀ y, f * y ≠ 0 → ∃ z, f * y * z = f

theorem FieldIdem.mul_eq_left {u v : R} (hu : FieldIdem u) (hv : IsIdempotentElem v) (h : u * v ≠ 0) :
    u * v = u := by
  obtain ⟨z, hz⟩ := hu.2.2 v h
  calc u * v = (u * v * z) * v := by rw [hz]
    _ = u * v * z * v := rfl
    _ = u * (v * v) * z := by ring
    _ = u := by rw [hv.eq, hz]

theorem FieldIdem.eq_of_mul_ne_zero {u v : R} (hu : FieldIdem u) (hv : FieldIdem v) (h : u * v ≠ 0) :
    u = v := by
  have h1 : u * v = u := hu.mul_eq_left hv.1 h
  have h2 : v * u = v := hv.mul_eq_left hu.1 (by rwa [mul_comm])
  calc u = u * v := h1.symm
    _ = v * u := mul_comm _ _
    _ = v := h2

theorem FieldIdem.map {u : R} (hu : FieldIdem u) (σ : R ≃+* R) : FieldIdem (σ u) := by
  refine ⟨?_, ?_, ?_⟩
  · show σ u * σ u = σ u
    rw [← map_mul, hu.1.eq]
  · intro h0
    exact hu.2.1 (σ.injective (by rw [h0, map_zero]))
  · intro y hy
    have hy' : u * σ.symm y ≠ 0 := by
      intro h0
      apply hy
      have h1 := congrArg σ h0
      rwa [map_mul, RingEquiv.apply_symm_apply, map_zero] at h1
    obtain ⟨z, hz⟩ := hu.2.2 _ hy'
    refine ⟨σ z, ?_⟩
    have h1 := congrArg σ hz
    rwa [map_mul, map_mul, RingEquiv.apply_symm_apply] at h1

theorem exists_fieldIdem_family [IsReduced R] [IsArtinianRing R] :
    ∃ (M : Type) (_ : Fintype M) (f : M → R), CompleteOrthogonalIdempotents f ∧ ∀ m, FieldIdem (f m) := by

  let φ := IsArtinianRing.equivPi R
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hc : CompleteOrthogonalIdempotents (fun m : MaximalSpectrum R => φ.symm (Pi.single m 1)) :=
    (CompleteOrthogonalIdempotents.single (fun I : MaximalSpectrum R => R ⧸ I.asIdeal)).map
      φ.symm.toRingEquiv.toRingHom
  refine ⟨MaximalSpectrum R, inferInstance, fun m => φ.symm (Pi.single m 1), hc, fun m => ?_⟩
  refine ⟨hc.idem m, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun x => φ x m) h0
    simp only [AlgEquiv.apply_symm_apply, map_zero, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · intro y hy
    have ha : φ y m ≠ 0 := by
      intro h0
      apply hy
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      funext j
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hj : j = m
      · subst hj
        rw [Pi.single_eq_same, one_mul]
        exact h0
      · simp only [Pi.single_eq_of_ne hj, zero_mul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
    refine ⟨φ.symm (Pi.single m b), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = m
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
      exact hb
    · simp only [Pi.single_eq_of_ne hj, zero_mul]

end Generic

theorem exists_isPre (K : UQ) (B : InvAlg K) (hP : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  have := InvAlg.isReduced_of_separable_P K B hP
  have : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  obtain ⟨M, _, f, hf, hF⟩ := exists_fieldIdem_family (R := B.A)

  have hex : ∀ m, ∃ m', B.σ (f m) = f m' := by
    intro m
    by_contra hcon
    push Not at hcon
    have hσ := (hF m).map B.σ
    have hzero : ∀ m', B.σ (f m) * f m' = 0 := fun m' => by
      by_contra h
      exact hcon m' (hσ.eq_of_mul_ne_zero (hF m') h)
    apply hσ.2.1
    calc B.σ (f m) = B.σ (f m) * 1 := (mul_one _).symm
      _ = ∑ m', B.σ (f m) * f m' := by rw [← hf.complete, Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero (fun m' _ => hzero m')
  choose τ hτ using hex
  have finj : Function.Injective f := by
    intro a b hab
    by_contra h
    apply (hF a).2.1
    calc f a = f a * f a := (hF a).1.eq.symm
      _ = f a * f b := congrArg (f a * ·) hab
      _ = 0 := hf.ortho h
  have hττ : ∀ m, τ (τ m) = m := by
    intro m
    apply finj
    calc f (τ (τ m)) = B.σ (f (τ m)) := (hτ (τ m)).symm
      _ = B.σ (B.σ (f m)) := by rw [hτ m]
      _ = f m := B.σ_σ _

  obtain ⟨rep, rep_mem, rep_tau⟩ : ∃ rep : M → M, (∀ m, rep m = m ∨ rep m = τ m) ∧
      ∀ m, rep (τ m) = rep m := by
    let enc := Fintype.equivFin M
    refine ⟨fun m => if enc m ≤ enc (τ m) then m else τ m, fun m => ?_, fun m => ?_⟩
    · dsimp only
      split_ifs <;> simp
    · dsimp only
      rw [hττ m]
      by_cases h1 : enc m ≤ enc (τ m) <;> by_cases h2 : enc (τ m) ≤ enc m
      · have h3 : m = τ m := enc.injective (le_antisymm h1 h2)
        rw [if_pos h2, if_pos h1]
        exact h3.symm
      · rw [if_neg h2, if_pos h1]
      · rw [if_pos h2, if_neg h1]
      · exact (le_total (enc m) (enc (τ m))).elim (fun h => absurd h h1) (fun h => absurd h h2)
  have rep_rep : ∀ m, rep (rep m) = rep m := by
    intro m
    rcases rep_mem m with h | h
    · rw [h, h]
    · rw [h, rep_tau, h]
  obtain ⟨g, hg⟩ : ∃ g : M → {m : M // rep m = m}, ∀ m, (g m).1 = rep m :=
    ⟨fun m => ⟨rep m, rep_rep m⟩, fun _ => rfl⟩
  have hfib : ∀ (i : {m : M // rep m = m}) (m : M), g m = i ↔ m = i.1 ∨ m = τ i.1 := by
    intro i m
    rw [Subtype.ext_iff, hg]
    constructor
    · intro h
      rcases rep_mem m with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · right
        have h3 : τ m = i.1 := h'.symm.trans h
        calc m = τ (τ m) := (hττ m).symm
          _ = τ i.1 := by rw [h3]
    · rintro (h | h)
      · rw [h]
        exact i.2
      · rw [h, rep_tau]
        exact i.2
  obtain ⟨e, he⟩ : ∃ e : {m : M // rep m = m} → B.A,
      ∀ i, e i = ∑ m ∈ Finset.univ.filter (fun m => g m = i), f m := ⟨_, fun _ => rfl⟩
  have hsum : ∀ i, e i = if τ i.1 = i.1 then f i.1 else f i.1 + f (τ i.1) := by
    intro i
    have hfil : Finset.univ.filter (fun m => g m = i) = {i.1, τ i.1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib i m
    rw [he, hfil]
    split_ifs with h
    · simp [h]
    · exact Finset.sum_pair (Ne.symm h)
  refine ⟨{m : M // rep m = m}, inferInstance, e, Finset.univ.filter (fun i => τ i.1 = i.1),
    ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · rw [he]
    exact hf.1.isIdempotentElem_sum
  · show e i * e j = 0
    rw [he, he, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply hf.1.mul_sum_of_notMem
    intro ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hij (ha.symm.trans ha')
  · simp_rw [he]
    rw [Finset.sum_fiberwise]
    exact hf.complete
  · refine ⟨f i.1, (hF _).1, (hF _).2.1, (hF _).2.2, fun hi => ?_, fun hi => ?_⟩
    · have hi' : τ i.1 = i.1 := (Finset.mem_filter.mp hi).2
      exact ⟨by rw [hsum i, if_pos hi'], by rw [hτ, hi']⟩
    · have hi' : τ i.1 ≠ i.1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact ⟨by rw [hτ]; exact hf.ortho (Ne.symm hi'), by rw [hsum i, if_neg hi', hτ]⟩

theorem isPre_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := fun K B hP => exists_isPre K B hP

end GlobalTheory.UnitLemma.Desc
