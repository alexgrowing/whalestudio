import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.nonSS_mono :
    ∀ (R R' S G G' : Type) [CommRing R] [CommRing R'] [CommRing S] [Group G] [Group G'] (p : G' →* G) (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R' G')) (φ : R →+* S) (φ' : R' →+* S) (Q : Ideal S), Function.Surjective p → (∀ z ∈ I', MonoidAlgebra.mapDomainRingHom S p (MonoidAlgebra.mapRingHom G' φ' z) ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I)) → NonSS I φ Q → NonSS I' φ' Q := by
  intro R R' S G G' _ _ _ _ _ p I I' φ φ' Q hp hI ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (f.comp φ) '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' (f.comp φ') '' I') with hJ'
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    J.ringCon.mk'.comp (MonoidAlgebra.mapDomainRingHom κ p)
  have hψs : Function.Surjective ψ := by
    have h1 : Function.Surjective (MonoidAlgebra.mapDomainRingHom κ p) := by
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact ⟨0, map_zero _⟩
      | add a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' + b', map_add _ _ _⟩
      | single g c =>
        obtain ⟨g', rfl⟩ := hp g
        exact ⟨MonoidAlgebra.single g' c, by simp⟩
    exact (RingCon.mk'_surjective _).comp h1
  have hcomm : ∀ w : MonoidAlgebra S G',
      MonoidAlgebra.mapDomainRingHom κ p (MonoidAlgebra.mapRingHom G' f w) =
        MonoidAlgebra.mapRingHom G f (MonoidAlgebra.mapDomainRingHom S p w) := by
    intro w
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g c => simp
  have hcomp : ∀ (T H : Type) [CommRing T] [Group H] (θ : T →+* S) (z : MonoidAlgebra T H),
      MonoidAlgebra.mapRingHom H (f.comp θ) z =
        MonoidAlgebra.mapRingHom H f (MonoidAlgebra.mapRingHom H θ z) := by
    intro T H _ _ θ z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g c => simp
  have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I) ≤
      J.comap (MonoidAlgebra.mapRingHom G f) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, ← hcomp]
    exact TwoSidedIdeal.subset_span ⟨y, hy, rfl⟩
  have hle' : J' ≤ J.comap (MonoidAlgebra.mapDomainRingHom κ p) := by
    rw [hJ', TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hcomp, hcomm, ← TwoSidedIdeal.mem_comap]
    exact hle (hI z hz)
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    have h1 : a - b ∈ J' := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    have h2 := hle' h1
    rw [TwoSidedIdeal.mem_comap, map_sub] at h2
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h2)
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := hψs y
  exact ⟨(x : J'.ringCon.Quotient), rfl⟩
