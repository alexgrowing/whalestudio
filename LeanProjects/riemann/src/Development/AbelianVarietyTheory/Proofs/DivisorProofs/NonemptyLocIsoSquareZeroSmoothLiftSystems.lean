import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys.LocalIsomorphism

theorem fix_of_mem {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b)
    (x : B) (hx : x ∈ I.map (algebraMap R B)) : e x = x := by
  set J := I.map (algebraMap R B) with hJdef
  have hδ : ∀ y, e y - y ∈ J := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  have hsq : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := fun a ha b hb ↦ by
    have : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hJ] at this
    simpa using this
  let T : Ideal B :=
    { carrier := {x | ∀ y, e (x * y) = x * y}
      add_mem' := fun {a b} ha hb y ↦ by simp only [Set.mem_setOf_eq] at *; rw [add_mul, map_add, ha, hb]
      zero_mem' := fun y ↦ by simp
      smul_mem' := fun c {a} ha y ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        rw [mul_assoc, mul_left_comm, ha, mul_left_comm] }
  have hIT : J ≤ T := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    intro r hr y
    show e (algebraMap R B r * y) = algebraMap R B r * y
    have hr' : algebraMap R B r ∈ J := Ideal.mem_map_of_mem _ hr
    rw [map_mul, AlgHom.commutes]
    have h0 := hsq _ hr' _ (hδ y)
    rw [mul_sub] at h0
    exact sub_eq_zero.1 h0
  have := hIT hx 1
  simpa using this

theorem bij {R B B₀ : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing B₀]
    (I : Ideal R) (hJ : I.map (algebraMap R B) ^ 2 = 0) (p : B →+* B₀)
    (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (e : B →ₐ[R] B) (he : ∀ b, p (e b) = p b) :
    Function.Bijective e := by
  have hδ : ∀ y, e y - y ∈ I.map (algebraMap R B) := fun y ↦ (hker _).1 (by rw [map_sub, he, sub_self])
  refine ⟨(injective_iff_map_eq_zero e).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
  · have hb' : b ∈ I.map (algebraMap R B) := (hker b).1 (by rw [← he, hb, map_zero])
    rw [← fix_of_mem I hJ p hker e he b hb', hb]
  · refine ⟨c - (e c - c), ?_⟩
    rw [map_sub, fix_of_mem I hJ p hker e he _ (hδ c)]
    ring

theorem nil {R C D : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing D] [Algebra R D] (I : Ideal R)
    (q : C →ₐ[R] D) (h : ∀ b, q b = 0 ↔ b ∈ I.map (algebraMap R C)) (h2 : I.map (algebraMap R C) ^ 2 = 0) :
    IsNilpotent (RingHom.ker (q : C →+* D)) := ⟨2, by
  have : RingHom.ker (q : C →+* D) = I.map (algebraMap R C) := Ideal.ext fun b ↦ by
    rw [RingHom.mem_ker]; exact h b
  rw [this, h2]⟩

theorem exists_iso {R R₀ B B' B₀ : Type} [CommRing R] [CommRing R₀] [CommRing B] [Algebra R B] [CommRing B']
    [Algebra R B'] [CommRing B₀] [Algebra R₀ B₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (p : B →+* B₀) (p' : B' →+* B₀) (hp : SemiHom π p) (hp' : SemiHom π p')
    (hs : Function.Surjective p) (hs' : Function.Surjective p')
    (hk : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (hk' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B'))
    [Algebra.FormallySmooth R B] [Algebra.FormallySmooth R B'] :
    ∃ φ : B ≃ₐ[R] B', ∀ b, p' (φ b) = p b := by
  letI : Algebra R B₀ := ((algebraMap R₀ B₀).comp π).toAlgebra
  let P : B →ₐ[R] B₀ := { p with commutes' := fun r ↦ hp.map_algebraMap r }
  let P' : B' →ₐ[R] B₀ := { p' with commutes' := fun r ↦ hp'.map_algebraMap r }
  have hJ := map_sq hI B
  have hJ' := map_sq hI B'
  let φ : B →ₐ[R] B' := Algebra.FormallySmooth.liftOfSurjective P P' hs' (nil I P' hk' hJ')
  let ψ : B' →ₐ[R] B := Algebra.FormallySmooth.liftOfSurjective P' P hs (nil I P hk hJ)
  have hφ : ∀ b, p' (φ b) = p b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P P' hs' (nil I P' hk' hJ') b
  have hψ : ∀ b, p (ψ b) = p' b := fun b ↦
    Algebra.FormallySmooth.liftOfSurjective_apply P' P hs (nil I P hk hJ) b
  have b1 := bij I hJ p hk (ψ.comp φ) fun b ↦ by simp [hψ, hφ]
  have b2 := bij I hJ' p' hk' (φ.comp ψ) fun b ↦ by simp [hψ, hφ]
  refine ⟨AlgEquiv.ofBijective φ ⟨fun x y h ↦ b1.1 (by simp [h]), fun c ↦ ?_⟩, hφ⟩
  obtain ⟨d, hd⟩ := b2.2 c
  exact ⟨ψ d, hd⟩

end GlobalTheory.LiftSys.LocalIsomorphism

namespace GlobalTheory.LiftSys

theorem locIso_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀),
    ∀ S S' : Sys I π s₀, Nonempty (S.LocIso S') := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ S S'
  have h : ∀ U, ∃ φ : S.F.obj U ≃ₐ[R] S'.F.obj U, ∀ b, S'.p U (φ b) = S.p U b := fun U ↦ by
    haveI := (S.smooth U).formallySmooth
    haveI := (S'.smooth U).formallySmooth
    exact LocalIsomorphism.exists_iso I hI π (S.p U) (S'.p U) (S.semi U) (S'.semi U) (S.surj U) (S'.surj U)
      (S.ker U) (S'.ker U)
  exact ⟨⟨fun U ↦ (h U).choose, fun U ↦ (h U).choose_spec⟩⟩

end GlobalTheory.LiftSys
