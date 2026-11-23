import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMaximalIdealOfTrdegLe
open IsLocalRing NumberField

namespace GlobalTheory.PointAlg

theorem trdeg_le_of_hom_algClosure (X Y Z : Type) [Field X] [Field Y] [Field Z] [Algebra ℚ X] [Algebra ℚ Y]
    (f : X →+* AlgebraicClosure Z) (e : Y →+* Z) (he : Function.Surjective e) :
    Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ Y := by
  letI : Algebra ℚ Z := (e.comp (algebraMap ℚ Y)).toAlgebra
  have h1 : Algebra.trdeg ℚ X ≤ Algebra.trdeg ℚ (AlgebraicClosure Z) :=
    trdeg_le_of_injective f.toRatAlgHom f.injective
  have h2 : Algebra.trdeg ℚ Z ≤ Algebra.trdeg ℚ Y :=
    trdeg_le_of_surjective e.toRatAlgHom he
  have h3 := trdeg_add_eq ℚ Z (A := AlgebraicClosure Z)
  rw [trdeg_eq_zero (R := Z) (A := AlgebraicClosure Z), add_zero] at h3
  exact h1.trans (h3.ge.trans h2)

theorem closed_point_of_values (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R]
    [IsLocalRing R] [Field K] (b : F →+* A) (hb : b.EssFiniteType) (ψ : A →+* R) (hψ : GlobalTheory.TChart.IsComplAt ψ)
    (ev : R →+* K) (k₀ : Subfield K) (hk : Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)))
    (hev : ∀ a, ev (ψ a) ∈ k₀) : (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  obtain ⟨j⟩ := hk
  obtain ⟨-, -, -, hmap, hres⟩ := hψ
  set q : Ideal A := (maximalIdeal R).comap ψ with hq
  haveI hqp : q.IsPrime := Ideal.comap_isPrime ψ _
  let L := Localization.AtPrime q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := fun y => by
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  let Φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  have hΦ : ∀ a, Φ (algebraMap A L a) = ψ a := fun a => IsLocalization.lift_eq hu a
  have hne : ∀ a, IsUnit (ψ a) → ev (ψ a) ≠ 0 := fun a h => (h.map ev).ne_zero
  have hΦk : ∀ x, ev (Φ x) ∈ k₀ := by
    intro x
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg (fun t => ev (Φ t)) h
    simp only [map_mul, hΦ] at h2
    rw [eq_div_of_mul_eq (hne _ (hu s)) h2]
    exact k₀.div_mem (hev _) (hev _)
  haveI : IsLocalHom Φ := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj q.primeCompl x
    have h2 := congrArg Φ h
    simp only [map_mul, hΦ] at h2
    have ha : IsUnit (ψ a) := h2 ▸ hx.mul (hu s)
    have ha' : a ∈ q.primeCompl := fun h => (mem_maximalIdeal _).mp h ha
    have := IsLocalization.map_units L ⟨a, ha'⟩
    simp only at h
    exact isUnit_of_mul_isUnit_left (h ▸ this)
  have hsurj : Function.Surjective (ResidueField.map Φ) := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    obtain ⟨a, s, hs, h⟩ := hres r
    rw [← residue_eq_zero_iff, map_sub, map_mul, sub_eq_zero] at h
    refine ⟨residue L (algebraMap A L a) / residue L (algebraMap A L s), ?_⟩
    rw [map_div₀, ResidueField.map_residue, ResidueField.map_residue, hΦ, hΦ, ← h]
    exact mul_div_cancel_right₀ _ (hs.map (residue R)).ne_zero
  let g : L →+* AlgebraicClosure (ResidueField R) := j.comp ((ev.comp Φ).codRestrict k₀ hΦk)
  haveI hP : (RingHom.ker g).IsPrime := RingHom.ker_isPrime g
  have hE : ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).EssFiniteType := by
    refine RingHom.EssFiniteType.comp (RingHom.EssFiniteType.comp ?_ hb) ?_
    · exact RingHom.essFiniteType_algebraMap.mpr inferInstance
    · exact RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization L q.primeCompl)
  letI : Algebra ℚ L := ((algebraMap A L).comp (b.comp (algebraMap ℚ F))).toAlgebra
  have hmax : RingHom.ker g = maximalIdeal L :=
    GlobalTheory.eq_maximalIdeal_of_trdeg_le ℚ L hE _ hP
      (trdeg_le_of_hom_algClosure _ _ _
        (IsFractionRing.lift (K := FractionRing (L ⧸ RingHom.ker g)) (RingHom.kerLift_injective g))
        (ResidueField.map Φ) hsurj)
  have h0 : ∀ r ∈ maximalIdeal R, ev r = 0 := by
    have : maximalIdeal R ≤ RingHom.ker ev := by
      rw [← hmap, Ideal.map_le_iff_le_comap]
      intro a ha
      have h1 : algebraMap A L a ∈ RingHom.ker g := by
        rw [hmax]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L q a).mpr ha
      rw [RingHom.mem_ker] at h1
      have h2 := congrArg Subtype.val (j.injective (h1.trans (map_zero j).symm))
      change ev (Φ (algebraMap A L a)) = 0 at h2
      rw [hΦ] at h2
      exact h2
    exact fun r hr => this hr
  refine ⟨h0, fun r => ?_⟩
  obtain ⟨a, s, hs, h⟩ := hres r
  have h2 := h0 _ h
  rw [map_sub, map_mul, sub_eq_zero] at h2
  rw [eq_div_of_mul_eq (hne _ hs) h2]
  exact k₀.div_mem (hev _) (hev _)

end GlobalTheory.PointAlg
