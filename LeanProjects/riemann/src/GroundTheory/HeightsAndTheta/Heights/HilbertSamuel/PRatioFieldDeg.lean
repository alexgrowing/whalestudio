import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatioFieldDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RatioFieldDeg

variable {ι : Type}

def quotCone {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ)) (hu : coordIdeal ℤ u = I) :
    MvPolynomial ι ℤ ⧸ I →+* Polynomial E :=
  Ideal.Quotient.lift I (coneMap ℤ u).toRingHom (fun a ha => by rw [← hu] at ha; exact ha)

theorem quotCone_injective {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : Function.Injective (quotCone u I hu) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.Quotient.eq_zero_iff_mem, ← hu, coordIdeal, RingHom.mem_ker]
  simpa [quotCone] using ha

theorem isDomain_quot {E : Type} [Field E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) : IsDomain (MvPolynomial ι ℤ ⧸ I) :=
  Function.Injective.isDomain _ (quotCone_injective u I hu)

theorem charZero_frac {E : Type} [Field E] [CharZero E] (u : ι → E) (I : Ideal (MvPolynomial ι ℤ))
    (hu : coordIdeal ℤ u = I) [IsDomain (MvPolynomial ι ℤ ⧸ I)] :
    CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I)) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  refine ⟨fun n m h => ?_⟩
  have h' := congrArg (IsFractionRing.lift hg) h
  simp only [map_natCast] at h'
  exact Nat.cast_injective h'

section

variable (I : Ideal (MvPolynomial ι ℤ)) [IsDomain (MvPolynomial ι ℤ ⧸ I)]

def coord (i : ι) : FractionRing (MvPolynomial ι ℤ ⧸ I) :=
  algebraMap _ _ (Ideal.Quotient.mk I (X i))

variable [CharZero (FractionRing (MvPolynomial ι ℤ ⧸ I))]

def ratField {κ : Type} (s : κ → ι) : IntermediateField ℚ (FractionRing (MvPolynomial ι ℤ ⧸ I)) :=
  IntermediateField.adjoin ℚ {t | ∃ k l, t = coord I (s k) / coord I (s l)}

theorem projDeg_eq {E : Type} [Field E] [CharZero E] (u : ι → E) (hu : coordIdeal ℤ u = I) {D : ℕ}
    (e : Fin (D + 1) → ι) :
    projDeg u e = IntermediateField.relfinrank (ratField I e) (ratField I id) := by
  have hg : Function.Injective ((algebraMap (Polynomial E) (RatFunc E)).comp (quotCone u I hu)) :=
    (IsFractionRing.injective (Polynomial E) (RatFunc E)).comp (quotCone_injective u I hu)
  let f : FractionRing (MvPolynomial ι ℤ ⧸ I) →ₐ[ℚ] RatFunc E := (IsFractionRing.lift hg).toRatAlgHom
  let c : E →ₐ[ℚ] RatFunc E := (RatFunc.C : E →+* RatFunc E).toRatAlgHom
  have hx : ∀ i, f (coord I i) = RatFunc.C (u i) * RatFunc.X := by
    intro i
    simp [f, coord, IsFractionRing.lift_algebraMap, quotCone, coneMap, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X]
  have hr : ∀ i j, f (coord I i / coord I j) = c (u i / u j) := by
    intro i j
    rw [map_div₀, hx, hx, mul_div_mul_right _ _ RatFunc.X_ne_zero]
    simp [c, map_div₀]
  have hmap : ∀ {κ : Type} (s : κ → ι), (ratField I s).map f = (fnField (u ∘ s)).map c := by
    intro κ s
    rw [ratField, fnField, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, (hr _ _).symm⟩
    · rintro ⟨_, ⟨k, l, rfl⟩, rfl⟩
      exact ⟨_, ⟨k, l, rfl⟩, hr _ _⟩
  rw [← IntermediateField.relfinrank_map_map (ratField I e) (ratField I id) f, hmap, hmap,
    IntermediateField.relfinrank_map_map]
  rfl

end

theorem proof : RatioFieldDeg.Statement := by
  intro ι E₁ E₂ _ _ _ _ u v D e h
  have : IsDomain (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u) := isDomain_quot u _ rfl
  have : CharZero (FractionRing (MvPolynomial ι ℤ ⧸ coordIdeal ℤ u)) := charZero_frac u _ rfl
  rw [projDeg_eq (coordIdeal ℤ u) u rfl e, projDeg_eq (coordIdeal ℤ u) v h.symm e]

end RatioFieldDeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
