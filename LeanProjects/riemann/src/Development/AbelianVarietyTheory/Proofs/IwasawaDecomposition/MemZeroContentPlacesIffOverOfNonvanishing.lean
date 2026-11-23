import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.TwistedPlaceExtensions

theorem mem_conjPl_iff {K : Type} [Field K] [StarRing K] (Q : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) :
    y ∈ (Formalism.DivisionValues.conjPl Q).asIdeal ↔ (Formalism.DivisionValues.cO K).symm y ∈ Q.asIdeal := by
  show y ∈ Ideal.map (Formalism.DivisionValues.cO K) Q.asIdeal ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, (Formalism.DivisionValues.cO K).apply_symm_apply y⟩

theorem coe_cO {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : ((Formalism.DivisionValues.cO K y : 𝓞 K) : K) = star (y : K) := rfl

theorem coe_cO_symm {K : Type} [Field K] [StarRing K] (y : 𝓞 K) : (((Formalism.DivisionValues.cO K).symm y : 𝓞 K) : K) = star (y : K) := by
  have h := congrArg (fun u : 𝓞 K => (u : K)) ((Formalism.DivisionValues.cO K).apply_symm_apply y)
  simp only [coe_cO] at h
  rw [← h, star_star]

theorem over_conjPl {D D' : D7} {P : HeightOneSpectrum (𝓞 D.what₂.LL)} {P' : HeightOneSpectrum (𝓞 D'.what₂.LL)}
    (h : ∀ (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL), D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL) →
      (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) (x : 𝓞 D.what₂.LL) (x' : 𝓞 D'.what₂.LL)
    (hx : D.what₂.embLL (x : D.what₂.LL) = D'.what₂.embLL (x' : D'.what₂.LL)) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x' ∈ (Formalism.DivisionValues.conjPl P').asIdeal := by
  rw [mem_conjPl_iff, mem_conjPl_iff]
  apply h
  rw [coe_cO_symm, coe_cO_symm, D.starLL_cx, D'.starLL_cx, hx]

theorem mem_zeroContentPlaces_iff_over_of_nonvanishing {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (hm : X.toD7.R.m = X'.toD7.R.m)
    (hN : ∀ (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m), (j : ℕ) = j' →
      ∀ (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL)),
        (∀ (x : 𝓞 X.toD7.what₂.LL) (x' : 𝓞 X'.toD7.what₂.LL),
          X.toD7.what₂.embLL (x : X.toD7.what₂.LL) = X'.toD7.what₂.embLL (x' : X'.toD7.what₂.LL) → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
        (NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P'))
    (v : X.B.places.Pl) (v' : X'.B.places.Pl) (hB : Below X.toD7 X'.toD7 v v') :
    v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 (fun _ _ => 0) := by
  have hB' := over_conjPl (D := X.toD7) (D' := X'.toD7) hB
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, hm ▸ j.2⟩, ?_⟩
    exact hj.imp (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB).1 h) (fun h => (hN j ⟨j, hm ▸ j.2⟩ rfl _ _ hB').1 h)
  · rintro ⟨j', hj⟩
    refine ⟨⟨j', hm.symm ▸ j'.2⟩, ?_⟩
    exact hj.imp (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB).2 h) (fun h => (hN ⟨j', hm.symm ▸ j'.2⟩ j' rfl _ _ hB').2 h)

theorem nzAt_iff_of {X X' : Stages} {px : PreX X.B.toPre} {px' : PreX X'.B.toPre} {I : ColIn X.B px} {I' : ColIn X'.B px'}
    {hX : X.B.fields.Ok} {hX' : X'.B.fields.Ok} {T : TwDat X.B} {T' : TwDat X'.B} {Wt : Set X.B.places.Pl}
    {Wt' : Set X'.B.places.Pl} (z : Dat X I hX T Wt) (z' : Dat X' I' hX' T' Wt') (j : Fin X.toD7.R.m) (j' : Fin X'.toD7.R.m)
    (P : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) (P' : HeightOneSpectrum (𝓞 X'.toD7.what₂.LL))
    (hI : (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 P ≠ 0 ↔
      (s0Of z'.R z'.F).Iw j' (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0 P' ≠ 0)
    (hJ : Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) P
          (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
          (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ↔
      Formalism.DivisionValues.jw (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).HT j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) P'
                (((famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j'
                (famR X' I' hX' (usedOf I' T' Wt') z'.Xg z'.tr).A.μ0) ≠ 0) :
    NzAt z.R z.F (fun _ _ => 0) j P ↔ NzAt z'.R z'.F (fun _ _ => 0) j' P' := by
  unfold NzAt
  exact or_congr hI (or_congr hJ Iff.rfl)

end GlobalTheory.Mem.R3.TwistedPlaceExtensions

end
