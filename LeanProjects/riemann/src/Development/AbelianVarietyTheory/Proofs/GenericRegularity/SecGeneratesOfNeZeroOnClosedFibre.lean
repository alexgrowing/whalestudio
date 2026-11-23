import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace SecLineGen

theorem constFn_mul' {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V) (U : X.Opens)
    (a b : V) : constFn π U (a * b) = constFn π U a * constFn π U b := by
  first
  | exact map_mul _ a b
  | (unfold constFn; exact map_mul _ a b)
  | (simp only [constFn, map_mul])
  | (unfold constFn; simp)
  | (unfold constFn Sp; done)

theorem apply_mem_basicOpen_of_mem {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V)
    (U : X.Opens) (a : V) (g : X) (hg : g ∈ X.basicOpen (constFn π U a)) :
    π g ∈ PrimeSpectrum.basicOpen a := by
  unfold constFn at hg
  have h0 := Scheme.basicOpen_appLE π U ⊤ (fun _ _ => trivial)
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a)
  have hg' : g ∈ U ⊓ π ⁻¹ᵁ ((Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a)) := by
    rw [← h0]
    exact hg
  have h2 : π g ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a) := hg'.2
  have h3 := AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of V) a
  first
  | (rw [h3] at h2; exact h2)
  | (unfold Sp at h2; rw [h3] at h2; exact h2)
  | exact h3 ▸ h2
  | (unfold Sp at h2; done)

end SecLineGen

open SecLineGen in

theorem sec_generates_of_ne_zero_on_closed_fibre :
    ∀ (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (π : X ⟶ Sp V) (L : LB X) (θ θ' : LB.Sec L), (∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn π _ a * θ.f i) → (∃ (g : X) (i : L.ι), π g = IsLocalRing.closedPoint V ∧ g ∈ X.basicOpen (θ'.f i)) → (∃ u : Vˣ, ∀ i, θ'.f i = constFn π _ (u : V) * θ.f i) ∧ ∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn π _ a * θ'.f i := by
  intro V _ _ X π L θ θ' hθ hpt
  obtain ⟨g, i, hgc, hgi⟩ := hpt
  obtain ⟨a, ha, -⟩ := hθ θ'

  have hmem : g ∈ X.basicOpen (constFn π (L.U i) a) := by
    have h := hgi
    rw [ha i, Scheme.basicOpen_mul] at h
    exact h.1

  have hu : IsUnit a := by
    by_contra hna
    have h1 := SecLineGen.apply_mem_basicOpen_of_mem π _ a g hmem
    rw [hgc] at h1
    have h2 : a ∉ (IsLocalRing.closedPoint V).asIdeal := (PrimeSpectrum.mem_basicOpen _ _).1 h1
    have hmax : a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).2 hna
    first | exact h2 hmax | exact h2 (by simpa using hmax)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨⟨u, fun j => ha j⟩, ?_⟩
  intro σ
  obtain ⟨b, hb, hbu⟩ := hθ σ
  refine ⟨b * ↑u⁻¹, ?_, ?_⟩
  · intro j
    rw [hb j, ha j, ← _root_.mul_assoc, ← SecLineGen.constFn_mul', _root_.mul_assoc b, Units.inv_mul, _root_.mul_one]
  · intro c hc
    have key : c * ↑u = b := hbu (c * ↑u) (fun j => by
      rw [hc j, ha j, ← _root_.mul_assoc, ← SecLineGen.constFn_mul'])
    rw [← key, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

end GlobalTheory
