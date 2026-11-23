import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.WtRat

theorem ev_spMap_top {R F : Type} [CommRing R] [CommRing F] (e : R →+* F)
    (h : ⊤ ≤ spMap e ⁻¹ᵁ ⊤) (u : Γ(Sp R, ⊤)) :
    ev (spMap e) ⊤ h u = e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u) :=
  (ev_top (spMap e) h u).trans
    (congrArg (fun q => CommRingCat.Hom.hom q u)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom e)))

theorem exists_frac_ev (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W))
    (x : PrimeSpectrum R) (hx : x ∈ W) :
    ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W),
      WtRat.ev (spMap e) W h s * e β = e α := by
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  obtain ⟨f, hfW, hxf⟩ := hT.exists_basicOpen_le (V := W) ⟨x, hx⟩ trivial
  have hb : (Sp R).basicOpen f =
      PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom f) :=
    basicOpen_eq_of_affine' f
  haveI := hT.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f)
    (((Sp R).presheaf.map (homOfLE hfW).op).hom s)
  set φ : Γ(Sp R, ⊤) →+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom with hφ
  refine ⟨φ a * φ f, φ f ^ (n + 1), ?_, ?_⟩
  · intro hm
    rw [hb] at hxf
    exact hxf (x.isPrime.mem_of_pow_mem _ hm)
  · intro F _ e h
    by_cases h0 : e (φ f) = 0
    · simp [h0]
    have hD : ⊤ ≤ spMap e ⁻¹ᵁ (Sp R).basicOpen f := by
      intro y _
      rw [hb]
      change e (φ f) ∉ y.asIdeal
      intro hy
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (Ne.isUnit h0))
    have key := congrArg (ev (spMap e) _ hD) ha
    rw [map_mul, ev_res (spMap e) hfW hD h s] at key
    have hv : ∀ u : Γ(Sp R, ⊤),
        ev (spMap e) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen f) u) = e (φ u) :=
      fun u => (ev_res (spMap e) ((Sp R).basicOpen_le f) hD le_top u).trans
        (ev_spMap_top e le_top u)
    rw [hv, hv] at key
    simp only [map_pow] at key
    rw [map_pow, map_mul, pow_succ, ← _root_.mul_assoc, key]

end GlobalTheory.SS.WtRat
