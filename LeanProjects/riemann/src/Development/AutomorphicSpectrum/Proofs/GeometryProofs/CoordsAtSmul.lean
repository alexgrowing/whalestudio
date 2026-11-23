import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_spec {a : Ω} {r : R} (h : ValAt ξ z a r) : ∃ hz : genPt ξ ⤳ centre z, a ∈ regAt ξ ⟨centre z, hz⟩ := by
  obtain ⟨hz, s, hs, -⟩ := h
  exact ⟨hz, s, hs⟩

theorem val_exists {a : Ω} {hz : genPt ξ ⤳ centre z} (h : a ∈ regAt ξ ⟨centre z, hz⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hz, s, hs, rfl⟩

theorem val_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, hs, rfl⟩ := h
  obtain ⟨hz', s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, hz⟩ (hs.trans hs'.symm)
  rw [this]

theorem val_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t * t', by rw [map_mul, ht]; rw [← ht'], map_mul _ _ _⟩

theorem val_add {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t + t', by rw [map_add, ht]; rw [← ht'], map_add _ _ _⟩

theorem val_nat (hz : genPt ξ ⤳ centre z) (n : ℕ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩

theorem val_one (hz : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 1

theorem val_zero (hz : genPt ξ ⤳ centre z) : ValAt ξ z (0 : Ω) (0 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 0

theorem val_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : ValAt ξ z a⁻¹ (↑r⁻¹ : R) := by
  obtain ⟨hz, s, hs, hr⟩ := h
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (hr ▸ r.isUnit)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · rw [← hs, map_units_inv]
  · have : (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom u) = r := Units.ext hr
    rw [← this]
    exact congrArg Units.val (map_inv (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom) u)

theorem val_ne_zero (hξ : IsCptGen ξ) [Nontrivial R] {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hz, -⟩ := val_spec h
  have := val_unique hξ h (val_zero hz)
  exact r.ne_zero this

theorem val_inv₀ {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) :
    ValAt ξ z a⁻¹ r⁻¹ := by
  have := val_inv (r := Units.mk0 r hr) h
  simpa using this

theorem val_zpow {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, -⟩ := val_spec h
  have hp : ∀ k : ℕ, ∀ {b : Ω} {s : F}, ValAt ξ z b s → ValAt ξ z (b ^ k) (s ^ k) := by
    intro k b s hb
    induction k with
    | zero => simpa using val_one hz
    | succ k ih => rw [pow_succ, pow_succ]; exact val_mul ih hb
  rcases n with k | k
  · simpa using hp k h
  · simpa [zpow_negSucc] using val_inv₀ (pow_ne_zero _ hr) (hp (k + 1) h)

theorem in_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  have h1 := fun k => hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (h1 k).1, fun c' => ?_⟩
  simp only
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (h1 k).2 (c' k)
  obtain ⟨hz', s, hs, -⟩ := hr
  exact ⟨s, hs⟩

theorem coordsAt_smul {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (hw : CoordsAt ξ y z w) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k c' hu => ?_⟩
  · obtain ⟨c', h'⟩ := hw.1 k
    exact ⟨c', (isUnit_iff_ne_zero.2 (hc k)).mul h'⟩
  · have hu' : IsUnit (w ⟨k, c'⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hu.ne_zero)
    obtain ⟨h1, h2⟩ := hw.2 k c' hu'
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨r, hr, hr'⟩ := h2 i
    refine ⟨r, hr, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, c'⟩)
    rw [hr']; ring

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
