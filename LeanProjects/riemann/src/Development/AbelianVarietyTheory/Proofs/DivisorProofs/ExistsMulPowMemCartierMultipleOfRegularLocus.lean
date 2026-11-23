import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem regAt_pow_of_regAt {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {u : Y.functionField} (h : RegAt y u) (n : ℕ) :
    RegAt y (u ^ n) :=
  have ⟨a, ha⟩ := h; ⟨a ^ n, by rw [map_pow, ha]⟩

theorem exists_regAt_mul_pow_affine {Y : Scheme.{0}} [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (hg : genericPoint Y ∈ U) {u g : Y.functionField} (hu0 : u ≠ 0) (hu : ∀ y ∈ U, RegAt y u)
    (h : ∀ y ∈ U, UnitAt y u → RegAt y g) : ∃ n : ℕ, ∀ y ∈ U, RegAt y (g * u ^ n) := by
  obtain ⟨f, rfl⟩ := exists_fnOf_eq hg hu
  have hb : genericPoint Y ∈ Y.basicOpen f := (unitAt_fnOf_iff hg hg f).1 (unitAt_genericPoint hu0)
  obtain ⟨b, rfl⟩ := exists_fnOf_eq hb fun y hy =>
    h y (Y.basicOpen_le f hy) ((unitAt_fnOf_iff (Y.basicOpen_le f hy) hg f).2 hy)
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) b
  refine ⟨n, fun y hy => ?_⟩
  have e' := congrArg (fnOf _ hb) e
  have r (c : Γ(Y, U)) : fnOf _ hb (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) c) = fnOf U hg c :=
    fnOf_resG (Y.basicOpen_le f) hb c
  simp only [map_mul, r] at e'
  rw [map_pow] at e'
  rw [e']
  exact regAt_fnOf hy hg a

theorem exists_mul_pow_mem_sec (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] (D : CartierDiv Y) (k : ℕ)
    (s : Y.functionField) (hs : s ∈ Sec D k) (g : Y.functionField) (hg : ∀ y ∈ locus D k s, RegAt y g) :
    ∃ n : ℕ, g * s ^ n ∈ Sec D (k * n) := by
  by_cases hs0 : s = 0
  · refine ⟨1, fun x => ?_⟩
    rw [hs0, pow_one, mul_zero]
    exact (CartierDiv.vanishesAt_zero _ x).regularAt
  have key (x : Y) : ∃ U : Y.Opens, x ∈ U ∧ ∃ n : ℕ, ∀ m, n ≤ m → ∀ y ∈ U,
      ((k * m) • D).RegularAt y (g * s ^ m) := by
    obtain ⟨V, hV, e, he⟩ := (k • D).exists_isEqn_nhds x
    obtain ⟨U, hU, hx, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
    have hu (y) (hy : y ∈ U) : RegAt y (s * e) := (he y (hUV hy)).regularAt_iff.1 (hs y)
    obtain ⟨n, hn⟩ := exists_regAt_mul_pow_affine (g := g) hU (gen_mem hx) (mul_ne_zero hs0 e.ne_zero) hu
      fun y hy h => hg y ⟨e, he y (hUV hy), h⟩
    refine ⟨U, hx, n, fun m hm y hy => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [mul_nsmul]
    refine ⟨_, (he y (hUV hy)).nsmul _, ?_⟩
    have := (hn y hy).mul (regAt_pow_of_regAt (hu y hy) d)
    rwa [_root_.mul_assoc, ← pow_add, mul_pow, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val] at this
  choose U hU n hn using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set Y)) (fun x => (U x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩
  refine ⟨t.sup n, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact hn x _ (Finset.le_sup hx) y hy

end GlobalTheory.Desc
