import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open Polynomial

private theorem zpMap_map_aeval {R' R : Type} [CommRing R'] [CommRing R] (π : R' →+* R)
    (f : ℤ[X]) (x : R') : π (Polynomial.aeval x f) = Polynomial.aeval (π x) f :=
  (Polynomial.aeval_algHom_apply π.toIntAlgHom x f).symm

private theorem zpMap_general {B R : Type} [CommRing B] [CommRing R]
    (f : ℤ[X]) (ζ : B) (S : Submonoid ℕ) (h0 : Polynomial.aeval ζ f = 0)
    (hinj : ∀ g : ℤ[X], Polynomial.aeval ζ g = 0 → f ∣ g)
    (hS : ∀ n ∈ S, IsUnit (n : B))
    (hsurj : ∀ b : B, ∃ n ∈ S, ∃ g : ℤ[X], b * (n : B) = Polynomial.aeval ζ g)
    (hS' : ∀ n ∈ S, IsUnit (n : R)) (z : R) (hz : Polynomial.aeval z f = 0) :
    ∃ β : B →+* R, β ζ = z := by
  let φ : AdjoinRoot f →+* B := AdjoinRoot.lift (algebraMap ℤ B) ζ h0
  let α : AdjoinRoot f →+* R := AdjoinRoot.lift (algebraMap ℤ R) z hz
  have hφ : ∀ g : ℤ[X], φ (AdjoinRoot.mk f g) = Polynomial.aeval ζ g := fun g =>
    AdjoinRoot.lift_mk _ _
  have hα : ∀ g : ℤ[X], α (AdjoinRoot.mk f g) = Polynomial.aeval z g := fun g =>
    AdjoinRoot.lift_mk _ _
  letI : Algebra (AdjoinRoot f) B := φ.toAlgebra
  have halg : algebraMap (AdjoinRoot f) B = φ := rfl
  let S' : Submonoid (AdjoinRoot f) := S.map (Nat.castRingHom (AdjoinRoot f))
  haveI : IsLocalization S' B := by
    refine (isLocalization_iff _ _).mpr ⟨?_, fun b => ?_, fun {a c} h => ⟨1, ?_⟩⟩
    · rintro ⟨_, n, hn, rfl⟩
      simpa using hS n hn
    · obtain ⟨n, hn, g, hg⟩ := hsurj b
      refine ⟨(AdjoinRoot.mk f g, ⟨_, n, hn, rfl⟩), ?_⟩
      simp only [halg, hφ]
      simpa using hg
    · obtain ⟨a, rfl⟩ := AdjoinRoot.mk_surjective a
      obtain ⟨c, rfl⟩ := AdjoinRoot.mk_surjective c
      rw [halg, hφ, hφ, ← sub_eq_zero, ← map_sub] at h
      rw [AdjoinRoot.mk_eq_mk.mpr (hinj _ h)]
  have hu : ∀ y : S', IsUnit (α y) := by
    rintro ⟨_, n, hn, rfl⟩
    simpa using hS' n hn
  refine ⟨IsLocalization.lift hu, ?_⟩
  have h1 : ζ = algebraMap (AdjoinRoot f) B (AdjoinRoot.mk f Polynomial.X) := by
    rw [halg, hφ, Polynomial.aeval_X]
  rw [h1, IsLocalization.lift_eq, hα, Polynomial.aeval_X]

private def zpMap_S (p : ℕ) : Submonoid ℕ where
  carrier := {n | n ≠ 0 ∧ n.Coprime p}
  mul_mem' := fun ha hb => ⟨mul_ne_zero ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨one_ne_zero, Nat.coprime_one_left p⟩

private theorem zpMap_isUnit (p M n : ℕ) (hn : n ∈ zpMap_S p) : IsUnit (n : Geo.Tor.ZP p M) := by
  have hmem : (n : ℂ)⁻¹ ∈ Geo.Tor.ZP p M := Subring.subset_closure (Or.inr ⟨n, hn.2, rfl⟩)
  refine IsUnit.of_mul_eq_one (⟨_, hmem⟩ : Geo.Tor.ZP p M) (Subtype.ext ?_)
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.1
  simp [this]

private theorem zpMap_surj (p M : ℕ) (x : ℂ) (hx : x ∈ Geo.Tor.ZP p M) :
    ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      x * (n : ℂ) = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with hx | ⟨n, hn, rfl⟩
    · exact ⟨1, one_mem _, Polynomial.X, by simpa [Geo.Tor.zetaZP] using hx⟩
    · by_cases h : n = 0
      · exact ⟨1, one_mem _, 0, by simp [h]⟩
      · have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
        exact ⟨n, ⟨h, hn⟩, 1, by simp [this]⟩
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | one => exact ⟨1, one_mem _, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * (m : ℤ[X]) + k * (n : ℤ[X]), ?_⟩
    simp only [map_add, map_mul, map_natCast, Nat.cast_mul, ← hg, ← hk]
    ring
  | neg x _ hx =>
    obtain ⟨n, hn, g, hg⟩ := hx
    exact ⟨n, hn, -g, by rw [map_neg, ← hg, neg_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, g, hg⟩ := hx
    obtain ⟨m, hm, k, hk⟩ := hy
    refine ⟨n * m, mul_mem hn hm, g * k, ?_⟩
    simp only [map_mul, Nat.cast_mul, ← hg, ← hk]
    ring

private theorem zpMap_unit (p : ℕ) (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (hn : n.Coprime p) : IsUnit (n : O) := by
  have hp : (p : O) ∈ Ideal.jacobson (⊥ : Ideal O) :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {(p : O)}) (Ideal.subset_span rfl)
  have hc : IsCoprime (n : O) (p : O) := Nat.Coprime.cast hn
  obtain ⟨a, b, hab⟩ := hc
  have hu := Ideal.mem_jacobson_bot.mp hp (-b)
  have : (p : O) * -b + 1 = a * n := by rw [← hab]; ring
  rw [this] at hu
  exact isUnit_of_mul_isUnit_right hu

private theorem zpMap_main (p : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ) (hM : M ≠ 0) (hMp : M.Coprime p) :
    ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧
      ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  have hpos : 0 < M := Nat.pos_of_ne_zero hM
  haveI : NeZero M := ⟨hM⟩
  have hprim : IsPrimitiveRoot ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) M :=
    Complex.isPrimitiveRoot_exp M hM
  have hmin := cyclotomic_eq_minpoly hprim hpos
  have hcoe : ∀ g : ℤ[X], ((Polynomial.aeval (Geo.Tor.zetaZP p M) g : Geo.Tor.ZP p M) : ℂ)
      = Polynomial.aeval ((Geo.Tor.zetaZP p M : Geo.Tor.ZP p M) : ℂ) g :=
    fun g => zpMap_map_aeval (Geo.Tor.ZP p M).subtype g _
  have h0 : Polynomial.aeval (Geo.Tor.zetaZP p M) (cyclotomic M ℤ) = 0 := by
    apply Subtype.ext
    rw [hcoe, hmin]
    exact minpoly.aeval _ _
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C M
  have hvw : v w ≤ 1 := by
    have h1 : v w ^ M = 1 := by rw [← map_pow, hw.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hM).mp h1).le
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvw
  have hminw := cyclotomic_eq_minpoly hw hpos
  have hz : Polynomial.aeval z (cyclotomic M ℤ) = 0 := by
    apply hv.hom_inj
    rw [zpMap_map_aeval, map_zero, hminw]
    exact minpoly.aeval _ _
  have hsurj : ∀ b : Geo.Tor.ZP p M, ∃ n ∈ zpMap_S p, ∃ g : ℤ[X],
      b * (n : Geo.Tor.ZP p M) = Polynomial.aeval (Geo.Tor.zetaZP p M) g := by
    intro b
    obtain ⟨n, hn, g, hg⟩ := zpMap_surj p M b b.2
    exact ⟨n, hn, g, Subtype.ext (by rw [hcoe, ← hg]; simp)⟩
  obtain ⟨β, hβ⟩ := zpMap_general (cyclotomic M ℤ) (Geo.Tor.zetaZP p M) (zpMap_S p) h0
    (fun g hg => by
      rw [hmin]
      refine minpoly.isIntegrallyClosed_dvd (hprim.isIntegral hpos) ?_
      rw [← hcoe, hg]
      rfl)
    (zpMap_isUnit p M) hsurj (fun n hn => zpMap_unit p O n hn.2) z hz
  have hMu : IsUnit (M : O) := zpMap_unit p O M hMp
  refine ⟨β, ?_, hMu, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨n, hn, g, hg⟩ := hsurj b
    have h1 : Polynomial.aeval (algebraMap O C z) g = 0 := by
      rw [← zpMap_map_aeval, ← hβ, ← zpMap_map_aeval, ← hg, map_mul, hb, zero_mul, map_zero]
    have h2 : cyclotomic M ℤ ∣ g := by
      rw [hminw]
      exact minpoly.isIntegrallyClosed_dvd (hw.isIntegral hpos) h1
    obtain ⟨q, rfl⟩ := h2
    rw [map_mul, h0, zero_mul] at hg
    exact ((zpMap_isUnit p M n hn).mul_left_eq_zero).mp hg
  · intro k _ gk
    haveI : NeZero (M : k) := ⟨by simpa using (hMu.map gk).ne_zero⟩
    rw [← isRoot_cyclotomic_iff, hβ, IsRoot.def, ← map_cyclotomic_int, ← algebraMap_int_eq,
      eval_map_algebraMap, ← zpMap_map_aeval, hz, map_zero]

end

theorem exists_zp_ringHom_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (M : ℕ), M ≠ 0 → M.Coprime p → ∃ β : Geo.Tor.ZP p M →+* O, Function.Injective β ∧ IsUnit (M : O) ∧ ∀ (k : Type) [Field k] (gk : O →+* k), IsPrimitiveRoot (gk (β (Geo.Tor.zetaZP p M))) M := by
  intro p _ C _ _ _ v O _ _ hv _ _ M hM hMp
  exact zpMap_main p C v O hv M hM hMp

end GlobalTheory
