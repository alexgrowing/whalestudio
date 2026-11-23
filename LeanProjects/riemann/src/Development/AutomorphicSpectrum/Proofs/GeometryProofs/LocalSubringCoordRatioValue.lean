import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemPtsOverOfMemMcPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneMemChartLatNm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ClosLoc

open GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Vals

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L}

theorem homog_const (n : ℤ) : IsMultiHomog (C n : MRing ι) 0 := by
  intro m hm k
  rw [C_apply] at hm
  have h0 : m = 0 := by simpa using support_monomial_subset hm
  simp [h0]

theorem hasVal_one : HasVal y (0 : K → ℤ) (1 : Ω) z (1 : L) := by
  refine ⟨0, 0, 1, 1, ?_, ?_, fun k => by simp, by simp, by simp, by simp⟩ <;>
  · simpa using homog_const (ι := ι) 1

theorem hasVal_mul {s s' : Ω} {w w' : L} (h : HasVal y (0 : K → ℤ) s z w)
    (h' : HasVal y (0 : K → ℤ) s' z w') : HasVal y (0 : K → ℤ) (s * s') z (w * w') := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩ := h
  obtain ⟨dg', dh', g', f', hg', hf', hd', e', hn', ev'⟩ := h'
  refine ⟨dg + dg', dh + dh', g * g', f * f', homog_mul hg hg', homog_mul hf hf', fun k => ?_, ?_, ?_, ?_⟩
  · have h1 := hd k
    have h2 := hd' k
    simp only [Pi.add_apply, Pi.zero_apply] at *
    push_cast
    omega
  · simp only [map_mul, e, e']
    ring
  · rw [map_mul]
    exact mul_ne_zero hn hn'
  · simp only [map_mul, ev, ev']
    ring

theorem hasVal_neg {s : Ω} {w : L} (h : HasVal y (0 : K → ℤ) s z w) :
    HasVal y (0 : K → ℤ) (-s) z (-w) := by
  simpa using GlobalTheory.CompanionTheory.Ar.Rec.OS.hasVal_zsmul (-1) h

theorem hasVal_inv (hz : z ∈ ptsOver L (mCoordIdeal y)) {s : Ω} {w : L} (h : HasVal y (0 : K → ℤ) s z w)
    (hw : w ≠ 0) : s ≠ 0 ∧ HasVal y (0 : K → ℤ) s⁻¹ z w⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩ := h
  have hgz : aeval z g ≠ 0 := by
    rw [ev]
    exact mul_ne_zero hw hn
  have hgy : aeval y g ≠ 0 := fun h0 => hgz (hz.2 _ (mem_of_aeval_eq_zero hg h0))
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at e
    exact hgy e
  refine ⟨hs, dh, dg, f, g, hf, hg, fun k => ?_, ?_, hgz, ?_⟩
  · have h1 := hd k
    simp only [Pi.zero_apply, add_zero] at *
    exact h1.symm
  · rw [e]
    field_simp
  · rw [ev]
    field_simp

end Vals

def valRing {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {L : Type} [Field L] (z : (Σ k, ι k) → L) : Subring Ω where
  carrier := {s | ∃ w : L, HasVal y (0 : K → ℤ) s z w}
  mul_mem' := fun ⟨w, h⟩ ⟨w', h'⟩ => ⟨w * w', hasVal_mul h h'⟩
  one_mem' := ⟨1, hasVal_one⟩
  add_mem' := fun ⟨w, h⟩ ⟨w', h'⟩ => ⟨w + w', GlobalTheory.CompanionTheory.Ar.Rec.OS.hasVal_add h h'⟩
  zero_mem' := ⟨0, GlobalTheory.CompanionTheory.Ar.Rec.OS.hasVal_zero_of (hasVal_one (y := y) (z := z))⟩
  neg_mem' := fun ⟨w, h⟩ => ⟨-w, hasVal_neg h⟩

section Ev

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L}

def evVal (hz : z ∈ ptsOver L (mCoordIdeal y)) : valRing y z →+* L where
  toFun s := Classical.choose s.2
  map_one' := GlobalTheory.CompanionTheory.Ar.Ht.Diag.hasVal_unique hz (Classical.choose_spec (valRing y z).one_mem) hasVal_one
  map_mul' s t := GlobalTheory.CompanionTheory.Ar.Ht.Diag.hasVal_unique hz (Classical.choose_spec (s * t).2)
    (hasVal_mul (Classical.choose_spec s.2) (Classical.choose_spec t.2))
  map_zero' := GlobalTheory.CompanionTheory.Ar.Ht.Diag.hasVal_unique hz (Classical.choose_spec (valRing y z).zero_mem)
    (GlobalTheory.CompanionTheory.Ar.Rec.OS.hasVal_zero_of (hasVal_one (y := y) (z := z)))
  map_add' s t := GlobalTheory.CompanionTheory.Ar.Ht.Diag.hasVal_unique hz (Classical.choose_spec (s + t).2)
    (GlobalTheory.CompanionTheory.Ar.Rec.OS.hasVal_add (Classical.choose_spec s.2) (Classical.choose_spec t.2))

theorem hasVal_evVal (hz : z ∈ ptsOver L (mCoordIdeal y)) (s : valRing y z) :
    HasVal y (0 : K → ℤ) (s : Ω) z (evVal hz s) := Classical.choose_spec s.2

instance isLocalHom_evVal (hz : z ∈ ptsOver L (mCoordIdeal y)) : IsLocalHom (evVal hz) := by
  refine ⟨fun s hs => ?_⟩
  have hw : evVal hz s ≠ 0 := hs.ne_zero
  obtain ⟨hs0, hinv⟩ := hasVal_inv hz (hasVal_evVal hz s) hw
  refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, _, hinv⟩ : valRing y z) ?_
  exact Subtype.ext (mul_inv_cancel₀ hs0)

theorem ratio_hasVal (hz : z ∈ ptsOver L (mCoordIdeal y)) (k : K) (a b : ι k) (hb : z ⟨k, b⟩ ≠ 0) :
    y ⟨k, b⟩ ≠ 0 ∧ HasVal y (0 : K → ℤ) (y ⟨k, a⟩ / y ⟨k, b⟩) z (z ⟨k, a⟩ / z ⟨k, b⟩) := by
  classical
  have hy : y ⟨k, b⟩ ≠ 0 := by
    intro h0
    have hmem : (X ⟨k, b⟩ : MRing ι) ∈ mCoordIdeal y :=
      mem_of_aeval_eq_zero (homog_X (ι := ι) ⟨k, b⟩) (by simpa using h0)
    exact hb (by simpa using hz.2 _ hmem)
  refine ⟨hy, Pi.single k 1, Pi.single k 1, X ⟨k, a⟩, X ⟨k, b⟩, homog_X (ι := ι) ⟨k, a⟩, homog_X (ι := ι) ⟨k, b⟩,
    fun j => by simp, ?_, ?_, ?_⟩
  · simp only [aeval_X]
    field_simp
  · simpa using hb
  · simp only [aeval_X]
    field_simp

theorem nat_hasVal (hz : z ∈ ptsOver L (mCoordIdeal y)) (n : ℕ) (hn : (n : L) ≠ 0) :
    (n : Ω) ≠ 0 ∧ HasVal y (0 : K → ℤ) (n : Ω)⁻¹ z (n : L)⁻¹ := by
  have h : HasVal y (0 : K → ℤ) (n : Ω) z (n : L) := by
    refine ⟨0, 0, C (n : ℤ), 1, homog_const _, by simpa using homog_const (ι := ι) 1, fun k => by simp, ?_, ?_, ?_⟩
    · simp [aeval_C]
    · simp
    · simp [aeval_C]
  exact hasVal_inv hz h hn

end Ev

theorem exists_localRing : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ (A : Subring Ω) (_ : IsLocalRing A), (∀ (k : K) (a b : J k), z ⟨k, b⟩ ≠ 0 → y ⟨k, b⟩ ≠ 0 ∧ y ⟨k, a⟩ / y ⟨k, b⟩ ∈ A) ∧ (∀ n : ℕ, (n : L) ≠ 0 → (n : Ω) ≠ 0 ∧ (n : Ω)⁻¹ ∈ A) ∧ ∀ s ∈ A, s⁻¹ ∈ A → s ≠ 0 → ∃ w : L, w ≠ 0 ∧ Small.HasVal y (0 : K → ℤ) s z w := by
  intro K _ J _ Ω _ y L _ z hz
  refine ⟨valRing y z, RingHom.domain_isLocalRing (evVal hz), fun k a b hb => ?_, fun n hn => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := ratio_hasVal hz k a b hb
    exact ⟨h1, _, h2⟩
  · obtain ⟨h1, h2⟩ := nat_hasVal hz n hn
    exact ⟨h1, _, h2⟩
  · rintro s ⟨w, hw⟩ ⟨w', hw'⟩ hs
    refine ⟨w, ?_, hw⟩
    rintro rfl
    have h1 := hasVal_mul hw hw'
    rw [mul_inv_cancel₀ hs, zero_mul] at h1
    exact zero_ne_one (GlobalTheory.CompanionTheory.Ar.Ht.Diag.hasVal_unique hz h1 hasVal_one)

end GlobalTheory.CompanionTheory.Ar.ClosLoc
