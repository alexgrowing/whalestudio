import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntSmulMem
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IsoCount

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem isTraceDef_of_pd (H : HermSpace K V) (hp : GlobalTheory.Mass.PD H.B.flip) : IsTraceDef H := by
  intro x hx
  have h1 := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := H.B x x)
  have h2 : (0 : ℝ) < (algebraMap ℚ ℂ (Algebra.trace ℚ K (H.B x x))).re := by
    have : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
    rw [h1, Complex.re_sum]
    exact Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) Finset.univ_nonempty
  have h3 : (algebraMap ℚ ℂ (Algebra.trace ℚ K (H.B x x))).re = ((Algebra.trace ℚ K (H.B x x) : ℚ) : ℝ) := by
    simp
  rw [h3] at h2
  exact_mod_cast h2

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def fixAut (H : HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {η | η ∈ isomGrp H ∧ imLat η L = L ∧ ∀ y ∈ U, η y = y}
  one_mem' := ⟨(isomGrp H).one_mem, Formalism.HermitianLatticesTheory.genusBasic_gmap_one L, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, haL, haU⟩ ⟨hb, hbL, hbU⟩
    refine ⟨mul_mem ha hb, ?_, fun y hy => ?_⟩
    · unfold imLat at *
      rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, hbL, haL]
    · show a (b y) = y
      rw [hbU y hy, haU y hy]
  inv_mem' := by
    rintro a ⟨ha, haL, haU⟩
    refine ⟨inv_mem ha, ?_, fun y hy => ?_⟩
    · unfold imLat at *
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv a L
      rwa [haL] at this
    · show a.symm y = y
      rw [LinearEquiv.symm_apply_eq, haU y hy]

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem map_eq_of_fix {U : Submodule K V} {g : V ≃ₗ[K] V} (h : ∀ y ∈ U, g y = y) :
    U.map (g : V →ₗ[K] V) = U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : (g : V →ₗ[K] V) x = x := h x hx
    rw [this]; exact hx
  · intro hy
    exact ⟨y, hy, h y hy⟩

def toQuot (H : HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) :
    fixAut H U L →* ((V ⧸ U) ≃ₗ[K] (V ⧸ U)) :=
  MonoidHom.mk' (fun g => Submodule.Quotient.equiv U U g.1 (map_eq_of_fix g.2.2.2)) (by
    intro a b
    ext x
    induction x using Submodule.Quotient.induction_on
    rfl)

theorem toQuot_mk (H : HermSpace K V) (U : Submodule K V) (L : Submodule (𝓞 K) V) (g : fixAut H U L)
    (x : V) : toQuot H U L g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g.1 x) := rfl

theorem toQuot_injective {H : HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    (L : Submodule (𝓞 K) V) : Function.Injective (toQuot H U L) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  ext x
  have h1 : Submodule.Quotient.mk (p := U) (g.1 x) = Submodule.Quotient.mk x := by
    rw [← toQuot_mk, hg]; rfl
  have hu : g.1 x - x ∈ U := (Submodule.Quotient.eq U).1 h1
  have h2 := (mem_isomGrp H g.1).1 g.2.1 x (g.1 x - x)
  rw [g.2.2.2 _ hu] at h2
  have h3 : H.B (g.1 x - x) (g.1 x - x) = 0 := by
    rw [map_sub H.B, LinearMap.sub_apply, h2, sub_self]
  by_contra hne
  have h4 := hH (g.1 x - x) (sub_ne_zero.2 hne)
  rw [h3, map_zero] at h4
  exact lt_irrefl _ h4

variable [FiniteDimensional K V]

theorem fixAut_finite {H : HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) : (fixAut H U L : Set (V ≃ₗ[K] V)).Finite :=
  (autCard_eq_natCard hH hL).1.subset fun _ hg => ⟨hg.1, hg.2.1⟩

theorem card_fixAut_dvd (hM : MinkowskiBound) {H : HermSpace K V} (hH : IsTraceDef H) (U : Submodule K V)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    Nat.card (fixAut H U L) ∣ minkowskiM (Module.finrank ℚ K * Module.finrank K (V ⧸ U)) := by
  have hfin : Finite (fixAut H U L) := (fixAut_finite hH U hL).to_subtype
  have e := MonoidHom.ofInjective (toQuot_injective hH U L)
  rw [Nat.card_congr e.toEquiv]
  refine GlobalTheory.AutLattice.card_dvd_minkM hM K (V ⧸ U) (L.map (U.mkQ.restrictScalars (𝓞 K)))
    (hL.fg.map _) ?_ _ (Finite.of_equiv _ e.toEquiv) ?_
  · have : ((L.map (U.mkQ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) (V ⧸ U)) : Set (V ⧸ U))
        = U.mkQ '' (L : Set V) := rfl
    rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  · rintro _ ⟨g, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨g.1 x, ?_, rfl⟩
    have h := g.2.2.1
    have h' : g.1 x ∈ imLat g.1 L := ⟨x, hx, rfl⟩
    rwa [h] at h'

end

theorem isoCnt : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (U : Submodule K V) (L L' : Submodule (𝓞 K) V), Submodule.IsLattice K L → Submodule.IsLattice K L' → ((({η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y}).encard : ℕ∞) : ℝ≥0∞) ≤ ((4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * ((Module.finrank K V) - Module.finrank K U) * (Formalism.HermitianLatticesTheory.fDeg K)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hp U L L' hL _
  have hH := isTraceDef_of_pd H hp
  set S := {η : V ≃ₗ[K] V | η ∈ isomGrp H ∧ imLat η L = L' ∧ ∀ y ∈ U, η y = y} with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨η, hη, hηL, hηU⟩
  · rw [h0]; simp
  have h1 : S.encard ≤ (fixAut H U L : Set (V ≃ₗ[K] V)).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun a => η⁻¹ * a) ?_ ?_
    · rintro a ⟨ha, haL, haU⟩
      refine ⟨mul_mem (inv_mem hη) ha, ?_, fun y hy => ?_⟩
      · unfold imLat at *
        rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, haL, ← hηL, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv]
      · show η.symm (a y) = y
        rw [LinearEquiv.symm_apply_eq, haU y hy, hηU y hy]
    · intro a _ b _ hab
      simpa using hab
  have hn : Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
    have := hK.1
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h2
    rw [Formalism.HermitianLatticesTheory.fDeg, h2, IsTotallyComplex.finrank]
  have hq : Module.finrank K (V ⧸ U) = Module.finrank K V - Module.finrank K U := by
    have := U.finrank_quotient_add_finrank
    omega
  have h2 := (card_fixAut_dvd hM hH U hL).trans (Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial _)
  have h3 := (Nat.le_of_dvd (Nat.factorial_pos _) h2).trans (Nat.factorial_le_pow _)
  have e : 2 * (Module.finrank ℚ K * Module.finrank K (V ⧸ U))
      = 4 * (Module.finrank K V - Module.finrank K U) * Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hn, hq]; ring
  rw [e] at h3
  have h4 : (fixAut H U L : Set (V ≃ₗ[K] V)).encard = (Nat.card (fixAut H U L) : ℕ∞) := by
    rw [← (fixAut_finite hH U hL).cast_ncard_eq, ← Nat.card_coe_set_eq]
    rfl
  rw [h4] at h1
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe]
  exact_mod_cast h3

end GlobalTheory.IsoCount
