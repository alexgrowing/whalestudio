import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.chainRing_of :
    ChainLoc → ChainRing := by
  intro hC κ B B' Λ _ _ _ _ _ _ _ _ _ π ε' _ q hπ hq hex εΛ g hg
  obtain ⟨t, ht, htm⟩ := hex
  set m : Ideal B := RingHom.ker (ε'.comp π).toRingHom with hm
  set m' : Ideal B' := RingHom.ker ε'.toRingHom with hm'
  haveI : m.IsPrime := RingHom.ker_isPrime _
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : Module.Finite κ B' := Module.Finite.of_surjective π.toLinearMap hπ
  haveI : IsArtinianRing B' := IsArtinianRing.of_finite κ B'
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime m)) :=
    IsArtinianRing.localization_surjective m.primeCompl _
  have hsurj' : Function.Surjective (algebraMap B' (Localization.AtPrime m')) :=
    IsArtinianRing.localization_surjective m'.primeCompl _
  haveI : Module.Finite κ (Localization.AtPrime m) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom κ B (Localization.AtPrime m)).toLinearMap hsurj
  haveI : IsArtinianRing (Localization.AtPrime m) := IsArtinianRing.of_finite κ _
  have hmem : ∀ x, x ∈ m ↔ ε' (π x) = 0 := fun x => by simp [m, RingHom.mem_ker]
  have hmem' : ∀ y, y ∈ m' ↔ ε' y = 0 := fun y => by simp [m', RingHom.mem_ker]
  have hunit : ∀ s, ε' (π s) ≠ 0 → IsUnit (g s) := by
    intro s hs
    by_contra hns
    have hker : (RingHom.ker εΛ.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨algebraMap κ Λ c, by simp⟩)
    have heq : RingHom.ker εΛ.toRingHom = IsLocalRing.maximalIdeal Λ := IsLocalRing.eq_maximalIdeal hker
    have hin : g s ∈ RingHom.ker εΛ.toRingHom := by
      rw [heq]
      exact (IsLocalRing.mem_maximalIdeal _).2 hns
    have h2 : εΛ (g s) = ε' (π s) := by
      simpa using congrArg (fun f : B →ₐ[κ] κ => f s) hg
    apply hs
    rw [← h2]
    simpa [RingHom.mem_ker] using hin
  have hφu : ∀ y : m.primeCompl,
      IsUnit (((IsScalarTower.toAlgHom κ B' (Localization.AtPrime m')).comp π) y) := by
    rintro ⟨y, hy⟩
    have hy' : π y ∈ m'.primeCompl := by
      show π y ∉ m'
      rw [hmem']
      exact fun h => hy ((hmem y).2 h)
    exact IsLocalization.map_units (Localization.AtPrime m') (⟨π y, hy'⟩ : m'.primeCompl)
  let φ : Localization.AtPrime m →ₐ[κ] Localization.AtPrime m' := IsLocalization.liftAlgHom hφu
  have hφ : ∀ x, φ (algebraMap B _ x) = algebraMap B' (Localization.AtPrime m') (π x) := fun x => by
    simp [φ, IsLocalization.lift_eq]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := hsurj' z
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨_, hφ x⟩
  have hεu : ∀ y : m.primeCompl, IsUnit ((ε'.comp π) y) := by
    rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.2 (fun h => hy ((hmem y).2 h))
  let ε : Localization.AtPrime m →ₐ[κ] κ := IsLocalization.liftAlgHom hεu
  have hmapm : m.map (algebraMap B (Localization.AtPrime m)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := Localization.AtPrime.map_eq_maximalIdeal
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime m) =
      Ideal.span {algebraMap B (Localization.AtPrime m) t} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal (Localization.AtPrime m))
        (IsNoetherian.noetherian _)
      · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      · rw [Ideal.smul_eq_mul, ← hmapm]
        calc m.map (algebraMap B (Localization.AtPrime m))
            ≤ (Ideal.span {t} ⊔ m ^ 2).map (algebraMap B (Localization.AtPrime m)) := Ideal.map_mono htm
          _ = _ := by rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.image_singleton, sq]
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← hmapm]
      exact Ideal.mem_map_of_mem _ ht
  have hJ : RingHom.ker φ = Ideal.span {(algebraMap B (Localization.AtPrime m) t) ^ q} := by
    apply hC κ (Localization.AtPrime m) ε (algebraMap B _ t) hmax (RingHom.ker φ) q
    rw [← hq]
    exact LinearEquiv.finrank_eq (Ideal.quotientKerAlgEquivOfSurjective hφs).toLinearEquiv
  have hfac : ∀ x y : B, algebraMap B (Localization.AtPrime m) x = algebraMap B _ y → g x = g y := by
    intro x y h
    rw [← sub_eq_zero, ← map_sub] at h
    obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) (x - y)).1 h
    have hu' : ε' (π u) ≠ 0 := fun h0 => hu ((hmem u).2 h0)
    have h1 := congrArg g hu0
    rw [map_mul, map_sub, map_zero] at h1
    exact sub_eq_zero.1 ((hunit u hu').mul_right_eq_zero.1 h1)
  constructor
  · intro hker x hx
    have ht1 : (algebraMap B (Localization.AtPrime m) t) ^ q ∈ RingHom.ker φ := by
      rw [hJ]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker, ← map_pow, hφ, map_pow] at ht1
    rw [← map_pow] at ht1
    obtain ⟨⟨u', hu'⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff m'.primeCompl (Localization.AtPrime m') _).1 ht1
    obtain ⟨v, rfl⟩ := hπ u'
    have hv : ε' (π v) ≠ 0 := fun h0 => hu' ((hmem' _).2 h0)
    have h1 : g (v * t ^ q) = 0 := hker _ (by rw [map_mul]; exact hu0)
    rw [map_mul, map_pow] at h1
    have hgt : g t ^ q = 0 := (hunit v hv).mul_right_eq_zero.1 h1
    have hx' : algebraMap B (Localization.AtPrime m) x ∈ Ideal.span {algebraMap B (Localization.AtPrime m) t} := by
      rw [← hmax, ← hmapm]
      exact Ideal.mem_map_of_mem _ ((hmem x).2 hx)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx'
    obtain ⟨y, rfl⟩ := hsurj z
    have he := hfac x (y * t) (by rw [map_mul, hz])
    rw [he, map_mul, mul_pow, hgt, mul_zero]
  · intro hq' x hx
    have hgt : g t ^ q = 0 := hq' t ((hmem t).1 ht)
    have hx' : algebraMap B (Localization.AtPrime m) x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, hφ, hx, map_zero]
    rw [hJ] at hx'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx'
    obtain ⟨y, rfl⟩ := hsurj z
    have he := hfac x (y * t ^ q) (by rw [map_mul, map_pow, hz])
    rw [he, map_mul, map_pow, hgt, mul_zero]
