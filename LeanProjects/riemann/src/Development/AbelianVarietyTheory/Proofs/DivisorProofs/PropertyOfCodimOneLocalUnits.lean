import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.HartogsUnit

variable {A : Type} [CommRing A] [IsDomain A]

noncomputable def toFrac (p : Ideal A) [p.IsPrime] : Localization.AtPrime p →+* FractionRing A :=
  IsLocalization.lift (M := p.primeCompl) (S := Localization.AtPrime p)
    (g := algebraMap A (FractionRing A))
    (fun s => IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (p.primeCompl_le_nonZeroDivisors s.2)))

theorem toFrac_comp (p : Ideal A) [p.IsPrime] :
    (toFrac p).comp (algebraMap A (Localization.AtPrime p)) = algebraMap A (FractionRing A) :=
  IsLocalization.lift_comp _

theorem toFrac_injective (p : Ideal A) [p.IsPrime] : Function.Injective (toFrac p) := by
  rw [toFrac, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors).eq_iff,
    (IsFractionRing.injective A (FractionRing A)).eq_iff]

theorem toFrac_mem (p : Ideal A) [p.IsPrime] (w : Localization.AtPrime p) :
    ∃ s, s ∉ p ∧ s • toFrac p w ∈ (algebraMap A (FractionRing A)).range := by
  obtain ⟨⟨m, s⟩, e⟩ := IsLocalization.surj p.primeCompl w
  refine ⟨s, s.2, m, ?_⟩
  have h := congrArg (toFrac p) e
  simp only [map_mul] at h
  rw [← RingHom.comp_apply (toFrac p), ← RingHom.comp_apply (toFrac p), toFrac_comp] at h
  rw [Algebra.smul_def, mul_comm, h]

theorem exists_unit_of_local_units : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (P : ∀ (k : Type) [Field k], (A →+* k) → k → Prop) (good : Set (PrimeSpectrum A)),
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ good →
    (∀ 𝔭 : PrimeSpectrum A, (𝔭 ∈ good ∨ 𝔭.asIdeal.height = 1) → ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      ∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k), P k (φ.comp (algebraMap A _)) (φ u)) →
    (∃ (k : Type) (_ : Field k) (φ : A →+* k), Function.Injective φ ∧ ∀ v v', P k φ v → P k φ v' → v = v') →
    (∀ (k : Type) [Field k] (φ : A →+* k) (v : k),
      (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum A) ∉ good → P k φ v) →
    ∃ f : Aˣ, ∀ (k : Type) [Field k] (φ : A →+* k), P k φ (φ f) := by
  intro A _ _ _ _ P good hbot hloc ⟨k, _, φ, hinj, huniq⟩ hbad
  classical
  let K := FractionRing A
  let ψ : K →+* k := IsFractionRing.lift hinj
  have hφ : ψ.comp (algebraMap A K) = φ := RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  obtain ⟨u₀, hu₀⟩ := hloc ⟨⊥, Ideal.isPrime_bot⟩ (Or.inl hbot)
  let x : K := toFrac _ (u₀ : Localization.AtPrime (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A).asIdeal)
  let y : K := toFrac _ ((u₀⁻¹ : (Localization.AtPrime (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A).asIdeal)ˣ) :
    Localization.AtPrime (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A).asIdeal)
  have hxy : x * y = 1 := by simp only [x, y, ← map_mul, Units.mul_inv, map_one]
  have key : ∀ (𝔭 : PrimeSpectrum A) (u : (Localization.AtPrime 𝔭.asIdeal)ˣ),
      (∀ (k : Type) [Field k] (φ : Localization.AtPrime 𝔭.asIdeal →+* k),
        P k (φ.comp (algebraMap A _)) (φ u)) → toFrac 𝔭.asIdeal u = x := by
    intro 𝔭 u hu
    have h1 := hu k (ψ.comp (toFrac 𝔭.asIdeal))
    have h0 := hu₀ k (ψ.comp (toFrac _))
    rw [RingHom.comp_assoc, toFrac_comp, hφ] at h1 h0
    exact ψ.injective (huniq _ _ h1 h0)
  have hmem : ∀ z : K, (∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 →
      ∃ w, toFrac 𝔭.asIdeal w = z) → ∃ a : A, algebraMap A K a = z := by
    intro z hz
    refine RingHom.mem_range.mp ((GlobalTheory.mem_range_algebraMap_iff_forall_height_eq_one (A := A) z).mpr ?_)
    intro p _ hp
    obtain ⟨w, hw⟩ := hz ⟨p, inferInstance⟩ hp
    rw [GlobalTheory.mem_primeLocalSubalgebra_iff, ← hw]
    exact toFrac_mem p w
  have hx0 : x ≠ 0 := left_ne_zero_of_mul_eq_one hxy
  obtain ⟨a, ha⟩ := hmem x fun 𝔭 hp => by
    obtain ⟨u, hu⟩ := hloc 𝔭 (Or.inr hp)
    exact ⟨u, key 𝔭 u hu⟩
  obtain ⟨b, hb⟩ := hmem y fun 𝔭 hp => by
    obtain ⟨u, hu⟩ := hloc 𝔭 (Or.inr hp)
    refine ⟨((u⁻¹ : (Localization.AtPrime 𝔭.asIdeal)ˣ) : Localization.AtPrime 𝔭.asIdeal), ?_⟩
    apply mul_left_cancel₀ hx0
    rw [hxy, ← key 𝔭 u hu, ← map_mul, Units.mul_inv, map_one]
  have hab : a * b = 1 := IsFractionRing.injective A K (by rw [map_mul, ha, hb, hxy, map_one])
  let f : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨f, fun k' _ φ' => ?_⟩
  by_cases hg : (⟨RingHom.ker φ', RingHom.ker_isPrime φ'⟩ : PrimeSpectrum A) ∈ good
  · obtain ⟨u, hu⟩ := hloc _ (Or.inl hg)
    let φl : Localization.AtPrime (RingHom.ker φ') →+* k' :=
      IsLocalization.lift (M := (RingHom.ker φ').primeCompl) (g := φ')
        (fun s => IsUnit.mk0 _ (fun h => s.2 (RingHom.mem_ker.mpr h)))
    have hl : φl.comp (algebraMap A _) = φ' := IsLocalization.lift_comp _
    have h := hu k' φl
    rw [hl] at h
    have hu' : (u : Localization.AtPrime (RingHom.ker φ')) = algebraMap A _ (f : A) :=
      toFrac_injective _ (by rw [key _ u hu, ← RingHom.comp_apply, toFrac_comp]; exact ha.symm)
    rwa [hu', ← RingHom.comp_apply, hl] at h
  · exact hbad k' φ' _ hg

end GlobalTheory.HartogsUnit
