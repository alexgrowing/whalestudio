import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.FiniteTypeDomainExtensionPoint
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem pole_proper {A K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K]
    [IsFractionRing A K] (𝔭 : Ideal A) (h𝔭 : 𝔭 ≠ ⊤) (f : K)
    (hf : ∀ s c : A, algebraMap A K s * f = algebraMap A K c → s ∈ 𝔭) :
    𝔭.map (algebraMap A (Algebra.adjoin A {f⁻¹})) ⊔
      Ideal.span {(⟨f⁻¹, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {f⁻¹})} ≠ ⊤ := by
  intro htop
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h𝔭 ((Ideal.eq_top_iff_one _).2 (hf 1 0 (by simp)))
  letI : Invertible f⁻¹ := invertibleOfNonzero (inv_ne_zero hf0)
  obtain ⟨p, hp, hpx⟩ :=
    Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top f⁻¹ 𝔭 h𝔭 htop
  rw [invOf_eq_inv, inv_inv] at hpx
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_leadingCoeff_smul p f hpx)
  have h1 : p.leadingCoeff ∈ 𝔭 := hf _ c (by rw [hc, Algebra.smul_def])
  apply h𝔭
  rw [Ideal.eq_top_iff_one]
  simpa using 𝔭.sub_mem h1 hp

theorem UpperTheory.exists_ext_point_inv_val_lt_one_of_pole_at_prime :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] (b : 𝓞 F →+* O), IsUp v ε O b → ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra O A] [Algebra.FiniteType O A] [CharZero A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (𝔭 : Ideal A), 𝔭.IsPrime → (∀ a ∈ maximalIdeal O, algebraMap O A a ∈ 𝔭) → ∀ f : K, (∀ s c : A, algebraMap A K s * f = algebraMap A K c → s ∈ 𝔭) → ∀ g : A, g ≠ 0 → ∃ (e : TrueGeo.Ext v) (φ : A →+* e.O) (t : e.O), (∀ a : 𝓞 F, ((φ (algebraMap O A (b a)) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ φ g ≠ 0 ∧ e.w (t : AlgebraicClosure F) < 1 ∧ ∀ s c : A, algebraMap A K s * f⁻¹ = algebraMap A K c → φ s * t = φ c := by
  intro F _ _ v F' _ _ ε O _ b hup A _ _ _ _ _ _ K _ _ _ 𝔭 h𝔭 hm f hf g hg
  let R := Algebra.adjoin A ({f⁻¹} : Set K)
  let x : R := ⟨f⁻¹, Algebra.subset_adjoin rfl⟩
  letI : Algebra O R := ((algebraMap A R).comp (algebraMap O A)).toAlgebra
  haveI : IsScalarTower O A R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A R := by
    apply Subalgebra.fg_iff_finiteType _ |>.1
    exact ⟨{f⁻¹}, by simp [R]⟩
  haveI : Algebra.FiniteType O R := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have hinj : Function.Injective (algebraMap A R) := by
    intro a a' h
    exact IsFractionRing.injective A K (congrArg Subtype.val h)
  haveI : CharZero R := charZero_of_injective_algebraMap hinj
  obtain ⟨e, φ, h1, h2, h3⟩ := UpperTheory.finiteType_domain_extension_point F v F' ε O b hup R
    (𝔭.map (algebraMap A R) ⊔ Ideal.span {x}) (pole_proper 𝔭 h𝔭.ne_top f hf)
    (fun a ha => Ideal.mem_sup_left (Ideal.mem_map_of_mem (algebraMap A R) (hm a ha)))
    (algebraMap A R g) (fun h => hg (hinj (h.trans (map_zero _).symm)))
  refine ⟨e, φ.comp (algebraMap A R), φ x, h1, h3,
    h2 x (Ideal.mem_sup_right (Ideal.subset_span rfl)), fun s c hsc => ?_⟩
  have : algebraMap A R s * x = algebraMap A R c := Subtype.ext hsc
  simp only [RingHom.comp_apply]
  rw [← map_mul, this]
