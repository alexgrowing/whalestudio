import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_placeOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x)]
  have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
  rw [this, ← IsScalarTower.algebraMap_apply]

end

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (hc : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal) :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  classical
  haveI := v.isMaximal
  haveI := v'.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 L ⧸ v'.asIdeal) := Fintype.ofFinite _
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal) :=
    (Ideal.quotientMap v'.asIdeal (algebraMap (𝓞 K) (𝓞 L)) hc.ge).toAlgebra
  refine ⟨Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal), ?_⟩
  simp only [normV, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank
end GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem restrictScalars_mem_Dec {A : ValuationSubring Ω} {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    (σ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hσ

theorem actsAs_restrictScalars {A : ValuationSubring Ω} {σ : G L Ω} {q f a b : ℕ} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (σ.restrictScalars K : G K Ω) (f * a) (f * b) := by
  refine ⟨restrictScalars_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [← pow_mul, ← pow_mul] at this
  exact this

theorem restrictScalars_mem_Ine_iff {A : ValuationSubring Ω} {σ : G L Ω} :
    (σ.restrictScalars K : G K Ω) ∈ Ine (F := K) A ↔ σ ∈ Ine (F := L) A := Iff.rfl

end

theorem exists_weil_restrict : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ'
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  obtain ⟨a, b, hab⟩ := (mem_Weil h').mp σ'.2
  rw [hf] at hab
  refine ⟨⟨(σ' : G L Ω).restrictScalars K, (mem_Weil h).mpr ⟨_, _, actsAs_restrictScalars hab⟩⟩, fun z => rfl, ?_⟩
  rw [deg_eq_zero_iff, deg_eq_zero_iff]
  exact restrictScalars_mem_Ine_iff
end GlobalTheory.AboveL
