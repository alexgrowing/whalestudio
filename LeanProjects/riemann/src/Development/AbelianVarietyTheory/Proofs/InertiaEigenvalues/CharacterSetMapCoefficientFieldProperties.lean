import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem mem_mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL')
    (Sig : Finset (I →* LLˣ)) (x : I →* LL'ˣ) :
    x ∈ mapSig f Sig ↔ ∃ a ∈ Sig, (Units.map (f : LL →* LL')).comp a = x := by
  classical
  unfold mapSig
  exact Finset.mem_image

theorem orbLen_map {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL')
    (I : Subgroup G) (Fr : G) (a b : I →* LLˣ) :
    Formalism.MainNotions.ElementDenominator.orbLen I Fr ((Units.map (f : LL →* LL')).comp a * ((Units.map (f : LL →* LL')).comp b)⁻¹) =
      Formalism.MainNotions.ElementDenominator.orbLen I Fr (a * b⁻¹) := by
  set φ : LLˣ →* LL'ˣ := Units.map (f : LL →* LL') with hφ
  have hinj : Function.Injective φ := by
    intro u v huv
    apply Units.ext
    have := congrArg Units.val huv
    simpa [hφ] using f.injective this
  have hcomp : φ.comp a * (φ.comp b)⁻¹ = φ.comp (a * b⁻¹) := by
    ext x
    simp
  rw [hcomp]
  unfold Formalism.MainNotions.ElementDenominator.orbLen
  congr 1
  ext k
  simp only [Set.mem_setOf_eq, MonoidHom.comp_apply]
  constructor
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => hinj (h g g' hg)⟩
  · rintro ⟨hk, h⟩
    exact ⟨hk, fun g g' hg => congrArg φ (h g g' hg)⟩

theorem mapSig_props : ∀ {G LL LL' : Type} [Group G] [Field LL] [Field LL'] (f : LL →+* LL') (I : Subgroup G) (Fr : G) (Sig : Finset (I →* LLˣ)), (FrobStable I Fr Sig → FrobStable I Fr (mapSig f Sig)) ∧ Formalism.MainNotions.ElementDenominator.rPrime I Fr (mapSig f Sig) = Formalism.MainNotions.ElementDenominator.rPrime I Fr Sig ∧ (mapSig f Sig).card ≤ Sig.card ∧ (1 ∈ Sig → 1 ∈ mapSig f Sig) := by
  intro G LL LL' _ _ _ f I Fr Sig
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hS a' ha'
    obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig a').1 ha'
    obtain ⟨b, hb, hab⟩ := hS a ha
    refine ⟨(Units.map (f : LL →* LL')).comp b, (mem_mapSig f Sig _).2 ⟨b, hb, rfl⟩, ?_⟩
    intro g h hgh
    simp [hab g h hgh]
  · unfold Formalism.MainNotions.ElementDenominator.rPrime
    apply le_antisymm
    · apply Finset.sup_le
      rintro ⟨p, q⟩ hpq
      rw [Finset.mem_product] at hpq
      obtain ⟨a, ha, rfl⟩ := (mem_mapSig f Sig p).1 hpq.1
      obtain ⟨b, hb, rfl⟩ := (mem_mapSig f Sig q).1 hpq.2
      rw [orbLen_map f I Fr a b]
      exact Finset.le_sup (s := Sig ×ˢ Sig)
        (f := fun p : (↥I →* LLˣ) × (↥I →* LLˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹)) (b := (a, b))
        (Finset.mem_product.2 ⟨ha, hb⟩)
    · apply Finset.sup_le
      rintro ⟨a, b⟩ hab
      rw [Finset.mem_product] at hab
      have := Finset.le_sup (s := mapSig f Sig ×ˢ mapSig f Sig)
        (f := fun p : (↥I →* LL'ˣ) × (↥I →* LL'ˣ) => Formalism.MainNotions.ElementDenominator.orbLen I Fr (p.1 * p.2⁻¹))
        (b := ((Units.map (f : LL →* LL')).comp a, (Units.map (f : LL →* LL')).comp b))
        (Finset.mem_product.2 ⟨(mem_mapSig f Sig _).2 ⟨a, hab.1, rfl⟩, (mem_mapSig f Sig _).2 ⟨b, hab.2, rfl⟩⟩)
      simpa only [orbLen_map f I Fr a b] using this
  · classical
    unfold mapSig
    exact Finset.card_image_le
  · intro h1
    exact (mem_mapSig f Sig 1).2 ⟨1, h1, MonoidHom.comp_one _⟩

end GlobalTheory.BaseCoef
