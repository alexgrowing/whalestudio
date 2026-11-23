import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

namespace GlobalTheory.EtC

def SpecGood : Prop :=
  ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (κ : Type) [Field κ] [Algebra O κ]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (hV : ∀ a : O, algebraMap K Ω (algebraMap O K a) ∈ V)
    (kb : Type) [Field kb] [IsAlgClosed kb] [Algebra κ kb] (r : V →+* kb), Function.Surjective r →
    (∀ a : O, r ⟨_, hV a⟩ = algebraMap κ kb (algebraMap O κ a)) →
    ∀ {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of O)) [Smooth p] [IsProper p]
      (iY : geom kb (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O κ)))) ⟶
        pullback p (Spec.map (CommRingCat.ofHom (RingHom.codRestrict ((algebraMap K Ω).comp (algebraMap O K)) V hV))))
      (jY : geom Ω (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))) ⟶
        pullback p (Spec.map (CommRingCat.ofHom (RingHom.codRestrict ((algebraMap K Ω).comp (algebraMap O K)) V hV)))),
    iY ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ →
    iY ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom r) →
    jY ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ →
    jY ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom V.subtype) →
    (∀ q : ℕ, IsUnit (q : kb) → ∀ i : ℤ, Eqv _ (sch.map iY) (tw q i) ∧ Eqv _ (sch.map jY) (tw q i)) ∧
    ∀ (l : ℕ) [Fact l.Prime], IsUnit (l : kb) → ∀ n i : ℤ,
      ∃ sp : HQ l (sch.obj (geom kb (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O κ)))))) n i ≃ₗ[ℚ_[l]]
          HQ l (sch.obj (geom Ω (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap O K)))))) n i,
        (∀ x, sp (pullHQ l (sch.map iY) n i x) = pullHQ l (sch.map jY) n i x) ∧
        ∀ (σ : Ω ≃ₐ[K] Ω) (τ : kb ≃ₐ[κ] kb) (hσ : ∀ v ∈ V, σ v ∈ V), (∀ v : V, r ⟨σ v, hσ v v.2⟩ = τ (r v)) →
          ∀ x, sp (galHQ l kb _ n i τ x) = galHQ l Ω _ n i σ (sp x)

end GlobalTheory.EtC

end
