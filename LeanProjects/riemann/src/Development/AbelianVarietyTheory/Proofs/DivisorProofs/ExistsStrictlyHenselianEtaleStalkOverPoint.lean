import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianIndEtaleOverPrimeStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.EtC.exists_isStalk_over_point : ∀ (S : Scheme.{0}) (U : Over S), Etale U.hom →
    ∀ u : U.left, ∃ (O : Type) (_ : CommRing O) (s : Spec (CommRingCat.of O) ⟶ S)
      (g : Over.mk s ⟶ U), _root_.GlobalTheory.EtC.IsStalk O s ∧ ∃ v, g.left v = u := by
  intro S U hU u
  let 𝒰 := U.left.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒰.covers u
  let R : CommRingCat := 𝒰.X (𝒰.idx u)
  let f : Spec R ⟶ U.left := 𝒰.f (𝒰.idx u)
  haveI : IsOpenImmersion f := 𝒰.map_prop _
  haveI := hU
  let j : Spec R ⟶ S := f ≫ U.hom
  let y' : Spec R := y
  haveI := y'.isPrime
  obtain ⟨O, hO, hAO, hloc, hsh, hind, hcomap⟩ :=
    _root_.GlobalTheory.StrictHensPrime.exists_sh_indEt R y'.asIdeal
  let φ : Spec (CommRingCat.of O) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R O))
  refine ⟨O, hO, φ ≫ j, Over.homMk (φ ≫ f) (by simp [j]),
    ⟨hsh, R, inferInstance, hAO, j, inferInstance, hind, rfl⟩, IsLocalRing.closedPoint O, ?_⟩
  have hφ : φ (IsLocalRing.closedPoint O) = y' := by
    apply PrimeSpectrum.ext
    rw [← hcomap]
    rfl
  show (φ ≫ f) (IsLocalRing.closedPoint O) = u
  change f (φ (IsLocalRing.closedPoint O)) = u
  rw [hφ]
  exact hy

end GlobalTheory.EtC
