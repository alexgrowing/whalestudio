import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem isAffineOpen_preimage_nonzeroLocus {k : Type} [CommRing k] {X Y : Scheme.{0}} (g : Y ⟶ Sp k) [IsProper g]
    (π : Y ⟶ X) {M : LB X} (hM : M.IsLB) (hA : Out.RelAmple (Over.mk g) (M.pull π)) {d : ℕ} (hd : 1 ≤ d)
    (u : LB.Sec (pw M d)) : IsAffineOpen (π ⁻¹ᵁ Out.nonzeroLocus u) := by
  let s : (lbPow M d).Sec := powSecMk d u.f fun i j =>
    (u.compat i j).trans (congrArg (· * _) (by
      change (M.g i j ^ (d : ℤ)).val = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val]))
  have hs : Out.nonzeroLocus s = Out.nonzeroLocus u := nonzeroLocus_powSecMk _ _ _
  have h := isAmpleLB_of_relAmple_of_isAffine (Over.mk g) (LB.isLB_pull hM π) hA
  have := IsAmpleLB.isAffineOpen_nonzeroLocus g h hd (secPowPull s π)
  rwa [nonzeroLocus_secPowPull, hs] at this

theorem isFinite_of_fibres {R : Type} [CommRing R] {X : Scheme.{0}} {m : ℕ} (φ : X ⟶ PSpace R m)
    (f : X ⟶ Sp R) [IsProper f] (hf : φ ≫ PSpace.str R m = f)
    (H : ∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧
      ∀ i, IsAffineOpen (pullback.fst f (spMap β) ⁻¹ᵁ (φ ⁻¹ᵁ ProjSpace.chart R m i))) : IsFinite φ := by
  have := isProper_str R m
  have : IsProper (φ ≫ PSpace.str R m) := by rw [hf]; infer_instance
  have : IsProper φ := .of_comp φ (PSpace.str R m)
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun p => ?_
  obtain ⟨k, _, β, hβ, hk⟩ := H (PSpace.str R m p).asIdeal (PSpace.str R m p).isPrime
  have B := ProjSpace.isPullback_baseChange m β
  let φ' : pullback f (spMap β) ⟶ PSpace k m :=
    B.lift (pullback.fst f (spMap β) ≫ φ) (pullback.snd f (spMap β))
      (by rw [Category.assoc, hf, pullback.condition])
  have e₁ : φ' ≫ ProjSpace.baseChange m β = pullback.fst f (spMap β) ≫ φ := B.lift_fst _ _ _
  have e₂ : φ' ≫ PSpace.str k m = pullback.snd f (spMap β) := B.lift_snd _ _ _
  have P : IsPullback (pullback.fst f (spMap β)) φ' φ (ProjSpace.baseChange m β) :=
    IsPullback.of_bot (by rw [e₂, hf]; exact IsPullback.of_hasPullback f (spMap β)) e₁.symm B
  have : IsProper φ' := MorphismProperty.of_isPullback (P := @IsProper) P inferInstance
  have : IsAffineHom φ' := isAffineHom_of_forall_exists_isAffineOpen _ fun y => by
    obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k m y
    refine ⟨_, hi, ProjSpace.isAffineOpen_chart k m i, ?_⟩
    rw [← ProjSpace.baseChange_preimage_chart m β i, ← Scheme.Hom.comp_preimage, e₁, Scheme.Hom.comp_preimage]
    exact hk i
  have : IsFinite φ' := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨p', hp', -⟩ := Scheme.exists_preimage_of_isPullback B p (⊥ : PrimeSpectrum k)
    (PrimeSpectrum.ext hβ.symm)
  refine ((φ'.finite_preimage_singleton p').image (pullback.fst f (spMap β))).subset fun x hx => ?_
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P x p' (hx.trans hp'.symm)
  exact ⟨z, h₂, h₁⟩

theorem isAffineOpen_nonzeroLocus_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  intro R _ X f M d m u hd _ hM hu H i
  have : IsFinite (ProjSpace.toProj f u hu) :=
    isFinite_of_fibres _ f (ProjSpace.toProj_str f u hu) fun q hq => by
      obtain ⟨k, _, β, hβ, hA⟩ := H q hq
      refine ⟨k, _, β, hβ, fun j => ?_⟩
      rw [ProjSpace.toProj_preimage_chart]
      exact isAffineOpen_preimage_nonzeroLocus _ _ hM hA hd (u j)
  rw [← ProjSpace.toProj_preimage_chart f u hu]
  exact (ProjSpace.isAffineOpen_chart R m i).preimage _

end GlobalTheory.FibreAmple
