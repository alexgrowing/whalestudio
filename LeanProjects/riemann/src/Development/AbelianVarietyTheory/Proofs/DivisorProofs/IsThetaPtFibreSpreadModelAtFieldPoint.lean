import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (j : B →+* C) :
    spMap j ≫ spMap f = spMap (j.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem isThetaPt_fibre : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  intro F Ω T _ _ _ _ _ _ _ _ em jT t hft hinj hcomp A P φ hp hw m I x y v hm hm3 hxy hy hcov hA
  obtain ⟨⟨hL, hL2, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  let tR : T →+* F := t.toRingHom
  have htR : ∀ a : F, tR (algebraMap F T a) = a := fun a => t.commutes a
  have hsurj : Function.Surjective tR := fun a => ⟨algebraMap F T a, htR a⟩
  let p : Ideal T := RingHom.ker tR
  haveI hpm : p.IsMaximal := RingHom.ker_isMaximal_of_surjective tR hsurj
  let R := Localization.AtPrime p
  let s : Sp R ⟶ Sp T := spMap (algebraMap T R)
  have hjT : ∀ z : p.primeCompl, IsUnit (jT z) := fun z => by
    refine IsUnit.mk0 _ fun h => z.2 ?_
    have : (z : T) = 0 := hinj (h.trans (map_zero jT).symm)
    rw [this]; exact p.zero_mem
  have htU : ∀ z : p.primeCompl, IsUnit (tR z) := fun z => IsUnit.mk0 _ fun h => z.2 h
  let jR : R →+* Ω := IsLocalization.lift hjT
  let r : R →+* F := IsLocalization.lift htU
  have hjR : jR.comp (algebraMap T R) = jT := IsLocalization.lift_comp hjT
  have hr : r.comp (algebraMap T R) = tR := IsLocalization.lift_comp htU
  have hjRinj : Function.Injective jR := by
    refine (injective_iff_map_eq_zero jR).2 fun z hz => ?_
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    have hz' := hz
    simp only [jR] at hz'
    rw [IsLocalization.lift_mk', Units.mul_left_eq_zero] at hz'
    show IsLocalization.mk' R a b = 0
    rw [hinj (hz'.trans (map_zero jT).symm), IsLocalization.mk'_zero]
  let aR : F →+* R := (algebraMap T R).comp (algebraMap F T)
  have hjaR : ∀ a, jR (aR a) = em a := fun a => by
    show (jR.comp (algebraMap T R)) (algebraMap F T a) = em a
    rw [hjR, ← hcomp]; rfl
  have hraR : ∀ a, r (aR a) = a := fun a => by
    show (r.comp (algebraMap T R)) (algebraMap F T a) = a
    rw [hr]; exact htR a
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hu : IsUnit (m : R) := by
    have := (IsUnit.mk0 (m : F) hmF).map aR
    rwa [map_natCast] at this

  have hmo : ∀ i, ((Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i) ^ (m ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨w, hwR⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local hL hL2 P s hm hu _ hmo

  have e1 : spMap jR ≫ s = 𝟙 (Sp Ω) ≫ spMap jT := by
    rw [Category.id_comp, spMap_comp_spMap, hjR]
  have e2 : spMap r ≫ s = spMap tR := by rw [spMap_comp_spMap, hr]
  have hΩ := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P jR e1 hwR
  have hF := GlobalTheory.Ex.Specialise.isThetaPt_map hL2 P r e2 hwR

  let yΩ : I → (Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ P.A) := fun i =>
    (Over.homMk (spMap jR) e1 : Over.mk (𝟙 (Sp Ω) ≫ spMap jT) ⟶ Over.mk s) ≫
      (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i
  have hyΩ : ∀ i, (yΩ i).left = (x i).left ≫ φ := fun i => by
    rw [hxy i]
    simp only [yΩ, Over.comp_left, Over.homMk_left]
    rw [← Category.assoc, e1, Category.id_comp]
  obtain ⟨eA, heA⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hp (𝟙 (Sp Ω)) (𝟙 (Sp Ω) ≫ spMap jT) rfl
  have hxo : ∀ i, x i ^ (m ^ 2) = 1 := fun i => by
    apply eA.injective
    rw [map_pow, map_one]
    have : eA (x i) = yΩ i := Over.OverMorphism.ext ((heA (x i)).trans (hyΩ i).symm)
    rw [this]
    simp only [yΩ]
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy, MonObj.comp_one, MonObj.comp_one]
  have hA' := (GlobalTheory.ThetaPtUp.isThetaPt_iff (T := baseOver (Sp Ω)) (x₀ := yΩ) hp hw hyΩ hxo _).1 hA
  let eΩ : Γ(Sp Ω, ⊤) ≃+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  haveI : IsLocalRing Γ((Over.mk (𝟙 (Sp Ω) ≫ spMap jT)).left, ⊤) := eΩ.symm.isLocalRing
  obtain ⟨u, hu'⟩ := GlobalTheory.ThetaUniq.exists_unit_over hL.globalFns P hm
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hΩ) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hA')
  let cΩ : Ωˣ := Units.map eΩ.toMonoidHom u
  have hc : ∀ i, em (v i) = (cΩ : Ω) * jR (w i) := fun i =>
    (eΩ.apply_symm_apply (em (v i))).symm.trans (((congrArg eΩ (hu' i)).trans (map_mul eΩ _ _)).trans
      (congrArg (_ * ·) (eΩ.apply_symm_apply (jR (w i)))))

  have hF' : IsThetaPt P m (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i)
      (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i))) := by
    have hpts : (fun i => (Over.homMk (spMap tR) : Over.mk (spMap tR) ⟶ baseOver (Sp T)) ≫ y i) =
        fun i => (Over.homMk (spMap r) e2 : Over.mk (spMap tR) ⟶ Over.mk s) ≫
          (Over.homMk s : Over.mk s ⟶ baseOver (Sp T)) ≫ y i := funext fun i => by
      refine Over.OverMorphism.ext ?_
      simp only [Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, e2]
    rw [hpts]
    exact hF
  obtain ⟨z, hz, hne⟩ := GlobalTheory.ThetaCoset.exists_ne_zero_over hL hL2 P (spMap tR) (k := m) (by omega) hmF
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local P _ hF') 1
  obtain ⟨i₀, hi₀⟩ := hcov z hz
  have hr0 : r (w i₀) ≠ 0 := fun h => hne i₀ (by rw [_root_.one_mul]; exact hi₀) (by
    show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (r (w i₀)) = 0
    rw [h]; exact map_zero _)

  have hv0 : v i₀ ≠ 0 := fun h => hr0 (by
    have q := hc i₀
    rw [h, map_zero, eq_comm, Units.mul_right_eq_zero] at q
    rw [hjRinj (q.trans (map_zero jR).symm), map_zero])
  have key : ∀ i, w i * aR (v i₀) = w i₀ * aR (v i) := fun i => hjRinj (by
    rw [map_mul, map_mul, hjaR, hjaR, hc, hc]; ring)
  have hrw : ∀ i, r (w i) * v i₀ = r (w i₀) * v i := fun i => by
    have q := congrArg r (key i)
    rwa [map_mul, map_mul, hraR, hraR] at q
  have hd : r (w i₀) / v i₀ ≠ 0 := div_ne_zero hr0 hv0
  have hfin : ∀ i, (r (w i₀) / v i₀)⁻¹ * r (w i) = v i := fun i => by
    rw [inv_div, div_mul_eq_mul_div, div_eq_iff hr0]
    linear_combination hrw i
  have H := GlobalTheory.Ex.Specialise.isThetaPt_mul P hF' (inv_ne_zero hd)
  simp only [hfin] at H
  exact H

end GlobalTheory.Mum
