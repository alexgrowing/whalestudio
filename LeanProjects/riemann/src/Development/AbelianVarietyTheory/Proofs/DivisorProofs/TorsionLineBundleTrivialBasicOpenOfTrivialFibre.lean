import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionSpread

theorem triv_lbPow_pull {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) (k : ℕ) (φ : Y ⟶ X)
    (h : ∃ t : (Hecke.lbPow M k).Gen, t.IsGen) : ∃ t : (Hecke.lbPow (M.pull φ) k).Gen, t.IsGen := by
  have hP : (Hecke.lbPow M k).IsLB := LB.isLB_linComb hM _ _
  have hM' : (M.pull φ).IsLB := LB.isLB_pull hM φ
  have hP' : (Hecke.lbPow (M.pull φ) k).IsLB := LB.isLB_linComb hM' _ _
  have e : ∀ {Z : Scheme.{0}} {N : LB Z} (hN : N.IsLB) (h' : (Hecke.lbPow N k).IsLB),
      CechPic.cls _ h' = k • CechPic.cls N hN := by
    intro Z N hN h'
    refine (CechPic.cls_linComb hN (fun _ : Fin k => 𝟙 Z) (fun _ => 1) h').trans ?_
    simp [CechPic.pull_id]
  rw [← CechPic.cls_eq_zero_iff hP']
  rw [← CechPic.cls_eq_zero_iff hP] at h
  rw [e hM' hP', CechPic.cls_pull hM φ hM', ← map_nsmul, ← e hM hP, h, map_zero]

theorem triv_basicOpen_of_triv_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  intro hinf R _ _ A _ hA M hM _hrig k hk hpow K _ g₀ ht₀
  haveI := hA.proper
  haveI := hA.smooth
  have hP := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom hM
  haveI : Surjective A.hom := by
    haveI : Surjective ((1 : 𝟙_ (Over (Sp R)) ⟶ A).left ≫ A.hom) := by
      rw [Over.w]
      change Surjective (𝟙 _)
      infer_instance
    exact Surjective.of_comp (1 : 𝟙_ (Over (Sp R)) ⟶ A).left A.hom
  have h₀ := IsPullback.of_hasPullback A.hom (spMap g₀)
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R A.left A.hom M hM hP inferInstance inferInstance K g₀
    _ _ _ h₀ (GlobalTheory.AbLaw.CubeOpen.bijective_appTop GlobalTheory.ExpansionTotal.globalFns A hA h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := GlobalTheory.AbLaw.CubeOpen.exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ _ _ _ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      have hg := IsPullback.of_hasPullback A.hom (spMap g)
      refine (H T g _ _ _ hg (hu r hr)).1 ?_
      have hkT : IsUnit (k : T) := by simpa using hk.map g
      letI : GrpObj ((Over.pullback (spMap g)).obj A) := Functor.grpObjObj
      have hp := IsPullback.of_hasPullback ((Over.pullback (spMap g)).obj A).hom
        (spMap (Ideal.Quotient.mk (Ideal.span {e})))
      refine hinf T e he he' ((Over.pullback (spMap g)).obj A)
        (Out.TLinPf.isAb_pullback (spMap g) A hA) (M.pull (pullback.fst A.hom (spMap g)))
        (LB.isLB_pull hM _) k hkT (triv_lbPow_pull hM k _ hpow) _ _ _ hp ?_
      have hq := hp.paste_horiz hg
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
      exact GlobalTheory.AbLaw.CubeOpen.triv_pull_pull _ _
        ((H _ _ _ _ _ hq ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle))
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range ((A.hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ A.hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact GlobalTheory.AbLaw.CubeOpen.triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm)
    (hp.lift_fst _ _ _) ht

end GlobalTheory.TorsionSpread
