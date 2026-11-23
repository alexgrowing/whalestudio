import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianSchemeDescendsFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneBirigidifiedSymmetricNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.KerTorsion

open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Pdiv

theorem exists_pow_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (B : Type) [CommRing B] (y : Sp B ⟶ S) (x : Over.mk y ⟶ A), (∃ t : (P.pull (lift (snd A (Over.mk y) ≫ x) (fst A (Over.mk y))).left).Gen, t.IsGen) → ∃ M : ℕ, 0 < M ∧ x ^ M = 1 := by
  intro S A _ _ P ab hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ symm ample B _ y x ⟨t, ht⟩
  let A' := (Over.pullback y).obj A
  let φ := PullbackComparison.pφ y A
  let φ₂ := PullbackComparison.pφ₂ y A
  have pb : IsGrpPullback A' A y φ := PullbackComparison.isGrpPullback y A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare y A
  have hab : IsAbelianScheme A' :=
    { comm := inferInstance
      smooth := by have := ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  let P' : LB (G2 A').left := P.pull φ₂
  have hP' : P'.IsLB := pull_isLB hP φ₂
  have iso : LBIso P' (P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  obtain ⟨B₀, A₀, _, _, ψ, ψ₂, P₀, fin, ab₀, pb₀, sq₀, hP₀, iso₀, r₁, r₂, symm₀, ample₀⟩ :=
    GlobalTheory.T.polarised_abelian_scheme_descends_finite_type B A' P' hab hP'
      (gen_chartPull (chartPullLinComb P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id y A)) t₁ ht₁)
      (gen_chartPull (chartPullLinComb P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one y A)) t₂ ht₂)
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull P _ _ rfl)
        (chartPullLinComb P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap y A)) symm)
      ((pol_pull S _ A A' y φ _ _ (pull_isLB hP _) (pull_isLB hP' _) ab pb dg).2.1 ample)
  have : IsNoetherianRing B₀ := Algebra.FiniteType.isNoetherianRing ℤ B₀
  obtain ⟨M, hM, hker⟩ := GlobalTheory.T.exists_pow_eq_one_birigidifiedSymmetric_noetherian B₀ A₀ P₀ ab₀ hP₀ r₁ r₂ symm₀ ample₀
  refine ⟨M, hM, ?_⟩
  let T : Over (Sp B) := Over.mk (𝟙 _)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb T y (Category.id_comp _).symm
  have hx : x.left = (e.symm x).left ≫ φ := by rw [← he, e.apply_symm_apply]
  have key : e.symm x ^ M = 1 := by
    refine GlobalTheory.HTPull.kernel_pullback pb₀ sq₀ hP₀ hP' iso₀ M hker T (e.symm x) ?_
    have w : ((fst A' T).left ≫ φ) ≫ A.hom = (snd A' T).left ≫ y := by
      rw [Category.assoc, pb.1.w, ← Category.assoc, Over.w (fst A' T), ← Over.w (snd A' T)]
      exact congrArg (· ≫ y) (Category.comp_id _)
    let χ : (A' ⊗ T).left ⟶ (A ⊗ Over.mk y).left := pullback.lift _ _ w
    have c₁ : χ ≫ (fst A (Over.mk y)).left = (fst A' T).left ≫ φ := pullback.lift_fst _ _ _
    have c₂ : χ ≫ (snd A (Over.mk y)).left = (snd A' T).left := pullback.lift_snd _ _ _
    refine gen_chartPull (chartPullLinComb P _ _ _ _ χ fun _ => ?_) t ht
    refine (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk ((A' ⊗ T).hom ≫ y))
      (T' := A' ⊗ T) (𝟙 _) _ _ (Z := A ⊗ Over.mk y) χ _ _ ?_ ?_)
    · rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← hx, ← Category.assoc χ, c₂]
    · rw [Category.id_comp, c₁]
  rw [← e.apply_symm_apply x, ← map_pow, key, map_one]

end GlobalTheory.KerTorsion
