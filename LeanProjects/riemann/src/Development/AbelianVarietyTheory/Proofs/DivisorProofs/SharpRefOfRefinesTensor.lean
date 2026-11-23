import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem sharpRef_of_tens : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  intro W V _ _ Q V₁ _ _ ρ D₀ D e₀ hR T e he
  obtain ⟨β, β₂, wR, hpb, hsq, hwR, hcR, htR⟩ := hR
  obtain ⟨io, hιm, hι⟩ := grpPullback_iso hpb (isGrpPullback_pullback Q.B (spMap ρ))
  have hprI : ∀ a, IsMonHom (T.pr a ≫ io.hom) := fun a => by
    haveI := T.pr_hom a; haveI := hιm; infer_instance
  have hpr' : ∀ a, (T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = (T.pr a).left ≫ β := fun a => by
    rw [Over.comp_left, Category.assoc, hι]
  let φQ : (Fin 8 × Fin 8) × Fin 4 → (D.P.A.left ⟶ Q.B.left) := fun k =>
    lamPts (T.pr k.1.1 ≫ io.hom) (T.pr k.1.2 ≫ io.hom) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)
  let εQ : (Fin 8 × Fin 8) × Fin 4 → ℤ := fun k => -(W k.1.1 k.1.2 * negε k.2)
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_tensor_mumfordBundle_iso_of_generator D₀.P.A Q.B D₀.P.L Q.M.L D₀.P.isLB Q.M.isLB β₂ wR hwR W D.P.A T.pr φQ εQ
    (fun k => GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback D₀.P.A Q.B (spMap ρ) β β₂ hpb hsq D.P.A _ _ _ _ (hpr' _) (hpr' _) k.2)
    (fun k => by obtain ⟨⟨a, b⟩, i⟩ := k; fin_cases i <;> simp [εQ, negε, Oε])
  obtain ⟨w', hw', hwv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_pullback_id_values (A := D.P.L) (tensφ T.pr) (tensε W) φQ εQ D.P.isLB D₀.P.isLB Q.M.isLB T.w T.w_gen v hv
  refine ⟨fun a => T.pr a ≫ io.hom, w', hprI, fun T' y => ?_, hw', fun mu a => ?_, fun κ hκ mu z J J' hJ hJ' => ?_⟩
  · refine ⟨Fan.IsLimit.lift T.lim (fun a => y a ≫ io.inv), fun a => ?_, fun x hx => ?_⟩
    · have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      show _ ≫ T.pr a ≫ io.hom = _
      rw [← Category.assoc, h]
      simp
    · refine Fan.IsLimit.hom_ext T.lim _ _ fun a => ?_
      have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      change x ≫ T.pr a = _ ≫ T.pr a
      rw [h, ← hx a]
      simp
  · show (D.c (e mu) ≫ T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = _
    rw [← Category.assoc, Over.comp_left, Category.assoc, hι, T.c_pr, hcR, he]
  · choose J₀ hJ₀ using fun s : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (s z)
    have hJ₀' : Good D₀.P.L z J₀ := hJ₀
    have h1 := T.psi (e mu) z J₀ J' hJ₀' hJ'
    have h2 := hwv _ (D.xK (e mu)) z J J₀ (J' (D.xK (e mu))) (hJ' _) hJ hJ₀'
    have h3 := hvv _ (D.xK (e mu)) z J J₀ hJ hJ₀'
    have h4 : ∀ a b, D.xK (e mu) ≫ (lift (T.pr a) (T.pr b)).left =
        (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left := by
      intro a b
      show (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ _ = _
      rw [← Over.comp_left, comp_lift, Category.assoc, Category.assoc, T.c_pr, T.c_pr]
    have h5 : ∀ a b, val (D₀.tau (T.xe (e mu) a) (T.xe (e mu) b)) (𝟙 _) z J₀ =
        lamVal wR (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left z J J₀ *
          val (Q.tau (mu a) (mu b)) κ z J := fun a b => by
      rw [htR κ hκ _ _ z J J₀ hJ hJ₀', he, he]
    rw [h1]
    erw [h2]
    rw [h3]
    simp only [h4, h5, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.Mum.PowData
