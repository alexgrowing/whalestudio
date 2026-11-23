import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsLiftSectionOfAmplePowFromClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    Presents (l • A) (lbPow (toLB A) l) fun j => (j PUnit.unit).1.2 ^ l := by
  refine ⟨isLB_lbPow (isLB_toLB A) l, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB A) l).g i j = _ from lbPow_g _ l i j, Units.val_pow_eq_pow_val,
      val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ l i).le hx)).nsmul l

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (s + t) f = GlobalTheory.secPull s f + GlobalTheory.secPull t f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.add_f, map_add])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (c • s) f = f.appTop c • GlobalTheory.secPull s f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.smul_f, map_mul]
    congr 1
    change ((X.presheaf.map _ ≫ f.appLE _ _ _).hom c) = ((f.appTop ≫ Y.presheaf.map _).hom c)
    rw [Scheme.Hom.map_appLE]
    rfl)

theorem algX_top_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (a : ℂ) :
    algX p ⊤ a = p.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv a) := by
  simp only [algX, RingHom.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem redι_closure_genericPoint {X : Scheme.{0}} (z : X)
    [IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme] :
    redι (Closeds.closure ({z} : Set X)) (genericPoint _) = z := by
  have hcl : closure ({redι (Closeds.closure ({z} : Set X)) (genericPoint _)} : Set X) = closure {z} := by
    rw [← Set.image_singleton, (redι _).isClosedEmbedding.closure_image_eq,
      (genericPoint_spec _).def, Set.image_univ, range_redι]
    rfl
  exact (inseparable_iff_closure_eq.2 hcl).eq

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sections_restrict_basis :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p →
      ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l →
        ∃ (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ (l • A).sections) ∧
          r = (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
            lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X))))) ∧
          ∀ a : Fin r → ℂ, a ≠ 0 → (l • A).GeneratesAt z (∑ i, Cartier.constFn p (a i) * f i) := by
  intro X _ _ p hp A z hA
  haveI hYi : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  obtain ⟨l₁, hl₁⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_exists_lift_section_of_ample_pow_from_closed X p hp (toLB A) (Closeds.closure ({z} : Set X)) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  letI : Algebra ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) :=
    algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  letI : Module ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    Module.compHom _ (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤))
  haveI : IsScalarTower ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤)
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    ⟨fun a g s => by
      show (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a * g) • s =
        algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a • (g • s)
      rw [mul_smul]⟩
  have hP := presents_lbPow_toLB A l
  have hr : Module.finrank ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec =
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) := by
    rw [← lineBundleGlobalSectionsDim_eq_finrank]
    exact lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB hP.isLB _) (pull_isLB (isLB_toLB _) _)
      (by rw [cls_pull hP.isLB, cls_pull (isLB_toLB _), ← hP.toPic_eq, toPic_apply])
  obtain ⟨v, hv⟩ : ∃ v : Fin (Module.finrank ℂ
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec) →
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec, LinearIndependent ℂ v := by
    by_cases hf : Module.Finite ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec
    · exact ⟨_, (Module.finBasis ℂ _).linearIndependent⟩
    · rw [Module.finrank_of_not_finite hf]
      exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  choose s hs using fun i => hl₁ l hl (v i)
  refine ⟨_, fun i => hP.rat (s i), fun i => hP.rat_mem _, hr, fun a ha => ?_⟩
  have e₁ : ∑ i, Cartier.constFn p (a i) * hP.rat (s i) = hP.rat (∑ i, algX p ⊤ (a i) • s i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, Algebra.smul_def, CartierDiv.algebraMap_top]
    rfl
  have e₂ : GlobalTheory.secPull (∑ i, algX p ⊤ (a i) • s i) (redι (Closeds.closure ({z} : Set X))) = ∑ i, a i • v i := by
    let F : (lbPow (toLB A) l).Sec →+ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
      { toFun := fun t => GlobalTheory.secPull t _
        map_zero' := by
          have := secPull_smul' (0 : Γ(X, ⊤)) (0 : (lbPow (toLB A) l).Sec) (redι (Closeds.closure ({z} : Set X)))
          rwa [zero_smul, map_zero, zero_smul] at this
        map_add' := fun t t' => secPull_add' t t' _ }
    change F _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change GlobalTheory.secPull _ _ = _
    rw [secPull_smul', hs i, algX_top_eq]
    rfl
  have hne : ∑ i, a i • v i ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    exact hi (Fintype.linearIndependent_iff.1 hv a h0 i)
  rw [← e₂] at hne
  have hgen := (sec_ne_zero_iff _).1 hne
  rw [GlobalTheory.nonzeroLocus_secPull] at hgen
  have hgen' : redι (Closeds.closure ({z} : Set X)) (genericPoint _) ∈
      nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := hgen
  have key : ∀ y : X, y = redι (Closeds.closure ({z} : Set X)) (genericPoint _) →
      y ∈ nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := fun y hy => hy ▸ hgen'
  have hz := key z (redι_closure_genericPoint z).symm
  rw [e₁]
  exact (hP.generatesAt_rat_iff _).2 hz

end GlobalTheory.PairStep
