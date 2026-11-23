import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterGrLinePermuteIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagBundleSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarOfIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChangeStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest.Reduce
open Limits

variable {k : Type} [CommRing k]

theorem isIsometry_pullbackCongr {X Y : Scheme.{0}} {q : Y ⟶ Sp k} {t : X ⟶ Sp k} {E : Y.Modules} {r : ℕ}
    (h : VMetric q E r) {f f' : X ⟶ Y} (e : f = f') (hf : f ≫ q = t) (hf' : f' ≫ q = t) :
    (h.pull f hf).IsIsometry (h.pull f' hf') ((Scheme.Modules.pullbackCongr e).app E) := by
  subst e
  intro σ V s s' y hy
  rfl

theorem isIsometry_bcIso {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    (g : B' ⟶ B) {E : B.Modules} {r : ℕ} (h : VMetric q E r)
    (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) :
    ((h.pull π w).pull (pullback.fst π g) rfl).IsIsometry ((h.pull g rfl).pull (pullback.snd π g) w')
      (bcIso π g E) := by
  obtain ⟨-, hc⟩ := VMetric.isIsometry_pull_id_comp k B q E r h
  have e₁ : (pullback.fst π g ≫ π) ≫ q = pullback.fst π g ≫ p := by rw [Category.assoc, w]
  have e₂ : (pullback.snd π g ≫ g) ≫ q = pullback.fst π g ≫ p := by rw [Category.assoc, w']
  exact IsometryPullback.isIsometry_trans (hc Y _ p _ π (pullback.fst π g) w rfl e₁)
    (IsometryPullback.isIsometry_trans (isIsometry_pullbackCongr h pullback.condition e₁ e₂)
      (IsometryPullback.isIsometry_symm (hc B' _ (g ≫ q) _ g (pullback.snd π g) rfl w' e₂)))

theorem isometric_grLB_bcFlag {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    (g : B' ⟶ B) {E : B.Modules} {r : ℕ} {h : VMetric q E r} (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r)
    (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) (i : Fin r) :
    (VMetric.grLB (bcFlag π g fl) i ((H.pull g rfl).pull (pullback.snd π g) w')).Isometric
      ((VMetric.grLB fl i (H.pull π w)).pull (pullback.fst π g) rfl) := by
  rw [bcFlag, VMetric.grLB_ofIso (isIsometry_bcIso π w g h w') ((H.pull π w).pull _ rfl)]
  exact VMetric.isometric_grLB_pull k Y _ p _ _ r (h.pull π w) (H.pull π w) fl (pullback.fst π g) rfl i

end GlobalTheory.CovTest.Reduce

namespace GlobalTheory.CovTest.Reduce
open Limits

theorem swap_of_section (hA : ArCalc) (hG : GdegPull) {G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ} (hS : SwapReg G)
    (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hp : IsArithVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl))
    (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ)
    (hΦ : IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ)
    (hΨ : IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ)
    (a b : ℤ) (B' : Scheme.{0}) [IsIntegral B'] (g : B' ⟶ B) (s : B' ⟶ Y) (hs : s ≫ π = g)
    (hgq : IsArithVar (g ≫ q) d) (hreg : ∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b))
    [IsIntegral (pullback π g : Scheme.{0})] (hY' : IsArithVar (pullback.fst π g ≫ p) (d + 1))
    (hfg : pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y)
    (hfd : (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0) :
    Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Ψ (G (d + 1) a b) := by
  set ρ := pullback.fst π g
  set π' := pullback.snd π g
  set δ := ρ.residueDegree (genericPoint (pullback π g : Scheme.{0}))
  have w' : π' ≫ g ≫ q = ρ ≫ p := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, w]
  set L : Fin 3 → HermLB p := ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w]
  set L' : Fin 3 → HermLB (ρ ≫ p) := ![VMetric.grLB (bcFlag π g fl) 0 ((H.pull g rfl).pull π' w'),
    VMetric.grLB (bcFlag π g fl) 1 ((H.pull g rfl).pull π' w'), (A.pull g rfl).pull π' w']
  have iso : ∀ j, ((L j).pull ρ rfl).Isometric (L' j) := by
    intro j
    fin_cases j
    · exact (isometric_grLB_bcFlag π w g H fl w' 0).symm
    · exact (isometric_grLB_bcFlag π w g H fl w' 1).symm
    · have e₁ : (ρ ≫ π) ≫ q = ρ ≫ p := by rw [Category.assoc, w]
      have e₂ : (π' ≫ g) ≫ q = ρ ≫ p := by rw [Category.assoc, w']
      exact (HermLB.isometric_of_refines (HermLB.refines_pull_pull A π w ρ rfl e₁)).trans
        ((HermLB.isometric_pull_of_eq A pullback.condition e₁ e₂).trans
          (HermLB.isometric_of_refines (HermLB.refines_pull_comp A g rfl π' w' e₂)))
  have hΦ' : IsArFun L' (d + 1) ((δ : ℝ) • Φ) :=
    (((hA.arIso) k _ (ρ ≫ p) (d + 1) hY').2 (Fin 3) _ _
      (((hA.arProj) k Y _ p (ρ ≫ p) (d + 1) hp hY' ρ rfl hfg hfd).2 (Fin 3) L Φ hΦ)).2.1 L' iso
  have hΨ' : IsGeoFun L' (d + 1) ((δ : ℝ) • Ψ) := by
    refine ⟨fun n => ?_, fun P e he hP => ?_⟩
    · rw [LinearMap.smul_apply, hΨ.1 n, smul_eq_mul,
        ← hG k Y _ p (ρ ≫ p) (d + 1) hp hY' ρ rfl hfg hfd (comb L n)]
      exact ((isometric_comb_pull L n ρ rfl).symm.trans (isometric_comb_congr iso n)).gdeg_eq _
    · rw [LinearMap.smul_apply, hΨ.2 P e he hP, smul_zero]
  have hflat : Nonempty (Vert.Flag ((Scheme.Modules.pullback g).obj E) 2) :=
    ⟨(fl.pull s).ofIso ((Scheme.Modules.pullbackComp s π).app E ≪≫ (Scheme.Modules.pullbackCongr hs).app E)⟩
  have key := hS k B' _ (g ≫ q) (ρ ≫ p) d hgq hY' hreg π' w' _ (h.pull g rfl) (H.pull g rfl) hflat
    (bcFlag π g fl) (GlobalTheory.T.flag_bundle_pullback_base_change B Y B' π g Unit (fun _ => E) (fun _ => 2) (fun _ => fl) hfl)
    (A.pull g rfl) ((δ : ℝ) • Φ) ((δ : ℝ) • Ψ) hΦ' hΨ' a b
  simp only [LinearMap.smul_apply, smul_eq_mul, ← mul_add] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hfd) key

end GlobalTheory.CovTest.Reduce

namespace GlobalTheory.CovTest

open Limits in

theorem swap2_of_swapRegular : ArCalc → RegularAlteration → GdegPull →
    ∀ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, SwapReg G → Swap2 G := by
  intro hA hR hG G hS k _ B Y _ _ q p d hq hp π w E h H fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨Z, _, i, hZ, hZg, hZd⟩ := GlobalTheory.T.rank_two_flag_bundle_section k B Y q p d hq hp π w E h.isVB fl hfl
  obtain ⟨B', _, ρ₀, hB', hreg, hρg, hρd⟩ := GlobalTheory.T.exists_regular_integral_cover_same_dimension hR k Z (i ≫ p) d hZ
  have hgq : IsArithVar ((ρ₀ ≫ i ≫ π) ≫ q) d := by
    rwa [Category.assoc, Category.assoc, w]
  have hgg : (ρ₀ ≫ i ≫ π) (genericPoint B') = genericPoint B := by
    rw [Scheme.Hom.comp_apply, hρg, hZg]
  have hgd : (ρ₀ ≫ i ≫ π).residueDegree (genericPoint B') ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, hρg]
    exact mul_ne_zero hZd hρd
  obtain ⟨_, hY', hfg, hfd⟩ := GlobalTheory.T.flag_bundle_base_change_arith_variety k B Y B' q p d hq hp π w E h.isVB fl hfl _ hgq hgg hgd
  exact Reduce.swap_of_section hA hG hS k B Y q p d hp π w E h H fl hfl A Φ Ψ hΦ hΨ a b B' _ (ρ₀ ≫ i)
    (Category.assoc _ _ _) hgq hreg hY' hfg hfd

end GlobalTheory.CovTest

end
