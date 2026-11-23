import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.Twist (resM)
open Limits (pullback)

namespace GlobalTheory.FlagBaseChange

variable {k : Type} [CommRing k] {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k}

set_option maxHeartbeats 1000000 in

theorem pull_snd_eq_map_bcIso (π : Y ⟶ B) (w : π ≫ q = p) (g : B' ⟶ B) {E : B.Modules} {n : ℕ}
    (h : VMetric q E n) (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) :
    (h.pull g rfl).pull (pullback.snd π g) w' =
      ((h.pull π w).pull (pullback.fst π g) rfl).map (bcIso π g E) := by
  have := h.isVB.isQuasicoherent
  have := (h.isVB.pullback π).isQuasicoherent
  have := (h.isVB.pullback g).isQuasicoherent
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  have hy : PtsOver.map π w _ (PtsOver.map (pullback.fst π g) rfl _ z) =
      PtsOver.map g rfl _ (PtsOver.map (pullback.snd π g) w' _ z) :=
    Subtype.ext (by simp only [PtsOver.map_val, Category.assoc, pullback.condition])
  let c₀ := h.isVB.pick (PtsOver.map g rfl _ (PtsOver.map (pullback.snd π g) w' _ z))
  have hc₀ := h.isVB.mem_pick (σ := σ) (PtsOver.map g rfl _ (PtsOver.map (pullback.snd π g) w' _ z))
  let c := (c₀.pull h.isVB g).pull (h.isVB.pullback g) (pullback.snd π g)
  let c' := ((c₀.pull h.isVB π).pull (h.isVB.pullback π) (pullback.fst π g)).map (bcIso π g E)
  have hz : z ∈ ptsIn _ σ c.U := hc₀
  have hz' : z ∈ ptsIn _ σ c'.U := by
    change PtsOver.map π w _ (PtsOver.map (pullback.fst π g) rfl _ z) ∈ ptsIn q σ c₀.U
    rw [hy]
    exact hc₀
  have hz'' : PtsOver.map π w _ (PtsOver.map (pullback.fst π g) rfl _ z) ∈ ptsIn q σ c₀.U := hz'
  have key : ∀ b, resM _ (inf_le_left : c.U ⊓ c'.U ≤ c.U) (c.e b) =
      resM _ (inf_le_right : c.U ⊓ c'.U ≤ c'.U) (c'.e b) := by
    intro b
    refine (GlobalTheory.QCoh.res_pullbackSections _ _ _ _ _).trans (Eq.trans ?_ (GlobalTheory.Twist.app_resM _ _ _))
    refine Eq.trans ?_ (congrArg _ (GlobalTheory.QCoh.res_pullbackSections _ _ _ _ _).symm)
    exact (GlobalTheory.Vert.DivPull.pullbackSquare_app pullback.condition E le_rfl _ le_rfl _ (c₀.e b)).symm
  have hW : z ∈ ptsIn _ σ (c.U ⊓ c'.U) := mem_ptsIn_inf.2 ⟨hz, hz'⟩
  have htr : c'.tr _ σ c z = 1 := by
    ext a b
    have e1 := c'.crd_resM (σ := σ) (c.e b) inf_le_left hW
    have e2 := c'.crd_resM (σ := σ) (c'.e b) inf_le_right hW
    rw [key] at e1
    rw [Chart.tr, Matrix.of_apply, ← e1, e2, c'.crd_frame hz', Pi.single_apply, Matrix.one_apply]
  have L : (((h.pull g rfl).pull (pullback.snd π g) w').met σ).G c z = (h.met σ).G c₀ (PtsOver.map g rfl _ (PtsOver.map (pullback.snd π g) w' _ z)) :=
    (((h.met σ).pull g rfl).pull_G (pullback.snd π g) w' (c₀.pull h.isVB g) hc₀).trans
      ((h.met σ).pull_G g rfl c₀ hc₀)
  have R1 : ((((h.pull π w).pull (pullback.fst π g) rfl).map (bcIso π g E)).met σ).G c z = ((((h.pull π w).pull (pullback.fst π g) rfl).map (bcIso π g E)).met σ).G c' z := by
    refine ((((((h.met σ).pull π w).pull (pullback.fst π g) rfl).map (bcIso π g E)).trans c' c z hz')).trans ?_
    rw [htr, chg_one]
    rfl
  have R2 : ((((h.pull π w).pull (pullback.fst π g) rfl).map (bcIso π g E)).met σ).G c' z = (h.met σ).G c₀ (PtsOver.map π w _ (PtsOver.map (pullback.fst π g) rfl _ z)) :=
    ((((h.met σ).pull π w).pull (pullback.fst π g) rfl).map_G (bcIso π g E)
      ((c₀.pull h.isVB π).pull (h.isVB.pullback π) (pullback.fst π g)) hz').trans
    ((((h.met σ).pull π w).pull_G (pullback.fst π g) rfl (c₀.pull h.isVB π) hz'').trans
      ((h.met σ).pull_G π w c₀ hz''))
  refine ⟨c, hz, ?_⟩
  rw [L, R1, R2, hy]

end GlobalTheory.FlagBaseChange

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt

theorem GlobalTheory.FlagBaseChange.isometric_grLB_pullFlag : ∀ (k : Type) [CommRing k] (B Y B' : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (g : B' ⟶ B) (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) (w' : Limits.pullback.snd π g ≫ g ≫ q = Limits.pullback.fst π g ≫ p) (i : Fin n), ((VMetric.grLB fl i (H.pull π w)).pull (Limits.pullback.fst π g) rfl).Isometric (VMetric.grLB (FlagBaseChange.pullFlag π g fl) i ((H.pull g rfl).pull (Limits.pullback.snd π g) w')) := by
  intro k _ B Y B' q p π w g E n h H fl w' i
  have hφ : ((h.pull π w).pull (Limits.pullback.fst π g) rfl).IsIsometry
      ((h.pull g rfl).pull (Limits.pullback.snd π g) w') (FlagBaseChange.bcIso π g E) :=
    (VMetric.isIsometry_iff _).2 (FlagBaseChange.pull_snd_eq_map_bcIso π w g h w')
  have e := VMetric.grLB_ofIso hφ ((H.pull π w).pull (Limits.pullback.fst π g) rfl)
    ((H.pull g rfl).pull (Limits.pullback.snd π g) w') (fl.pull (Limits.pullback.fst π g)) i
  have A := VMetric.isometric_grLB_pull k Y (Limits.pullback π g) p (Limits.pullback.fst π g ≫ p)
    ((Scheme.Modules.pullback π).obj E) n (h.pull π w) (H.pull π w) fl (Limits.pullback.fst π g) rfl i
  change HermLB.Isometric _ (VMetric.grLB ((fl.pull (Limits.pullback.fst π g)).ofIso
    (FlagBaseChange.bcIso π g E)) i _)
  rw [e]
  exact A.symm
