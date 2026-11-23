import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcInvariantUnderScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLineMetricUnderScalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDetZeroRankMetricStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagScale

theorem flagBc_scale {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ}
    {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (s : ℝ) :
    ((h.scale s).FlagBcFinite fl ↔ h.FlagBcFinite fl) ∧ (h.scale s).flagBc fl = h.flagBc fl :=
  GlobalTheory.T.flag_bc_invariant_under_scaling H fl s

theorem isometric_grLB_scale {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ}
    {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) (s : ℝ) :
    (VMetric.grLB fl i (H.scale s)).Isometric ((VMetric.grLB fl i H).shift (fun _ => -s / 2) fun _ => rfl) :=
  GlobalTheory.T.graded_line_metric_under_scaling H fl i s

theorem gdeg_det_rank_zero (HC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (hp : IsArithVar p 1) {E : X.Modules} {h : VMetric p E 0} (H : h.IsCInf) :
    gdeg (VMetric.det H) 1 = 0 :=
  GlobalTheory.T.degree_det_zero_rank_metric HC hp H

theorem isometric_det_last {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ}
    {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) :
    (VMetric.det (H.restrict (fl.isSubbundle (Fin.last r)) (fl.isVB (Fin.last r)))).Isometric (VMetric.det H) := by
  have e : (h.restrict (fl.isSubbundle (Fin.last r)) (fl.isVB (Fin.last r))).IsIsometry h (asIso (fl.ι (Fin.last r))) :=
    fun σ V s t y hy => ((h.met σ).form_restrict (fl.isSubbundle (Fin.last r)) (fl.isVB (Fin.last r)) s t hy).symm
  rw [VMetric.isIsometry_iff] at e
  have := VMetric.isometric_det_map (H.restrict (fl.isSubbundle (Fin.last r)) (fl.isVB (Fin.last r))) (asIso (fl.ι (Fin.last r)))
  convert this using 2 <;> first | rfl | simp | exact e

theorem isometric_det_tens_grLB' {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {N : ℕ}
    {h : VMetric p E N} (H : h.IsCInf) (fl : Vert.Flag E N) (i : Fin N) :
    ((VMetric.det (H.restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc))).tens (VMetric.grLB fl i H)).Isometric
      (VMetric.det (H.restrict (fl.isSubbundle i.succ) (fl.isVB i.succ))) := by
  have hf : VB.IsSubbundle (fl.step i) := ⟨inferInstance, 1, fl.isVB_gr i⟩
  have e := VMetric.isometric_det_tens_det k X p (VMetric.stepSeq fl i) i 1 (h.stepMet fl i)
    (H.restrict _ _) (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i) hf
  refine (HermLB.Isometric.tens_right ?_ _).trans e
  refine HermLB.isometric_of_chart (fun c => c) (fun _ => le_rfl) (fun x c c' _ _ => rfl) fun σ c y hy => ?_
  change -Real.log ((((h.stepMet fl i).met σ).restrict hf (fl.isVB i.castSucc)).G c y).det.re =
    -Real.log (((h.met σ).restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc)).G c y).det.re
  have key : ∀ t : Γ(fl.F i.castSucc, c.U), (fl.ι i.succ).app c.U ((fl.step i).app c.U t) =
      (fl.ι i.castSucc).app c.U t := fun t => by
    rw [← fl.step_ι i]; rfl
  have eG : (((h.stepMet fl i).met σ).restrict hf (fl.isVB i.castSucc)).G c y =
      ((h.met σ).restrict (fl.isSubbundle i.castSucc) (fl.isVB i.castSucc)).G c y := by
    ext a b
    exact ((h.met σ).form_restrict (fl.isSubbundle i.succ) (fl.isVB i.succ) _ _ hy).trans
      (congrArg₂ (fun s t => (h.met σ).form s t y) (key (c.e a)) (key (c.e b)))
  rw [eG]

theorem gdeg_tens (HC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (hp : IsArithVar p 1) (L M : HermLB p) : gdeg (L.tens M) 1 = gdeg L 1 + gdeg M 1 := by
  obtain ⟨Ψ, hΨ⟩ := ((HC.arExists k X p 1 hp).2 (Fin 2) ![L, M]).2
  have e₀ := hΨ.1 (Pi.single 0 1)
  have e₁ := hΨ.1 (Pi.single 1 1)
  have e₂ := hΨ.1 (Pi.single 0 1 + Pi.single 1 1)
  rw [HermLB.Isometric.gdeg_eq (ArInt.isometric_comb_single ![L, M] 0) 1] at e₀
  rw [HermLB.Isometric.gdeg_eq (ArInt.isometric_comb_single ![L, M] 1) 1] at e₁
  rw [HermLB.Isometric.gdeg_eq (ArInt.isometric_comb_add ![L, M] (Pi.single 0 1) (Pi.single 1 1)) 1,
    HermLB.Isometric.gdeg_eq ((ArInt.isometric_comb_single ![L, M] 0).tens
      (ArInt.isometric_comb_single ![L, M] 1)) 1] at e₂
  simp only [GlobalTheory.ThetaRR.Elim.lin_single, pow_one] at e₀ e₁
  have hl : (lin fun i => (((Pi.single (0 : Fin 2) (1 : ℤ) + Pi.single 1 1 : Fin 2 → ℤ) i : ℤ) : ℝ)) =
      MvPolynomial.X 0 + MvPolynomial.X 1 := by
    simp [lin, Fin.sum_univ_two, Pi.single_apply]
  rw [hl, pow_one, map_add, e₀, e₁] at e₂
  simpa using e₂.symm

theorem sum_gdeg_grLB (HC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (hp : IsArithVar p 1) {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) :
    ∑ i, gdeg (VMetric.grLB fl i H) 1 = gdeg (VMetric.det H) 1 := by
  let g : ℕ → ℝ := fun j => if hj : j < r + 1 then
    gdeg (VMetric.det (H.restrict (fl.isSubbundle ⟨j, hj⟩) (fl.isVB ⟨j, hj⟩))) 1 else 0
  have step (i : Fin r) : gdeg (VMetric.grLB fl i H) 1 = g (i + 1) - g i := by
    have e := (isometric_det_tens_grLB' H fl i).gdeg_eq 1
    rw [gdeg_tens HC hp] at e
    simp only [g, dif_pos (show (i : ℕ) + 1 < r + 1 by omega), dif_pos (show (i : ℕ) < r + 1 by omega)]
    exact eq_sub_of_add_eq' e
  have h0 : g 0 = 0 := by
    simp only [g, dif_pos (show 0 < r + 1 by omega)]
    exact gdeg_det_rank_zero HC hp _
  have hr : g r = gdeg (VMetric.det H) 1 := by
    simp only [g, dif_pos (show r < r + 1 by omega)]
    exact (isometric_det_last H fl).gdeg_eq 1
  rw [Finset.sum_congr rfl fun i _ => step i, Fin.sum_univ_eq_sum_range (fun j => g (j + 1) - g j),
    Finset.sum_range_sub, h0, hr, sub_zero]

theorem isFlagCh2_scale : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ (E : S.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (a s : ℝ), VMetric.IsFlagCh2 H fl a → VMetric.IsFlagCh2 (H.scale s) fl (a - s / 2 * gdeg (VMetric.det H) 1) := by
  intro HC k _ S p _ hS E r h H fl a s ha
  have hp : IsArithVar p 1 := hS.toIsArithVar
  obtain ⟨hfin, x, hx, rfl⟩ := ha
  obtain ⟨hF, hB⟩ := flagBc_scale H fl s
  refine ⟨hF.2 hfin, fun i => x i - s * gdeg (VMetric.grLB fl i H) 1, fun i => ?_, ?_⟩
  · have h1 := HC.arShift k S p 1 hp (VMetric.grLB fl i H) (x i) (-s / 2) (hx i)
    have h2 := (isometric_grLB_scale H fl i s).symm.isSelfInter hp h1
    convert h2 using 1
    push_cast
    ring
  · rw [hB, ← sum_gdeg_grLB HC hp H fl, Finset.mul_sum]
    have e (i : Fin r) : (x i - s * gdeg (VMetric.grLB fl i H) 1) / 2 =
        x i / 2 - s / 2 * gdeg (VMetric.grLB fl i H) 1 := by ring
    simp only [e, Finset.sum_sub_distrib]
    ring

end GlobalTheory.FlagScale
