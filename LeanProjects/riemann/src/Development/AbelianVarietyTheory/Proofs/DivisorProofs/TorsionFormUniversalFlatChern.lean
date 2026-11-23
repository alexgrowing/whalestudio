import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMetricChernFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff Real

namespace GlobalTheory.UnivPullback

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

variable {g : ℕ}

theorem tauU_symPart {A : Matrix (Fin g) (Fin g) ℂ} (h : A.IsSymm) : tauU (symPart A) = A := by
  ext i j
  simp only [tauU, symPart, Matrix.of_apply]
  rw [h.apply i j]
  ring

theorem stdLat_int {l : Fl g} (hl : l ∈ stdLat g) (i : Fin g ⊕ Fin g) : ∃ k : ℤ, l i = k := by
  obtain ⟨k, hk⟩ := ((Pi.basisFun ℝ (Fin g ⊕ Fin g)).mem_span_iff_repr_mem ℤ l).1 hl i
  exact ⟨k, by simpa using hk.symm⟩

theorem riem_int : ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∃ k : ℤ, riem l l' = k := by
  intro l hl l' hl'
  choose a ha using stdLat_int hl
  choose a' ha' using stdLat_int hl'
  exact ⟨∑ i, (a (Sum.inr i) * a' (Sum.inl i) - a (Sum.inl i) * a' (Sum.inr i)), by
    simp [riem, ha, ha']⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem transl_zero (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : transl τ 0 P = P := by
  have e := GlobalTheory.FlatRigidity.per_add (τ P.1) 0 0
  simp only [add_zero] at e
  have e0 : per (τ P.1) 0 = 0 := by
    have := congrArg (fun v => v - per (τ P.1) 0) e
    simpa using this.symm
  simp [transl, e0]

theorem isFactor_translPull [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}
    (hj : IsFactor B τ M j) (x : Fl g) : IsFactor B τ M (translPullFactor τ x j) := by
  refine ⟨fun l hl => ⟨?_, fun P hP => hj.1 l hl |>.2 _ (GlobalTheory.FlatRigidity.transl_mem τ x hP)⟩,
    fun l hl l' hl' P hP => ?_⟩
  · exact (hj.1 l hl).1.comp (GlobalTheory.FlatRigidity.differentiableOn_transl hτ x)
      fun P hP => GlobalTheory.FlatRigidity.transl_mem τ x hP
  · simp only [translPullFactor]
    have hc : transl τ x (transl τ l' P) = transl τ l' (transl τ x P) := by
      rw [GlobalTheory.FlatRigidity.transl_transl, GlobalTheory.FlatRigidity.transl_transl, add_comm]
    rw [hc]
    exact hj.2 l hl l' hl' _ (GlobalTheory.FlatRigidity.transl_mem τ x hP)

section Congr

variable {B : Set E} {τ τ' : E → Matrix (Fin g) (Fin g) ℂ}

theorem transl_congr (hE : EqOn τ τ' B) (x : Fl g) {P : Pt E g} (hP : P ∈ cov B g) :
    transl τ x P = transl τ' x P := by
  simp only [transl, hE hP.1]

theorem isPeriodMap_congr (h : IsPeriodMap B τ) (hE : EqOn τ τ' B) : IsPeriodMap B τ' :=
  ⟨h.1, fun i j => (h.2.1 i j).congr fun b hb => by simp only [hE hb], fun b hb => hE hb ▸ h.2.2 b hb⟩

theorem isFactor_congr {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} (h : IsFactor B τ M j)
    (hE : EqOn τ τ' B) : IsFactor B τ' M j :=
  ⟨h.1, fun l hl l' hl' P hP => by rw [← transl_congr hE l' hP]; exact h.2 l hl l' hl' P hP⟩

theorem isMetric_congr {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {m : Pt E g → ℝ}
    (h : IsMetric B τ M j m) (hE : EqOn τ τ' B) : IsMetric B τ' M j m :=
  ⟨h.1, h.2.1, fun l hl P hP => by rw [← transl_congr hE l hP]; exact h.2.2 l hl P hP⟩

theorem om0_congr (hB : IsOpen B) (hE : EqOn τ τ' B) {P : Pt E g} (hP : P ∈ cov B g) :
    om0 τ P = om0 τ' P := by
  have hev : flat τ =ᶠ[𝓝 P] flat τ' :=
    Filter.eventually_of_mem ((hB.prod isOpen_univ).mem_nhds hP) fun Q hQ => by
      simp only [flat, hE hQ.1]
  simp only [om0, dflat, hev.fderiv_eq]

theorem chernIsFlat_congr (hB : IsOpen B) {m : Pt E g → ℝ} (h : ChernIsFlat B τ m)
    (hE : EqOn τ τ' B) : ChernIsFlat B τ' m := fun P hP v w => by
  rw [← om0_congr hB hE hP]; exact h P hP v w

end Congr

def symPartCLM (g : ℕ) : (Fin g → Fin g → ℂ) →L[ℂ] symMat g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => symPart A
      map_add' := fun A B => by
        apply Subtype.ext; funext i j; simp only [symPart, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c A => by
        apply Subtype.ext; funext i j
        simp only [symPart, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem differentiableOn_symPart {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) : DifferentiableOn ℂ (fun x => symPart (τ x)) B := by
  have h1 : DifferentiableOn ℂ (fun x => fun i j => τ x i j) B :=
    differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hτ.2.1 i j
  exact ((symPartCLM g).differentiable.comp_differentiableOn h1).congr fun _ _ => rfl

end GlobalTheory.UnivPullback

namespace GlobalTheory.UnivPullback

open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

theorem torsion_eq_univ : Naturality → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (g : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ)
    (j : Fl g → Pt E g → ℂ) (m : Pt E g → ℝ), Convex ℝ B → IsDatum B τ (stdLat g) j m →
    ChernIsFlat B τ m → ∀ b ∈ B, ∀ (e : E) (T : Ext (1 + 1)),
    IsTorsionForm τ (stdLat g) j m ![e] b T →
    IsUnivTorsion g (symPart (τ b)) (fderiv ℂ (fun x => symPart (τ x)) b e) T := by
  rintro ⟨hBC, -, hIso, hTr, -, -, -⟩ E _ _ _ g B τ j m hcvx hD hC b hb e T hT
  obtain ⟨hτ, hLat, hF, hM⟩ := hD

  set τ' : E → Matrix (Fin g) (Fin g) ℂ := fun x => tauU (symPart (τ x)) with hτ'
  have hE : EqOn τ τ' B := fun x hx => (tauU_symPart (hτ.2.2 x hx).1).symm
  have hτP : IsPeriodMap B τ' := isPeriodMap_congr hτ hE
  have hF' : IsFactor B τ' (stdLat g) j := isFactor_congr hF hE
  have hM' : IsMetric B τ' (stdLat g) j m := isMetric_congr hM hE
  have hC' : ChernIsFlat B τ' m := chernIsFlat_congr hτ.1 hC hE
  have hT' : IsTorsionForm τ' (stdLat g) j m ![e] b T :=
    GlobalTheory.T.isTorsionForm_congr_of_eventuallyEq E g 1 τ τ' (stdLat g) j m ![e] b T
      (Filter.eventually_of_mem (hτ.1.mem_nhds hb) fun x hx => hE hx) hT

  have hθF := (theta_factor hτP).1
  have hθM := GlobalTheory.T.theta_metric_chern_flat hτP
  haveI : SimplyConnectedSpace B := by
    haveI := hcvx.contractibleSpace ⟨b, hb⟩
    infer_instance
  obtain ⟨x, ψ, hψ, hψi⟩ := GlobalTheory.T.period_map_rigidity hτP ‹_› (stdLat g) hLat riem_int _ j _ m hθF hθM.1
    hθM.2 hF' hM' hC'
  have hTM := GlobalTheory.T.metric_translation_pullback_flat hτP (stdLat g) _ _ hθM.1 hθM.2 x
  have hD1 := (⟨hτP, hLat, isFactor_translPull hτP hθF x, hTM.1⟩ :
    IsDatum B τ' (stdLat g) (translPullFactor τ' x _) _)
  have h1 := hIso E g 1 B τ' (stdLat g) j _ m _ ψ ⟨hτP, hLat, hF', hM'⟩ hD1 hψ hψi ![e] b hb T hT'
  have h2 := hTr E g 1 B τ' (stdLat g) _ _ hD1 (-x) ![e] b hb T h1
  have e0 : ∀ P : Pt E g, transl τ' x (transl τ' (-x) P) = P := fun P => by
    rw [GlobalTheory.FlatRigidity.transl_transl, add_neg_cancel, transl_zero]
  have e1 : translPullFactor τ' (-x) (translPullFactor τ' x
      fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ' P.1) l P.2)) =
      fun l P => Complex.exp (2 * π * Complex.I * thetaExp (τ' P.1) l P.2) := by
    funext l P; simp only [translPullFactor, e0]
  rw [e1] at h2
  simp only [e0] at h2

  obtain ⟨hU, -⟩ := GlobalTheory.T.siegel_period_map_simply_connected g
  have hDU : IsDatum (siegel g) tauU (stdLat g) _ _ :=
    ⟨hU, hLat, (theta_factor hU).1, (GlobalTheory.T.theta_metric_chern_flat hU).1⟩
  have hφm : MapsTo (fun x => symPart (τ x)) B (siegel g) := fun x hx => by
    show IsSiegel (tauU (symPart (τ x)))
    rw [tauU_symPart (hτ.2.2 x hx).1]
    exact hτ.2.2 x hx
  have h4 := (hBC (symMat g) E g 1 (siegel g) tauU (stdLat g) _ _ hDU B (fun x => symPart (τ x))
    hτ.1 (differentiableOn_symPart hτ) hφm ![e] b hb T).1 h2
  refine ⟨_, _, hDU, (GlobalTheory.T.theta_metric_chern_flat hU).2, ?_⟩
  have e3 : (fun i => fderiv ℂ (fun x => symPart (τ x)) b (![e] i)) =
      ![fderiv ℂ (fun x => symPart (τ x)) b e] := by
    funext i; fin_cases i; rfl
  rw [e3] at h4
  exact h4

end GlobalTheory.UnivPullback
