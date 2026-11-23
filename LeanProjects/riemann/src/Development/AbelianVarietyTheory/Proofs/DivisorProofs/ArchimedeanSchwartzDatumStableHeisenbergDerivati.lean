import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtHeisenbergTranslateFockBoxStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigNZ.DatRealStable

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem schr_schr_apply {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) (x : κ → R) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' f) x =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) * GlobalTheory.WeilM.schr ψ (w + w') f x := by
  simp only [GlobalTheory.WeilM.schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  rw [dotProduct_comm w'.1 w.2]
  first
    | linear_combination (w.1 ⬝ᵥ w'.2) * invOf_mul_self (2 : R)
    | linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

theorem sum_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} (a : PolT G p →₀ ℂ) (τ : TotT G p) (g : PureT G p → ℂ) :
    (tensT W a τ).sum (fun d c => c * g d) =
      a.sum fun P c => τ.sum fun d c' => c * c' * g (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) := by
  unfold tensT
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun P _ => ?_
  beta_reduce
  rw [Finsupp.sum_sum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  refine Finset.sum_congr rfl fun d _ => ?_
  beta_reduce
  rw [Finsupp.sum_single_index (zero_mul _)]

theorem datum_stable : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W) (h : IsTripleOf W M t i j e Bs Γ X), IsTriple Bs Γ X om om' → ∀ n Φ τ τ', HasFlip B t ρ i j n Φ τ τ' →
    ∀ φ, IsFinPart Γ.M X.T φ → ∀ (f : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank))) a, IsDatumA W e Γ (tensT W a τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → ∀ f₁ : SInf D.host.F (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Γ.M.heisLine Bs.ψ u) f f₁ →
    ∃ a', IsDatumA W e Γ (tensT W a' τ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ) := by
  intro D T L sc G μ₀ hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f a ha u hu f₁ h1
  change TotT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) at τ
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  have hFr : IsTotallyReal D.host.F := hT.base.cm.1
  have hψc : IsCharAF D.host.F W.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hψ
  have hstd := (hT.geo.hM.std.and (Finset.finite_toSet X.T).compl_mem_cofinite).mono
    fun v hv => (hφ.2 v hv.2).trans hv.1
  have hrest := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ.1 hstd
  have hmem1 := GlobalTheory.TensUniq.pure_mem_schA f₁ φ hφ.1 hstd
  have hd : ∀ x, HasDerivAt (fun s : ℝ => Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ x) 0 := by
    intro x
    rw [← h.ψ]
    exact h1 _ hrest x
  choose b hb using fun P => GlobalTheory.T.hasDerivAt_heisenbergTranslate_fockBox hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF u hu P
  refine ⟨a.sum fun P c => c • b P, hmem1, fun v => ?_⟩
  have H1 := GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho Γ.M.co W.ψ hFr hψc u _ ha.1 _ hmem1 hd v
  set g : PolT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) → PureT G (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.routeA t i j) → _ → ℂ :=
    fun P d => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.boxA e (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) with hg
  set ph : ℝ → ℂ := fun s => W.ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).2 -
        (Γ.M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)).1 ⬝ᵥ (Γ.M.co.e v).2)) with hph
  have e1 : ∀ s : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ v (Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) = ∑ P ∈ a.support, ∑ d ∈ τ.support,
        a P * τ d * (ph s * g P d (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)) := by
    intro s
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ v (Γ.M.co.rho W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) = ph s * GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho W.ψ
          (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) := by
      unfold GlobalTheory.WeilM.thetaSum
      rw [← tsum_mul_left]
      refine tsum_congr fun ξ => ?_
      simp only [GlobalTheory.WeilM.Darboux.rho, map_add]
      exact schr_schr_apply W.ψ _ _ _ _
    rw [e2, ha.2, sum_tensT, Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hg]
    ring
  have H2 : HasDerivAt (fun s : ℝ => ∑ P ∈ a.support, ∑ d ∈ τ.support,
        a P * τ d * (ph s * g P d (v + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u)))
      (∑ P ∈ a.support, ∑ d ∈ τ.support, a P * τ d * (b P).sum fun P' c => c * g P' d v) 0 :=
    HasDerivAt.fun_sum fun P _ => HasDerivAt.fun_sum fun d hd => (hb P d hd v).const_mul (a P * τ d)
  rw [← funext e1] at H2
  rw [H1.unique H2, sum_tensT, Finsupp.sum_sum_index (fun _ => by simp) (fun _ _ _ => by simp only [add_mul, Finsupp.sum_add])]
  refine Finset.sum_congr rfl fun P _ => ?_
  beta_reduce
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P' _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [hg, smul_eq_mul]
  ring

end GlobalTheory.BigNZ.DatRealStable
