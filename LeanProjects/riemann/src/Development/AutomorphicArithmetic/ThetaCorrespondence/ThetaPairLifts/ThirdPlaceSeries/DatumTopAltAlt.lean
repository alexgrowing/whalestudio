import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataTopStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedVacuumStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTailStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.DatumTopAt
section Gen
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
end Gen
end GlobalTheory.DatumTopAt
namespace GlobalTheory.DatumTopAt
theorem datum_top_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) ∧ ((omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h))) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j h d₀ hd₀
  have hψ : IsStdChar D (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := hd₀.2.1.1
  obtain ⟨hΛ, hΛX, M, hM, hMv, hg0⟩ := _root_.GlobalTheory.T.descent_top_self_dual_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT j h d₀ hd₀
  obtain ⟨Lp, κ, hκ, hq, hint, heGT, hdat⟩ := _root_.GlobalTheory.T.descent_top_step_vector_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR
    j h d₀ hd₀ hΛ hΛX M hM hMv
  have hNT : v.NT = f.g.LT := hVT.bT.2
  have hLT : IsSelfDualC D.sp.X' f.g.LT := hNT ▸ hv.sdT
  have hinj : Function.Injective fun i => (Lp i).q.v := fun i i' e => hGP.inj ((hq i).symm.trans (e.trans (hq i')))
  generalize hg : omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) = g₀ at hg0 hdat ⊢
  have hcomb : ∀ i, GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).o ∧ GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).e :=
    fun i => locPl_combAt (Lp i)
  have hplace : ∀ i, (Lp i).q.v ∈ v.gP := fun i => (hGP.places _).2 ⟨i, hq i⟩
  have hoP : ∀ i, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (Lp i).o := fun i =>
    combAt_mono' (fun p (hp : p = (Lp i).q.v) => hp ▸ hplace i) (hcomb i).1
  obtain ⟨o', ho', ho'eq⟩ := comp_list (ψ := f.c.ψ) (S := Yc D (j + 1)) (T := D.sp.X') hψ (· ∈ v.gP) (fun i => (Lp i).o) hoP
    (List.finRange n)
  obtain ⟨F₀, hF₀, hF₀t, -⟩ := hdat d₀ hd₀
  have hoff : ∀ p, (∀ i, p ≠ (Lp i).q.v) → GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) =
      GlobalTheory.FinPl.latV (Yc D (j + 1)) M (· = p) ∧ GlobalTheory.FinPl.latV D.sp.X' v.NT (· = p) = GlobalTheory.FinPl.latV D.sp.X' f.g.LT (· = p) := by
    intro p hp
    have hpg : p ∉ v.gP := fun hm => by
      obtain ⟨i, hi⟩ := (hGP.places p).1 hm
      exact hp i (hi.trans (hq i).symm)
    exact ⟨latV_eq_of_moves (hv.sd (j + 1) (by omega)).1 hM.1
      (hVT.moves (j + 1) (by omega) (· = p) fun p' (hp' : p' = p) => hp' ▸ hpg) (hMv _), by rw [hNT]⟩
  have hNvac := (GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hψ _ _ M f.g.LT hM hLT n Lp hinj g₀ F₀ hg0 hF₀ hF₀t).2 (v.N (j + 1)) v.NT
    (hv.sd (j + 1) (by omega)) hv.sdT hint hoff
  have hre := comm_list hψ (fun i => (Lp i).q.v) hinj (fun i => (Lp i).o) (fun i => (Lp i).e) (fun i => (hcomb i).1)
    (fun i => (hcomb i).2) (List.finRange n) (List.nodup_finRange n)
  have hth : IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' (comb f.c.ψ _ _ o' g₀) := by
    rw [ho'eq]; exact hNvac.1
  have hkey : ∀ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (Lp i).q.e)
      (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 g₀ (prodDat Lp) F →
      IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F → F = comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' g₀) := by
    intro F hF hFt
    rw [(GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hψ _ _ M f.g.LT hM hLT n Lp hinj g₀ F hg0 hF hFt).1, hre, heGT _ hth, ho'eq]
  refine ⟨M, f.g.LT, o', hM, hLT, ho', vac_mono' _ hg0, ?_, ?_, κ, hκ, ?_⟩
  · rw [ho'eq]; exact vac_mono' _ hNvac
  · intro hne
    rw [ho'eq]
    exact GlobalTheory.T.seesawCombinations_composite_ne_zero_of_vacuum D f.c.ψ hψ _ _ M f.g.LT hM hLT n Lp hinj g₀ hg0 hne
  · intro d hd
    obtain ⟨F, hF, hFt, heq⟩ := hdat d hd
    rw [heq, hkey F hF hFt]
end GlobalTheory.DatumTopAt
end
end
