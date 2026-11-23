import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullOfXiRec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleChar
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTopOfCore
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistHeckeCharacter

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.RunOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val_eq (D : D7) (y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ((cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  have h : D.conjF = D.sp.cm.sig :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin sigR
  rw [h]
  rfl

theorem xi_det_of_isDetRoot {D : D7} {xi de : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (h : XiTilde xi de)
    (V : Formalism.BasicNotions.TH.HSp D) (g : Formalism.L2.Theta.GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.IsDetRoot V g x) :
    xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom V g)) =
      de (Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x) := by
  rw [← GlobalTheory.AntiCycRead.quo_of_isDetRoot D V g x hx, ← h]
  congr 1
  apply GlobalTheory.AntiCycRead.quo_eq_of
  have e : (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) =
      ((Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := rfl
  rw [e, ← cjFin_val_eq, ← Units.val_mul, div_mul_cancel]

theorem exists_run_pins : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ hC l hl

  obtain ⟨δ, hδdef⟩ : ∃ δ : Formalism.L2.Host.HChar D.host.E, δ = if l = D.host.pde then (R2 p).C.del else (R2 p).C.del' :=
    ⟨_, rfl⟩
  have hδ : Formalism.L2.Host.IsDelta (H := D.host) l δ := by
    rcases hl with rfl | rfl
    · rw [hδdef, if_pos rfl]; exact (R2 p).C.isDel
    · rw [hδdef, if_neg D.host.pde_ne.symm]; exact (R2 p).C.isDel'
  have hδv : ∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D := by
    intro x
    by_cases h : l = D.host.pde
    · rw [hδdef, if_pos h]; exact hC.delVal x
    · rw [hδdef, if_neg h]; exact hC.delVal' x
  obtain ⟨χ, de, hχ, hd, hfin⟩ := GlobalTheory.TameFinitePart.exists_xiRec D l δ hl hδ hδv
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D l := by
    rcases hl with rfl | rfl
    exacts [hC.field₁, hC.field₂]

  obtain ⟨Pk, hPk⟩ := hC.oneHalf
  obtain ⟨P, hP, hPv⟩ : ∃ P : HeightOneSpectrum (𝓞 D.host.K), ((l : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal ∧
      ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ PP ∈ placesOver (R2 p) ((R2 p).mu v) (ownAt D v),
        P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
    by_cases hex : ∃ v ∈ (R2 p).twPl, ownAt D v = l
    · obtain ⟨v, hv, hvl⟩ := hex
      refine ⟨Pk l, by rw [← hvl]; exact (hPk v hv).1, fun w hw hwl PP hPP => ?_⟩
      have := (hPk w hw).2 PP hPP
      rwa [hwl] at this
    · have hlp : l.Prime := by
        rcases hl with rfl | rfl
        exacts [D.host.pde_prime, D.host.pde'_prime]
      obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hlp
      exact ⟨P, hP, fun w hw hwl => absurd ⟨w, hw, hwl⟩ hex⟩

  have hJ : LawsJ p.T := (fw2 p).laws
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D p.T.toCore hC.laws hC.rank hF.kpsi
  have hcan : T.Q.Canon := by
    have e : T.toCore.Q = p.T.toCore.Q := congrArg (fun C => C.Q) hTc
    rw [show T.Q = p.T.Q from e]
    exact hC.canon
  obtain ⟨dd, TF, hTF, -, hJ', hxi, hh, hcov⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiRec D p.T T hJ hT hTc hcan l hF P hP de hd
  obtain ⟨r, rfl⟩ : ∃ r : GlobalTheory.RealIndexBound.RunData p.T, r.full = TF := by
    rw [← hJ']
    exact ⟨GlobalTheory.RealIndexBound.RunData.of TF, rfl⟩
  have hInR : ∀ i : Fin D.R.m, InR D ((i : ℕ) + 1) := fun i => ⟨Nat.le_add_left _ _, i.2⟩
  refine ⟨r, hTF, fun i => (hcov _ (hInR i)).1, fun j n hj => (hcov j hj).2 n, ?_, ?_⟩
  · intro i γ₀ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D _).2.2.1 γ₀ hγ
    rw [xi_det_of_isDetRoot hxi _ _ _ hx]
    exact hd.rat _ x rfl
  · intro v hv hvl i
    letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hvl]
      exact (hcov _ (hInR i)).2 _
    · intro PP hPP
      rw [hh]
      exact hPv v hv hvl PP hPP
    · have hδv' : (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = δ := by
        unfold ownAt at hvl
        unfold Formalism.L2.Host.CharFrame.delAt
        by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
        · rw [if_pos h] at hvl ⊢
          rw [hδdef, ← hvl, if_neg D.host.pde_ne.symm]
        · rw [if_neg h] at hvl ⊢
          rw [hδdef, ← hvl, if_pos rfl]
      refine ⟨χ, hδv' ▸ hχ, fun g x hx => ?_⟩
      rw [xi_det_of_isDetRoot hxi _ _ _ hx]
      exact hfin x _ rfl

end GlobalTheory.RunOnto
