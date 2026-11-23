import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

namespace GlobalTheory.BotMove.Fst

private theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

private theorem placeModel_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) (c : ℂ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) (c • Tm) := by
  have hs : ∀ x (F : WO S T → ℂ), heisO ψ S T x (c • F) = c • heisO ψ S T x F := fun x F => by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.trans Φ hΦ x hx]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.modul Φ hΦ y hy]
  · rw [LinearMap.smul_apply, h.vac]

private theorem thetaAt_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ Φ f : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ (c⁻¹ • f) := by
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := h
  refine ⟨⟨c⁻¹ • T₀, ?_⟩, fun T' hT' => ?_⟩
  · have := placeModel_smul hT₀ c⁻¹
    rwa [inv_smul_smul₀ hc] at this
  · have e1 : f = (c • T') Φ := hall _ (placeModel_smul hT' c)
    show c⁻¹ • f = T' Φ
    rw [e1, LinearMap.smul_apply, inv_smul_smul₀ hc]

private theorem thetaAt_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ')
    (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : GlobalTheory.FinPl.Moves S b Λ M (fun _ => True))
    (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' (fun _ => True)) {e : AE D} {Φ f₀ f : WO S T → ℂ} (hee : e * e = e)
    (hinf : infPart D e = 0) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀)
      (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

private theorem frMapO_move {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (g : GA D S) (h : GA D T) (x : WO S T) :
    frMapO S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have e1 : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((Lev.finE T h)⁻¹).val := by
    rw [← map_inv]; rfl
  have e2 : (Formalism.L2.Theta.mt S g).map (toEAf D) = (Lev.finE S g).val := rfl
  rw [frMapO, frMapO, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, e1, e2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem stdFst_move {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) :
    stdFst ν e I S T (Lev.finE S g * βS) (Lev.finE T h * βT) = fun x => stdFst ν e I S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  funext x
  unfold stdFst
  rw [frMapO_move, GlobalTheory.SchrMove.isHalf_actO_iff g⁻¹ h⁻¹ x]

end GlobalTheory.BotMove.Fst

theorem _root_.GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) (latO (neg A) WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac
    (stdFst (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA _ hW g _ g' _ h _ mA _ mW t₀ r r' hr hv _ t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hY.idem t)
  have mA' : GlobalTheory.FinPl.Moves (neg A) ((ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mA
  have h1 := GlobalTheory.BotMove.Fst.thetaAt_move (S := neg A) (hY.weil t) (GlobalTheory.BotMove.Fst.selfDual_neg hY.rigA.1)
    (GlobalTheory.BotMove.Fst.selfDual_neg hA) hY.rigW.1 hW mA' mW ho.idem ho.infPart_eq hY.isVac.2.theta (hY.fst t)
  have e1 : ∀ F, (Y.ω t).toSgn true ((ofSgn true A).symm g, h) F = Y.ω t (g, h) F := fun F => rfl
  rw [e1, e1, hv t] at h1
  have h2 := GlobalTheory.BotMove.Fst.thetaAt_smul (hr t).1 h1
  have e2 := GlobalTheory.BotMove.Fst.stdFst_move (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β g h
  show IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (Y.e t) (latO (neg A) WW ΛA ΛW fun _ => True) 1 (Y.ω t₀ (g, h) Y.vac)
    (stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW (Lev.finE A g * Y.rA.β) (Lev.finE WW h * Y.rW.β))
    ((r t)⁻¹ • Y.ω t (g, h) (Y.f t))
  rw [e2]
  exact h2
