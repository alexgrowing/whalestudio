import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal

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

noncomputable section

namespace GlobalTheory.BotMoveSnd

variable {D : D7}

theorem heisO_smul' {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) (ζ : ℂ) (g : WO S T → ℂ) :
    heisO ψ S T w (ζ • g) = ζ • heisO ψ S T w g := by
  funext x
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem isPlaceModel_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ}
    (a : ℂ) {g₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c g₀ Tm) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (a • g₀) (a • Tm) :=
  { trans := fun Φ hΦ x hx => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.trans Φ hΦ x hx, heisO_smul']
    modul := fun Φ hΦ y hy => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, hT.modul Φ hΦ y hy, heisO_smul']
    vac := by rw [LinearMap.smul_apply, hT.vac] }

theorem isThetaAt_rescale {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)} {c κ : ℂ}
    {f₀ Φ f : WO S T → ℂ} (hκ : κ ≠ 0) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (κ • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ (κ⁻¹ • f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  refine ⟨⟨κ⁻¹ • Tm, ?_⟩, fun Tm' hT' => ?_⟩
  · have := isPlaceModel_smul κ⁻¹ hT
    rwa [smul_smul, inv_mul_cancel₀ hκ, one_smul] at this
  · rw [hall _ (isPlaceModel_smul κ hT'), LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem isHalf_iff_smul {m n : ℕ} (c : AE D) (u : Mx D m n) : IsHalf c u ↔ c • u = u :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem isHalf_actO' {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf c x) :
    IsHalf c (actO S T g h x) := by
  rw [isHalf_iff_smul] at hx ⊢
  rw [GlobalTheory.VacMove.actO_eq]
  conv_rhs => rw [← hx]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_actO_inv_iff {S T : HSp D} (c : AE D) (g : GA D S) (h : GA D T) (x : WO S T) :
    IsHalf c (actO S T g⁻¹ h⁻¹ x) ↔ IsHalf c x := by
  refine ⟨fun hx => ?_, isHalf_actO' c _ _⟩
  have := isHalf_actO' c g h hx
  have e := GlobalTheory.SplitHecke.actO_inv_actO (S := S) (T := T) g⁻¹ h⁻¹ x
  simp only [inv_inv] at e
  rwa [e] at this

theorem frame_move_alg {R : Type} [CommRing R] {s t : ℕ} (a βS : GL (Fin s) R) (b βT : GL (Fin t) R)
    (K : Matrix (Fin s) (Fin t) R) :
    ((a * βS)⁻¹ : GL (Fin s) R).1 * K * (b * βT).1 =
      (βS⁻¹).1 * (a⁻¹).1 * βS.1 * ((βS⁻¹).1 * K * βT.1) * ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R).1 := by
  have e1 : (βS.1 : Matrix (Fin s) (Fin s) R) * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : (βT.1 : Matrix (Fin t) (Fin t) R) * (βT⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e3 : ((βT⁻¹ * b⁻¹ * βT)⁻¹ : GL (Fin t) R) = βT⁻¹ * b * βT := by group
  rw [e3, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1 (βS⁻¹).1, e1, Matrix.one_mul, ← Matrix.mul_assoc βT.1 (βT⁻¹).1, e2, Matrix.one_mul]

theorem frMapAdj_move (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D S)
    (h : GA D T) (x : WO S T) :
    frMapAdj S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapAdj S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have split : actO S T g⁻¹ h⁻¹ x = actO S T g⁻¹ 1 (actO S T 1 h⁻¹ x) := by
    simp only [GlobalTheory.VacMove.actO_eq, inv_one, GlobalTheory.VacMove.mt_one₀, Matrix.one_mul, Matrix.mul_one]
  rw [split, GlobalTheory.FreeBlockTwist.frMapAdj_actO_one, GlobalTheory.AdjAct.frMapAdj_actO, ← GlobalTheory.AdjAct.finE_inv_val, ← map_inv]
  unfold frMapAdj
  rw [map_inv (Lev.finE S), map_inv (Lev.finE T), ← Matrix.mul_assoc]
  exact frame_move_alg (R := EAf D) (Lev.finE S g) βS (Lev.finE T h) βT _

theorem stdSnd_move (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) (x : WO S T) :
    stdSnd ν e I a S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = stdSnd ν e I a S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  unfold stdSnd dualCoord
  rw [frMapAdj_move]
  rw [propext (isHalf_actO_inv_iff (cA D e) g h x)]

theorem snd_moved : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
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
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv' t
  have hWe : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := (GlobalTheory.Grid.isWeil_false ψ A' WW _ _ _).1 (hY.weil' t)
  have hee : cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := by
    rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self (hY.idem t)]
  have hinf : infPart D (cA D (Y.e t)) = 0 :=
    GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum (hY.idem t))
  have hm := GlobalTheory.VacMove.isThetaAt_moveLat D ψ A' WW (α t) (α t / β t) (Y.ω' t) hWe Y.rA'.Λ ΛA' Y.rW.Λ ΛW hY.rigA'.1 hA'
    hY.rigW.1 hW g' hg' h hh mA' mW (cA D (Y.e t)) _ Y.vac' (Y.f' t) hee hinf hY.isVac'.2.theta
    (GlobalTheory.ConstRatio.theta_f hY t).2 (hY.snd t)
  rw [hv' t] at hm
  have hm2 := isThetaAt_rescale (hr t).2 hm
  have hΦ : (fun x => stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β (actO A' WW g'⁻¹ h⁻¹ x)) =
      stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW (Lev.finE A' g' * Y.rA'.β) (Lev.finE WW h * Y.rW.β) :=
    funext fun x => (stdSnd_move _ _ _ _ _ _ _ _ _ _ x).symm
  rw [hΦ] at hm2
  exact hm2

end GlobalTheory.BotMoveSnd

end
