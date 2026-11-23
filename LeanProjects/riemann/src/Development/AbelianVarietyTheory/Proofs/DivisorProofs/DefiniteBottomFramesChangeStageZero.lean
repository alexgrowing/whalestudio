import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulCutSubOneEntry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicUnitarySplitPlaceComponent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LawsRescaleWithS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareCharQuotientFiniteUnitIdeleRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaPairSecondIsSchwartzBruhatConjHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaPairFirstFrameChangeUnitTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardThetaPairSecondFrameChangeUnitTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryStabilizerTransitionSelfDualFrames

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomFrames
theorem away_of_root {K : Type} [Field K] (ζ : K) (n : ℕ) (hn : 0 < n) (hζ : ζ ^ n = 1) (m : ℕ) :
    GlobalTheory.Square.IsAwayUnit m ζ := by
  have hi : IsIntegral ℤ ζ := IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one)
  set a : 𝓞 K := ⟨ζ, hi⟩ with ha
  have h1 : (a : K) = ζ := rfl
  refine ⟨a, 0, 0, ?_, by rw [pow_zero, mul_one, h1]⟩
  rw [pow_zero]
  refine ⟨a ^ (n - 1), ?_⟩
  apply RingOfIntegers.ext
  push_cast [h1]
  rw [← pow_succ', Nat.sub_add_cancel hn, hζ]

theorem ratio_alg {u1 u2 a b : ℂ} (h2 : u2 ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    u1 * (a / b) / u2 = (u1 * b⁻¹) / (u2 * a⁻¹) := by
  field_simp

theorem const_alg {c1 c2 c x : ℂ} (h2 : c2 ≠ 0) : c1 * (c * x) = c1 / c2 * c * (c2 * x) := by
  field_simp
end GlobalTheory.BottomFrames

namespace GlobalTheory.BottomFrames

theorem compAt_supp {D : D7} (θ : InfFam D) {e : AE D} (he : infPart D e = 0) {V : HSp D} {k : GA D V}
    (hk : SuppAt e V k) (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_mt_one θ τ V
  rw [GlobalTheory.AdelicLatMove.mt_one] at h1
  ext a b
  have e1 : Formalism.L2.Theta.mt V k a b = (e + cA D e) * (Formalism.L2.Theta.mt V k - 1) a b + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) a b := by
    rw [hk a b, Matrix.sub_apply, sub_add_cancel]
  have h2 := congrFun (congrFun h1 a) b
  simp only [compAt, Matrix.map_apply] at h2 ⊢
  have h0 : infPart D (e + cA D e) = 0 := by rw [RingHom.map_add, he, GlobalTheory.PlaceDatum.infPart_cA he, add_zero]
  rw [e1, RingHom.map_add (infPart D), RingHom.map_mul (infPart D), h0, zero_mul, zero_add, h2]

theorem suppAt_one' {D : D7} (e : AE D) (V : HSp D) : SuppAt e V 1 := fun i j => by
  rw [GlobalTheory.AdelicLatMove.mt_one, sub_self]; simp

theorem stabLat_one' {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.StabLat V Λ 1 := fun y => by simp

theorem isDetAt_one' {D : D7} (e : AE D) (V : HSp D) : IsDetAt e V 1 1 := by
  show ((1 : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V 1).det + (1 - e)
  rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]; simp

theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

set_option maxHeartbeats 4000000 in
theorem frames_change : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  Y.rA.Λ = X.rA.Λ → Y.rA'.Λ = X.rA'.Λ → Y.rW.Λ = X.rW.Λ →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ Z.rA.β = X.rA.β ∧ Z.rA'.β = X.rA'.β ∧ Z.rW.β = X.rW.β ∧
    (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW X Y hX hY eA eA' eW
  classical
  obtain ⟨p1, p2, p3, p4, n1, n2, n3, hI⟩ := hY
  have hXI := hX.is
  have fA : Formalism.L2.DIV.IsFrame X.rA.β Y.rA.Λ := eA ▸ hXI.rigA.2.1
  have fA' : Formalism.L2.DIV.IsFrame X.rA'.β Y.rA'.Λ := eA' ▸ hXI.rigA'.2.1
  have fW : Formalism.L2.DIV.IsFrame X.rW.β Y.rW.Λ := eW ▸ hXI.rigW.2.1
  set α : T → ((AE D)ˣ →* Circle) := fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) with hα
  set β : T → ((AE D)ˣ →* Circle) := fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) with hβ
  have hee : ∀ t, Y.e t * Y.e t = Y.e t := fun t => GlobalTheory.PlaceDatum.idemSum_mul_self (hI.idem t)
  choose k hk1 hk2 hk3 hk4 using fun t =>
    GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames (Y.e t) (locPl G t) (hI.idem t) WW Y.rW.Λ hI.rigW.1 Y.rW.β X.rW.β hI.rigW.2.1 fW
  choose x1 hx1 hx1' using fun t => GlobalTheory.T.standardThetaPair_first_frameChange_unitTranslate (α t / β t) (Y.e t) (locPl G t) (hI.idem t) (Y.ideal (locPl G) t) A WW
    Y.rA.Λ Y.rA.β X.rA.β hI.rigA.2.1 fA Y.rW.β X.rW.β (k t) (hk1 t) (hk3 t)
  choose x2 hx2 hx2' using fun t => GlobalTheory.T.standardThetaPair_second_frameChange_unitTranslate (α t / β t) (Y.e t) (locPl G t) (hI.idem t) (Y.ideal (locPl G) t) A.rank
    A' WW Y.rA'.Λ Y.rA'.β X.rA'.β hI.rigA'.2.1 fA' Y.rW.β X.rW.β (k t) (hk1 t) (hk3 t)
  set y : T → (AE D)ˣ := fun t => GlobalTheory.VecInv.detAt (Y.e t) (hee t) WW (k t) with hy
  have hy1 : ∀ t, IsDetAt (Y.e t) WW (k t) (y t) := fun t => GlobalTheory.VecInv.isDetAt_detAt _ _ _ _
  set c1 : T → ℂ := fun t => (((α t / β t) (x1 t) : Circle) : ℂ) * (((β t (y t) : Circle) : ℂ))⁻¹ with hc1
  set c2 : T → ℂ := fun t => (((α t / β t) (x2 t) : Circle) : ℂ) * (((α t (y t) : Circle) : ℂ))⁻¹ with hc2

  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hSdA := selfDual_neg hI.rigA.1
  have hinf : ∀ t, infPart D (Y.e t) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_idemSum (hI.idem t)
  have hinf' : ∀ t, infPart D (cA D (Y.e t)) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_cA (hinf t)
  have hee' : ∀ t, cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := fun t => by rw [← RingHom.map_mul, hee t]
  have hSB : ∀ t, IsSBHalf (Y.e t) (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW Y.rA.β Y.rW.β) := fun t => by
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A) hSdA.1 hI.rigW.1.1 Y.rA.β Y.rW.β
    exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB (hI.weil' t).hecT.1 (hI.idem t) (GlobalTheory.ConstRatio.ideal_ne_bot Y (locPl G) t)
      A WW Y.rA.β Y.rW.β _ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hSdA.1.fg hI.rigW.1.1.fg Y.rA.β Y.rW.β)
      ⟨K, hK, fun t' ht => hC t' (GlobalTheory.PlaceDatum.infPart_of_half (hinf t) ht)⟩
  have hSB' : ∀ t, IsSBHalf (cA D (Y.e t)) (latO A' WW (Y.rA'.Λ : Set (Fin A'.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW Y.rA'.β Y.rW.β) := fun t =>
    GlobalTheory.T.standardThetaPair_second_isSchwartzBruhat_conjHalf _ (hI.weil' t).hecT.1 (Y.e t) (locPl G t) (hI.idem t) _ (GlobalTheory.ConstRatio.ideal_ne_bot Y (locPl G) t) A.rank A' WW
      Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.rA'.β Y.rW.β
  have thY : ∀ t, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (Y.f t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.fst t).1
    rw [(hI.fst t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hψ (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 (Y.e t) (hee t) (hinf t)
      Y.vac hI.isVac.2.theta Tm hTm _ (hSB t)
  have thY' : ∀ t, IsThetaFunO W.ψ A' WW (Y.f' t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.snd t).1
    rw [(hI.snd t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ hψ A' WW Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 (cA D (Y.e t)) (hee' t) (hinf' t)
      Y.vac' hI.isVac'.2.theta Tm hTm _ (hSB' t)
  let Z : Tri T A A' WW :=
    ⟨⟨Y.rA.Λ, X.rA.β, Y.rA.s, Y.rA.B⟩, ⟨Y.rA'.Λ, X.rA'.β, Y.rA'.s, Y.rA'.B⟩, ⟨Y.rW.Λ, X.rW.β, Y.rW.s, Y.rW.B⟩, Y.ω, Y.ω',
      Y.vac, Y.vac', Y.e, Y.c, fun t => c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t), fun t => c2 t • Y.ω' t (1, k t) (Y.f' t),
      Y.m, Y.fd, Y.m', Y.fd'⟩
  have hZI : Z.Is W.ψ W.θ α β (fun t => nuH G t i j) (locPl G) := by
    refine ⟨hI.rank, ⟨hI.rigA.1, fA, hI.rigA.2.2⟩, ⟨hI.rigA'.1, fA', hI.rigA'.2.2⟩, ⟨hI.rigW.1, fW, hI.rigW.2.2⟩, hI.weil,
      hI.weil', hI.isVac, hI.isVac', hI.idem, hI.expo, fun t => ?_, fun t => ?_, hI.meas, hI.meas'⟩
    · refine ⟨(hI.fst t).1, fun Tm hTm => ?_⟩
      have hY := (hI.fst t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D W.ψ W.θ (GlobalTheory.Grid.neg A) WW (β t) (β t / α t) ((Y.ω t).toSgn true)
        (hI.weil t) (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 Y.vac hI.isVac (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).1 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β =
          (((α t / β t) (x1 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW
            Y.rA.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 (k t) s) := funext fun s => hx1' t s
      show c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A WW X.rA.β X.rW.β)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc1, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]
    · refine ⟨(hI.snd t).1, fun Tm hTm => ?_⟩
      have hY := (hI.snd t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D W.ψ W.θ A' WW (α t) (α t / β t) (Y.ω' t)
        (hI.weil' t) Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.vac' hI.isVac' (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).2 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB' t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β =
          (((α t / β t) (x2 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW
            Y.rA'.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 (k t) s) := funext fun s => hx2' t s
      show c2 t • Y.ω' t (1, k t) (Y.f' t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal (locPl G) t) A.rank A' WW X.rA'.β X.rW.β)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc2, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]

  have tsg : ∀ t (h' : GA D WW), (Y.ω t).toSgn true (1, h') = Y.ω t (1, h') := fun t h' => by
    show Y.ω t ((GlobalTheory.Grid.ofSgn true A) 1, h') = _
    rw [map_one]
  have kerZ : ∀ t P h' g, Z.ker W.ψ W.θ t P h' g = c1 t * Y.ker W.ψ W.θ t P (h' * k t) g := by
    intro t P h' g
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW _ _ ((Y.ω t).toSgn true) (hI.weil t) W.θ_is
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f t) (thY t) P).2
    have hm : ∀ F, Y.ω t (g, h') (Y.ω t (1, k t) F) = Y.ω t (g, h' * k t) F := fun F => by
      have e := (Y.ω t).map_mul (g, h') (1, k t)
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
        (c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t)) P = c1 t • (Y.ω t) (1, k t)
        (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, ← tsg, hop]
    calc Z.ker W.ψ W.θ t P h' g = (Y.ω t (g, h') (c1 t • Y.ω t (1, k t)
          (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [← e1]; rfl
      _ = c1 t * (Y.ω t (g, h') (Y.ω t (1, k t)
          (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c1 t * Y.ker W.ψ W.θ t P (h' * k t) g :=
          congrArg (c1 t * ·) (congrFun (hm (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P)) 0)
  have kerZ' : ∀ t P h' g, Z.ker' W.ψ W.θ t P h' g = c2 t * Y.ker' W.ψ W.θ t P (h' * k t) g := by
    intro t P h' g
    have hw' : IsWeilDatumO W.ψ A' WW (α t) (α t / β t) (Y.ω' t) := hI.weil' t
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ A' WW (α t) (α t / β t) (Y.ω' t) hw' W.θ_is
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp W.θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f' t) (thY' t) P).2
    have hm : ∀ F, Y.ω' t (g, h') (Y.ω' t (1, k t) F) = Y.ω' t (g, h' * k t) F := fun F => by
      have e : Y.ω' t ((g, h') * (1, k t)) = Y.ω' t (g, h') * Y.ω' t (1, k t) := map_mul _ _ _
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
        (c2 t • Y.ω' t (1, k t) (Y.f' t)) P = c2 t • (Y.ω' t) (1, k t)
        (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, hop]
    calc Z.ker' W.ψ W.θ t P h' g = (Y.ω' t (g, h') (c2 t • Y.ω' t (1, k t)
          (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [← e1]; rfl
      _ = c2 t * (Y.ω' t (g, h') (Y.ω' t (1, k t)
          (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c2 t * Y.ker' W.ψ W.θ t P (h' * k t) g :=
          congrArg (c2 t * ·) (congrFun (hm (pureTensorO W.ψ W.θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)) 0)
  have IZ : ∀ t P h', Z.I W.ψ W.θ t P h' = c1 t * Y.I W.ψ W.θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd, Z.ker W.ψ W.θ t P h' g ∂Y.m = _
    simp only [kerZ]
    exact MeasureTheory.integral_const_mul _ _
  have IZ' : ∀ t P h', Z.I' W.ψ W.θ t P h' = c2 t * Y.I' W.ψ W.θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd', Z.ker' W.ψ W.θ t P h' g ∂Y.m' = _
    simp only [kerZ']
    exact MeasureTheory.integral_const_mul _ _
  have c1ne : ∀ t, c1 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  have c2ne : ∀ t, c2 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

  have hv : ∀ t, ∃ ζ : D.what₂.LL, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ D.what₂.embLL ζ = c1 t / c2 t := by
    intro t
    obtain ⟨z1, ⟨n1, hn1, hz1⟩, e1⟩ := GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity μ₀ hL hN.chars i j t (x1 t) (hx1 t)
    obtain ⟨z2, ⟨n2, hn2, hz2⟩, e2⟩ := GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity μ₀ hL hN.chars i j t (x2 t) (hx2 t)
    obtain ⟨z3, ⟨n3, hn3, hz3⟩, e3⟩ := GlobalTheory.T.gridSquareCharQuotient_finiteUnitIdele_rootOfUnity μ₀ hL hN.chars i j t (y t) (hk4 t _ (hy1 t))
    refine ⟨z1 * z3 / z2, ⟨n1 * n2 * n3, by positivity, ?_⟩, ?_⟩
    · have r1 : z1 ^ (n1 * n2 * n3) = 1 := by rw [mul_assoc, pow_mul, hz1, one_pow]
      have r2 : z2 ^ (n1 * n2 * n3) = 1 := by rw [mul_comm n1 n2, mul_assoc, pow_mul, hz2, one_pow]
      have r3 : z3 ^ (n1 * n2 * n3) = 1 := by rw [mul_comm, pow_mul, hz3, one_pow]
      rw [div_pow, mul_pow, r1, r2, r3]; simp
    · rw [map_div₀, map_mul, e1, e2, e3, MonoidHom.div_apply, Circle.coe_div]
      exact ratio_alg (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  refine ⟨Z, fun t => c1 t / c2 t, ⟨p1, p2, p3, p4, n1, n2, n3, hZI⟩, eA, eA', eW, rfl, rfl, rfl, fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨z, ⟨n, hn, hz⟩, ez⟩ := hv t
    obtain ⟨z0, ⟨n0, hn0, hz0⟩, ez0⟩ := hv μ₀
    have hz0' : z0 ≠ 0 := fun h => by rw [h, zero_pow hn0.ne'] at hz0; exact zero_ne_one hz0
    refine ⟨div_ne_zero (c1ne t) (c2ne t), z / z0, away_of_root (z / z0) (n * n0) (by positivity) ?_ _, ?_⟩
    · have r1 : z ^ (n * n0) = 1 := by rw [pow_mul, hz, one_pow]
      have r2 : z0 ^ (n * n0) = 1 := by rw [mul_comm, pow_mul, hz0, one_pow]
      rw [div_pow, r1, r2, div_one]
    · rw [map_div₀, ez, ez0, div_mul_cancel₀ _ (div_ne_zero (c1ne μ₀) (c2ne μ₀))]
  · obtain ⟨⟨t0, ht0⟩, P, P', H⟩ := hc
    refine ⟨⟨t0, mul_ne_zero (div_ne_zero (c1ne t0) (c2ne t0)) ht0⟩, P, P', fun t => ⟨fun h' => ⟨?_, ?_⟩, ?_, fun h' => ?_⟩⟩
    · have e : Z.ker W.ψ W.θ t P h' = fun g => c1 t * Y.ker W.ψ W.θ t P (h' * k t) g := funext (kerZ t P h')
      rw [e]
      exact ((H t).1 (h' * k t)).1.const_mul _
    · have e : Z.ker' W.ψ W.θ t P' h' = fun g => c2 t * Y.ker' W.ψ W.θ t P' (h' * k t) g := funext (kerZ' t P' h')
      rw [e]
      exact ((H t).1 (h' * k t)).2.const_mul _
    · obtain ⟨h0, hh0⟩ := (H t).2.1
      refine ⟨h0 * (k t)⁻¹, ?_⟩
      rw [IZ', inv_mul_cancel_right]
      exact mul_ne_zero (c2ne t) hh0
    · show Z.I W.ψ W.θ t P h' = c1 t / c2 t * c t * Z.I' W.ψ W.θ t P' h'
      rw [IZ, IZ', (H t).2.2]
      exact const_alg (c2ne t)

end GlobalTheory.BottomFrames
