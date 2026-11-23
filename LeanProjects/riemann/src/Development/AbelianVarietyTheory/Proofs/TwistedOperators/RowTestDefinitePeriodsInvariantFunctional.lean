import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefPerEqGenPer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastRealAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmLiftOfMultilinearTprod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftCast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMultilinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdaptedFrameOrthonormal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvContCast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def pullBil {V₁ V₂ W₁ W₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (a : V₁ →ₗ[ℂ] W₁) (b : V₂ →ₗ[ℂ] W₂) :
    (W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] (V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) where
  toFun f := f.compl₁₂ a b
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp

theorem invLine_of_iso [DecidableEq D.what₂.Tau] (ch : Choice R) {μ0 : T} (hL : R.toLevCh.Is μ0)
    (hlf : (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
      ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (hc : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support,
        ∀ y Q ξ η, GenConv ch t a M d y Q ξ η)
    (Aψ : weylSub ((rowSizes D).nR (0 : Fin ((rowSizes D).m + 1))) (psiWt (rowEntries D ch.sc.cGap)) ≃ₗ[ℂ]
      Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W)
    (hA : ∀ g F, Aψ (psiRep (rowEntries D ch.sc.cGap) g F) =
      Aψ F ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ ((kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)
    (Bf : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
      Module.Dual ℂ R.cX.W)
    (hB : ∀ g φ, Bf ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
      Bf φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹) :
    InvLine ch := by
  classical
  obtain ⟨tc, tr, htr⟩ := GlobalTheory.RowReal.exists_fock_transport hL ch.W
  refine ⟨D.what₂.Tau, inferInstance, inferInstance, rowSizes D, rowEntries D ch.sc.cGap,
    fun τ => rowEntries_good D _ τ, fun Q => PiTensorProduct.tprod ℂ (fun j => tc j (Q.1 j)) ⊗ₜ[ℂ]
      (PiTensorProduct.tprod ℂ (fun i => tr i (Q.2 i)) ⊗ₜ[ℂ] (Aψ.symm ch.ξ ⊗ₜ[ℂ] Bf.symm (R.prX.flip ch.cv.v))), ?_⟩
  intro t a hS β hβ M hM τ hτ d hd y
  obtain ⟨Φ0, hΦ0⟩ := GlobalTheory.RowReal.genPer_multilinear ch t a M d y (hc t a hS β hβ M hM τ hτ d hd y)
  let Irow := (LinearMap.compMultilinearMapₗ ℂ (pullBil Aψ.toLinearMap Bf.toLinearMap)) ∘ₗ
    (MultilinearMap.compLinearMapₗ (fun i : Fin D.R.m => (tr i).symm.toLinearMap))
  let Φ := (Irow.compMultilinearMap Φ0).compLinearMap (fun j : Fin D.R.m => (tc j).symm.toLinearMap)
  have hΦ : ∀ x₁ y₁ v₁ φ₁, Φ x₁ y₁ v₁ φ₁ =
      genPer ch t a M d y (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁) :=
    fun x₁ y₁ v₁ φ₁ => hΦ0 (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁)
  have hv := hS.vec β τ hτ d hd
  have hinv : ∀ g x₁ y₁ v₁ φ₁, Φ (fun j => rowFock (rowEntries D ch.sc.cGap) j g (x₁ j))
      (fun i => colFock (rowEntries D ch.sc.cGap) i g (y₁ i)) (psiRep (rowEntries D ch.sc.cGap) g v₁)
      ((baseRep (rowEntries D ch.sc.cGap)).dual g φ₁) = Φ x₁ y₁ v₁ φ₁ := by
    intro g x₁ y₁ v₁ φ₁
    rw [hΦ, hΦ, hA, hB]
    obtain ⟨h1, h2⟩ := htr ch.S.toGridChoice g t
    have e1 : ptTop ch.W g 0 = (kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩ := ptTop_lt ch.W g _
    have e2 : ptGrid ch.W g 0 = (kappa ch.W g).2 0 := ptGrid_le ch.W g (Nat.succ_pos _)
    have key := GlobalTheory.RowReal.genPer_move ch hL t a M d y (fun j => ⟨_, hM.1 j j.2⟩) (fun i => ⟨_, hM.2 i (Nat.le_of_lt_succ i.2)⟩)
      hv.1 hv.2 (hlf.1 a) (hlf.2 t y) g (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i))
      (fun j => (tc j).symm (rowFock (rowEntries D ch.sc.cGap) j g (x₁ j)),
        fun i => (tr i).symm (colFock (rowEntries D ch.sc.cGap) i g (y₁ i)))
      (fun j => by simpa using h1 j (d.1 j) (hv.1 j) ((tc j).symm (x₁ j)))
      (fun i => by simpa using h2 i (d.2 i) (hv.2 i) ((tr i).symm (y₁ i))) (Aψ v₁) (Bf φ₁)
    rw [e1, e2] at key
    exact key
  obtain ⟨l, hl, hle⟩ := GlobalTheory.RowReal.invFun_of_multilinear (rowEntries D ch.sc.cGap) Φ hinv
  refine ⟨l, hl, fun Q => ?_⟩
  rw [hle]
  refine Eq.trans ?_ (hΦ _ _ _ _).symm
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem invLine_big : Big fun ch => InvLine ch := by
  obtain ⟨C1, h1⟩ := GlobalTheory.RowReal.gen_left
  obtain ⟨C2, h2⟩ := GlobalTheory.GenConvProof.genPer_conv
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, h1'⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, h2'⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  classical
  have hlf := h1' D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hc := h2' D large₂ he (le_of_max_le_right hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hL := hS.core.lev
  obtain ⟨Aψ, hA⟩ := GlobalTheory.CoefPsi.coefPsi ch.W (posOnb_of_defNode ch.W A.μ0 hL (X := .top 0) (Nat.zero_le _))
  obtain ⟨Bf, hB⟩ := GlobalTheory.CoefBase.coefBase ch hS.core.models.inf hS.core.models.cX hS.core.models.prX hch.weil
    (posOnb_of_defNode ch.W A.μ0 hL (X := .grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩)
  exact invLine_of_iso ch hL hlf hc Aψ hA Bf hB

end GlobalTheory.RowReal
