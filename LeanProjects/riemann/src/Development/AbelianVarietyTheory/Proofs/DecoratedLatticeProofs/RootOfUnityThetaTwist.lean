import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormEmbeddingHostFormConstantEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.TupRoot

variable {D : D7}

theorem finite_pow_eq_one (n : ℕ) (hn : 0 < n) : {z : Circle | z ^ n = 1}.Finite := by
  refine ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.preimage
    (Set.injOn_of_injective Circle.coe_injective)).subset fun z hz => ?_
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  have hz' : z ^ n = 1 := hz
  have := congrArg (fun w : Circle => (w : ℂ)) hz'
  simpa using this

theorem isOpen_ker_of_pow {X : Type} [TopologicalSpace X] [Group X] (c : X →* Circle) (hc : Continuous c) (n : ℕ) (hn : 0 < n)
    (hp : ∀ x, c x ^ n = 1) : IsOpen (c.ker : Set X) := by
  have hF : ({z : Circle | z ^ n = 1} \ {1}).Finite := (finite_pow_eq_one n hn).diff
  have ho := hF.isClosed.isOpen_compl.preimage hc
  convert ho using 1
  ext x
  simp [hp x]

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 := by
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D ((powMonoidHom n).comp c)
    ⟨(continuous_pow n).comp h.1.1, fun k => by
      have := h.1.2 k
      simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
      erw [this, one_pow]⟩
    (fun y hy => by simpa using GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n hn y hy) x
  simpa using this

theorem eq_one_of_finPart {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn0 : 0 < n)
    (hn : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 :=
  GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one D c
    (isOpen_ker_of_pow c h.1.1 n hn0 (pow_eq_one_of_chrEq h hn)) x hx

theorem twist_eq {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT ν : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hW' : IsWeilDatumO ψ S T (χS * ν) (χT * ν) om') {g : GA D S} {h : GA D T} {x y : (AE D)ˣ}
    (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = (((ν x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) f := by
  rw [GlobalTheory.T.weilData_differ_by_splittingFactorQuotient D ψ S T χS χT _ _ om om' hW hW' g h x y hx hy f hf]
  congr 1
  have e : splitFacO (χS * ν) (χT * ν) x y = (ν x)⁻¹ * ν y * splitFacO χS χT x y := by
    simp only [splitFacO, MonoidHom.mul_apply]
    rw [mul_inv]
    ac_rfl
  rw [e, Circle.coe_mul, mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), mul_one]

theorem isWeil_rec {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {n n' : ℕ} (e : n = n')
    (om : Om (Yc D n) D.sp.X') (h : IsWeilDatumO ψ (Yc D n) D.sp.X' χS χT om) :
    IsWeilDatumO ψ (Yc D n') D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') om e) := by
  subst e
  exact h

end GlobalTheory.TupRoot

open GlobalTheory.TupRoot in

theorem GlobalTheory.TupRoot.weil_tuple_root : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ t, ∃ ζ : ℕ → ℂ, (∀ j, ∃ n : ℕ, 0 < n ∧ ζ j ^ n = 1) ∧ (∀ j, j + 1 < D.R.m → f.g.b j ∈ GfC _ → f.g.b (j + 1) ∈ GfC _ → ∀ a ∈ GinfC _, ∀ a' ∈ GinfC _, ∀ g, IsThetaFunO (pk W).ψ _ _ g → (pk W).ωY t j (a * f.g.b j, a' * f.g.b (j + 1)) g = ζ j • (pk W).ωY W.P.A3.A.μ0 j (a * f.g.b j, a' * f.g.b (j + 1)) g) ∧ (∀ j h g, IsThetaFunO (pk W).ψ _ _ g → omT (pk W) t j h (f.g.b (j + 1), f.g.bT) g = ζ (j + 1) • omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) g) ∧ ∀ j, ∃ n : ℕ, 0 < n ∧ (pk W).toLevCh.mu t j ^ n = (pk W).toLevCh.mu W.P.A3.A.μ0 j ^ n := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP _hR t
  have hc := hP.bot.hyp.2.2.2.1
  have hL := hc.lev
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have hxi : ChrEq ((pk W).xi t) ((pk W).xiH t) := hL.xi t
  have hb : (pk W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have hstep : ∀ k, Lift.chrStep ((pk W).toLevCh.mu t) (pk W).eta k =
      ((Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta k).1 * (pk W).xi t,
        (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta k).2 * (pk W).xi t) := by
    intro k
    unfold Lift.chrStep
    split_ifs <;> simp [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_right_comm]
  have hpow : ∀ x, (pk W).xi t x ^ n = 1 := pow_eq_one_of_chrEq hxi hn
  have hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → (pk W).xi t x = 1 := eq_one_of_finPart hxi hn0 hn
  choose xr hxr using fun k => GlobalTheory.RecDict.exists_isDetRoot D (Yc D k) (f.g.b k)
  obtain ⟨xT, hxT⟩ := GlobalTheory.RecDict.exists_isDetRoot D D.sp.X' f.g.bT
  let w : ℕ → Circle := fun k => if k + 1 < D.R.m then ((pk W).xi t (xr k))⁻¹ * (pk W).xi t (xr (k + 1))
    else ((pk W).xi t (xr k))⁻¹ * (pk W).xi t xT
  refine ⟨fun k => (w k : ℂ), ?_, ?_, ?_, ?_⟩
  · intro k
    refine ⟨n, hn0, ?_⟩
    have h1 : w k ^ n = 1 := by
      simp only [w]
      split_ifs <;> rw [mul_pow, inv_pow, hpow, hpow, inv_one, one_mul]
    have := congrArg (fun z : Circle => (z : ℂ)) h1
    simpa using this
  · intro j hj _ _ a ha a' ha' g hg
    have hW0 := hc.chain.ωY W.P.A3.A.μ0 j hj
    have hWt := hc.chain.ωY t j hj
    rw [hstep] at hWt
    obtain ⟨z, hz⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D j) a
    obtain ⟨y, hy1, hy⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a ha z hz
    obtain ⟨z', hz'⟩ := GlobalTheory.RecDict.exists_isDetRoot D (Yc D (j + 1)) a'
    obtain ⟨y', hy1', hy'⟩ := GlobalTheory.TwistFinPart.exists_isDetRoot_finPart_one _ a' ha' z' hz'
    rw [twist_eq hW0 hWt (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy (hxr j))
      (GlobalTheory.ExtCore.isDetRoot_mul _ _ _ _ _ hy' (hxr (j + 1))) hg]
    have e : ((pk W).xi t (y * xr j))⁻¹ * (pk W).xi t (y' * xr (j + 1)) = w j := by
      simp only [w, if_pos hj, map_mul, hinf _ hy1, hinf _ hy1', one_mul]
    rw [e]
  · intro j h g hg
    have hW0 := isWeil_rec (idx_top h) _ (hc.chain.ωX W.P.A3.A.μ0)
    have hWt := isWeil_rec (idx_top h) _ (hc.chain.ωX t)
    rw [hstep] at hWt
    have e := twist_eq hW0 hWt (hxr (j + 1)) hxT hg
    have hw : w (j + 1) = ((pk W).xi t (xr (j + 1)))⁻¹ * (pk W).xi t xT := by
      simp only [w]
      rw [if_neg (by omega)]
    show _ = ((w (j + 1) : Circle) : ℂ) • _
    rw [hw]
    exact e
  · intro j
    refine ⟨n, hn0, ?_⟩
    have hν : (pk W).xi t ^ n = 1 := MonoidHom.ext fun x => by simpa using hpow x
    simp only [Formalism.IndefR.Links.LevCh.mu, Lift.tup, hb, mul_one, mul_pow, hν]
