import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EqOfUnitriangularOfEqLowerMul

open AlgebraicGeometry CategoryTheory Limits NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg.GenericFlagInj

theorem unitri_eq_of_lower {S : Type} [CommRing S] {n : ℕ} (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ i j, j < i → A i j = 0) (hAd : ∀ i, A i i = 1)
    (hA' : ∀ i j, j < i → A' i j = 0) (hAd' : ∀ i, A' i i = 1)
    (hL : ∀ i j, i < j → L i j = 0) (e : A' = L * A) : A' = A := by
  first
  | exact @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | (apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genPt_inj {Z Z' : Comp Xo c} (h : genPt Z = genPt Z') : Z = Z' := by
  have g : ∀ W : Comp Xo c, IsGenericPoint (genPt W) (W : Set (Xo.XF c)) := fun W =>
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  exact Subtype.ext (by rw [← (g Z).def, ← (g Z').def, h])

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := by
  symm
  show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem genSp_eq {T : Type} [CommRing T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') :
    spMap ψ.toRingHom ≫ genSp Z = spMap ψ'.toRingHom ≫ genSp Z' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h
  · have e := genSp_strK Z
    have e' := genSp_strK Z'
    rw [Category.assoc, Category.assoc]
    erw [e, e']
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext r
    exact (ψ.commutes r).trans (ψ'.commutes r).symm

theorem comp_eq {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') : Z = Z' := by
  obtain ⟨p⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  have e := congrArg (fun f : Sp T ⟶ Xo.XF c => f p) (genSp_eq ψ ψ' h)
  simp only [Scheme.Hom.comp_apply, genSp] at e
  apply genPt_inj
  exact (Scheme.fromSpecResidueField_apply _ _).symm.trans (e.trans (Scheme.fromSpecResidueField_apply _ _))

theorem emb_eq {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (ψ ψ' : kap Z →ₐ[c.F] T)
    (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z) : ψ = ψ' := by
  have e := genSp_eq ψ ψ' h
  haveI : Mono (genSp Z) := by unfold genSp; infer_instance
  have e2 : spMap ψ.toRingHom = spMap ψ'.toRingHom := (cancel_mono (genSp Z)).1 e
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
  exact AlgHom.coe_ringHom_injective e3

noncomputable def resKap {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T) : kap Z →ₐ[c.F] T :=
  { φ.toRingHom.comp (algebraMap (kap Z) (Om Z)) with
    commutes' := fun r => by
      have := φ.commutes r
      rw [gfp_tower] at this
      exact this }

theorem x_eq {T : Type} [CommRing T] [Algebra c.F T] (h : GenFrEx Xo c) {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T)
    {y : FrPt Xo c T} (hy : FrMap φ (genFr h Z) y) : y.x = spMap (resKap φ).toRingHom ≫ xGen Z := by
  rw [hy.1, (isGenFr_genFr h Z).1, ← Category.assoc, spMap_comp_ring]
  rfl

theorem eq_of_frBor {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] (h : GenFrEx Xo c) (Z Z' : Comp Xo c)
    (φ : Om Z →ₐ[c.F] T) (φ' : Om Z' →ₐ[c.F] T) (y y' : FrPt Xo c T) (t : Ix Dw → Tˣ)
    (hy : FrMap φ (genFr h Z) y) (hy' : FrMap φ' (genFr h Z') y') (hb : FrBor t y y') : Z = Z' ∧ HEq φ φ' := by
  have hx := x_eq h φ hy
  have hx' := x_eq h φ' hy'
  have hxx := hx.symm.trans (hb.1.symm.trans hx')
  obtain rfl : Z = Z' := comp_eq _ _ hxx
  refine ⟨rfl, heq_of_eq ?_⟩
  have hψ : resKap φ = resKap φ' := emb_eq _ _ hxx
  obtain ⟨y₀, hy₀, hc⟩ := (isGenFr_genFr h Z).2
  have pull : ∀ (χ : Om Z →ₐ[c.F] T) (w : FrPt Xo c T), FrMap χ (genFr h Z) w → ∀ τ i,
      IsCombAt w.x (fun j => spMap (dualMap (resKap χ).toRingHom) ≫ y₀.u τ j) (fun j => χ (genCoef Z τ i j))
        (w.u τ i) := by
    intro χ w hw τ i
    refine isCombAt_pull χ.toRingHom hw.1 (fun j => ?_) (hw.2.1 τ i) (hc τ i)
    rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp]
    rfl
  have hcoef : ∀ τ i j, φ' (genCoef Z τ i j) = φ (genCoef Z τ i j) := by
    intro τ
    choose cf hd hz hcf using hb.2.1 τ
    have hyx : y.x = spMap (resKap φ).toRingHom ≫ y₀.x := by rw [hx, hy₀]
    have key := unitri_eq_of_lower (Matrix.of fun i j => φ (genCoef Z τ i j))
      (Matrix.of fun i j => φ' (genCoef Z τ i j)) (Matrix.of cf)
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef])
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef]) (fun i j hij => hz i j hij) ?_
    · intro i j
      exact congrFun (congrFun key i) j
    · ext i j
      have h1 := pull φ' y' hy' τ i
      rw [← hψ, hb.1] at h1
      have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo T y.x
        (fun j => spMap (dualMap (resKap φ).toRingHom) ≫ y₀.u τ j)
        (fun j => hyx ▸ GlobalTheory.Frames.FramedBaseChange.tan_bc (resKap φ).toRingHom (y₀.tan τ j)) (y.u τ)
        (Matrix.of fun j i => φ (genCoef Z τ i j)) (cf i) (y'.u τ i) (pull φ y hy τ) (hcf i)
      have ht : IsTanAt y.x (y'.u τ i) := hb.1 ▸ y'.tan τ i
      rw [hyx] at h1 h2 ht
      have h3 := (GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c _ T (resKap φ) y₀ τ _ ht (y'.eig τ i)).unique h1 h2
      have h4 := congrFun h3 j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at h4
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [h4]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · exact AlgHom.congr_fun hψ r
  · obtain ⟨τ, ⟨i, j⟩, hij⟩ := v
    have := hcoef τ i j
    simp only [genCoef, dif_pos (show i < j from hij)] at this
    exact this.symm

end GlobalTheory.Reg.GenericFlagInj
