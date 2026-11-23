import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import GroundTheory.GlobalFields.Adele.IntegersLattice
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFinInhab

variable {D : D7}

theorem upSum_add' {ρ : ℕ} (A B : Mx D ρ ρ) : upSum (A + B) = upSum A + upSum B := by
  simp only [upSum, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem upSum_one' {ρ : ℕ} : upSum (1 : Mx D ρ ρ) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro hij; rw [hij] at h; omega
  · rfl

theorem mt_one_ (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

section Cond

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ σ}
  {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {ψ : AddChar (AF D.host.F) ℂ}

theorem _root_.GlobalTheory.AscFin.cond_one (hp : p.Is dV dW x ψ) (y : Mx D V₀.rank σ) : Cond dW p x y ψ (fun _ => True) 1 := by
  refine ⟨⟨1, 0, zero_mem _, ?_⟩, ?_, ?_⟩
  · intro i j
    simp [mt_one_]
  · intro N h1 h2 h3
    rw [inv_one, mt_one_, Matrix.one_mul] at h3
    have hdet : (1 + N).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · refine Finset.prod_eq_one fun i _ => ?_
        rw [Matrix.add_apply, h2 i i le_rfl, Matrix.one_apply_eq, add_zero]
      · intro i j hij
        change j < i at hij
        rw [Matrix.add_apply, h2 i j hij.le, Matrix.one_apply_ne (ne_of_gt hij), add_zero]
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, hdet]; exact isUnit_one
    have hm : hu.unit ∈ UX D ρ := by
      rw [UX, GlobalTheory.UniIndexPrime.mem_uniSub]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · show (1 + N) i j = 0
        rw [Matrix.add_apply, h2 i j hij.le, Matrix.one_apply_ne (ne_of_gt hij), add_zero]
      · show (1 + N) i i = 1
        rw [Matrix.add_apply, h2 i i le_rfl, Matrix.one_apply_eq, add_zero]
    have hN : (hu.unit.1 : Mx D ρ ρ) = 1 + N := rfl
    have key := hp.uni ⟨hu.unit, hm⟩ (by
        show MxAt (fun _ => True) ((hu.unit.1 : Mx D ρ ρ) - 1)
        rw [hN, add_sub_cancel_left]; exact h1) (by
        show x ⬝ (hu.unit.1 : Mx D ρ ρ) - x ∈ p.A₁
        rw [hN, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]; exact h3)
    have e : psiUni ψ (⟨hu.unit, hm⟩ : UX D ρ).1 = psiE ψ (upSum N) := by
      show psiE ψ (upSum (1 + N)) = _
      rw [upSum_add', upSum_one', zero_add]
    rw [← e]; exact key
  · intro ξ _ ξ' _ h
    rw [mt_one_, Matrix.one_mul] at h
    rw [h]

end Cond

end GlobalTheory.AscFinInhab

namespace GlobalTheory.AscFinInhab

open scoped Classical
open Topology

variable {D : D7}

abbrev dimE (D : D7) : ℕ := Module.finrank D.host.F D.host.E

def bAE (D : D7) : Module.Basis (Fin (dimE D)) (AF D.host.F) (AE D) :=
  Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)

def bInf (D : D7) : Module.Basis (Fin (dimE D)) (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
  Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)

def bFin (D : D7) : Module.Basis (Fin (dimE D)) (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) :=
  Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)

theorem infPart_tmul (r : AF D.host.F) (e : D.host.E) :
    infPart D (r ⊗ₜ[D.host.F] e) = fstA D.host.F r ⊗ₜ[D.host.F] e := by
  simp only [infPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem finPart_tmul (r : AF D.host.F) (e : D.host.E) :
    finPart D (r ⊗ₜ[D.host.F] e) = sndA D.host.F r ⊗ₜ[D.host.F] e := by
  simp only [finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem bInf_repr_infPart (a : AE D) (k : Fin (dimE D)) :
    (bInf D).repr (infPart D a) k = fstA D.host.F ((bAE D).repr a k) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [(infPart D).map_add, LinearEquiv.map_add, LinearEquiv.map_add, Finsupp.add_apply, Finsupp.add_apply, ha, hb]
    exact (map_add (fstA D.host.F) _ _).symm
  | tmul r e =>
    rw [infPart_tmul, bInf, bAE, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.mapRange_apply, map_mul, AlgHom.commutes]

theorem bFin_repr_finPart (a : AE D) (k : Fin (dimE D)) :
    (bFin D).repr (finPart D a) k = sndA D.host.F ((bAE D).repr a k) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    rw [(finPart D).map_add, LinearEquiv.map_add, LinearEquiv.map_add, Finsupp.add_apply, Finsupp.add_apply, ha, hb]
    exact (map_add (sndA D.host.F) _ _).symm
  | tmul r e =>
    rw [finPart_tmul, bFin, bAE, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.mapRange_apply, map_mul, AlgHom.commutes]

theorem infPart_eq_zero_iff (a : AE D) : infPart D a = 0 ↔ ∀ k, fstA D.host.F ((bAE D).repr a k) = 0 := by
  rw [← (bInf D).repr.map_eq_zero_iff, Finsupp.ext_iff]
  simp only [bInf_repr_infPart, Finsupp.coe_zero, Pi.zero_apply]

theorem finPart_eq_zero_iff (a : AE D) : finPart D a = 0 ↔ ∀ k, sndA D.host.F ((bAE D).repr a k) = 0 := by
  rw [← (bFin D).repr.map_eq_zero_iff, Finsupp.ext_iff]
  simp only [bFin_repr_finPart, Finsupp.coe_zero, Pi.zero_apply]

end GlobalTheory.AscFinInhab

namespace GlobalTheory.AscFinInhab

open scoped Classical
open Topology

variable {D : D7}

abbrev XR (D : D7) (m n : ℕ) : Type := Fin m → Fin n → Fin (dimE D) → mixedEmbedding.mixedSpace D.host.F

abbrev XF (D : D7) (m n : ℕ) : Type := Fin m → Fin n → Fin (dimE D) → Af D.host.F

theorem hms_zero : GroundTheory.Global.homeomorphMixedSpace D.host.F 0 = 0 := by
  rw [GroundTheory.Global.homeomorphMixedSpace_apply, map_zero]

theorem hms_add (a b : Ainf D.host.F) : GroundTheory.Global.homeomorphMixedSpace D.host.F (a + b) =
    GroundTheory.Global.homeomorphMixedSpace D.host.F a + GroundTheory.Global.homeomorphMixedSpace D.host.F b := by
  rw [GroundTheory.Global.homeomorphMixedSpace_apply, GroundTheory.Global.homeomorphMixedSpace_apply,
    GroundTheory.Global.homeomorphMixedSpace_apply, map_add]

def rc (a : AE D) (k : Fin (dimE D)) : mixedEmbedding.mixedSpace D.host.F :=
  GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr a k))

def fc (a : AE D) (k : Fin (dimE D)) : Af D.host.F := sndA D.host.F ((bAE D).repr a k)

def RCh (D : D7) (m n : ℕ) : Mx D m n →+ XR D m n where
  toFun z i j := rc (z i j)
  map_zero' := by
    funext i j k
    show GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr 0 k)) = 0
    rw [map_zero, Finsupp.zero_apply, map_zero, hms_zero]
  map_add' z w := by
    funext i j k
    show GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr (z i j + w i j) k)) =
      GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr (z i j) k)) +
      GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr (w i j) k))
    rw [map_add, Finsupp.add_apply, map_add, hms_add]

def FCh (D : D7) (m n : ℕ) : Mx D m n →+ XF D m n where
  toFun z i j := fc (z i j)
  map_zero' := by
    funext i j k
    show sndA D.host.F ((bAE D).repr 0 k) = 0
    rw [map_zero, Finsupp.zero_apply, map_zero]
  map_add' z w := by
    funext i j k
    show sndA D.host.F ((bAE D).repr (z i j + w i j) k) =
      sndA D.host.F ((bAE D).repr (z i j) k) + sndA D.host.F ((bAE D).repr (w i j) k)
    rw [map_add, Finsupp.add_apply, map_add]

theorem RCh_eq_zero_iff {m n : ℕ} (u : Mx D m n) : RCh D m n u = 0 ↔ u.map (infPart D) = 0 := by
  constructor
  · intro h
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply, infPart_eq_zero_iff]
    intro k
    have h1 := congrFun (congrFun (congrFun h i) j) k
    apply (GroundTheory.Global.homeomorphMixedSpace D.host.F).injective
    rw [hms_zero]
    exact h1
  · intro h
    funext i j k
    have h1 : infPart D (u i j) = 0 := by
      exact congrFun (congrFun h i) j
    rw [infPart_eq_zero_iff] at h1
    show GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr (u i j) k)) = 0
    rw [h1 k, hms_zero]

theorem FCh_eq_zero_iff {m n : ℕ} (u : Mx D m n) : FCh D m n u = 0 ↔ u.map (finPart D) = 0 := by
  constructor
  · intro h
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply, finPart_eq_zero_iff]
    intro k
    exact congrFun (congrFun (congrFun h i) j) k
  · intro h
    funext i j k
    have h1 : finPart D (u i j) = 0 := by
      exact congrFun (congrFun h i) j
    rw [finPart_eq_zero_iff] at h1
    exact h1 k

theorem continuous_repr : Continuous fun a : AE D => (bAE D).equivFun a := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (bAE D).equivFun.toLinearMap

theorem continuous_repr_symm : Continuous fun f : Fin (dimE D) → AF D.host.F => (bAE D).equivFun.symm f := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  exact IsModuleTopology.continuous_of_linearMap (bAE D).equivFun.symm.toLinearMap

theorem continuous_RCh (m n : ℕ) : Continuous (RCh D m n) := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => ?_
  exact (GroundTheory.Global.homeomorphMixedSpace D.host.F).continuous.comp (continuous_fst.comp
    ((continuous_apply k).comp (continuous_repr.comp (continuous_id.matrix_elem i j))))

theorem continuous_FCh (m n : ℕ) : Continuous (FCh D m n) := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun k => ?_
  exact continuous_snd.comp ((continuous_apply k).comp (continuous_repr.comp (continuous_id.matrix_elem i j)))

theorem pair_eq (a : AE D) : (fun k => (show AF D.host.F from ((GroundTheory.Global.homeomorphMixedSpace D.host.F).symm
    (rc a k), fc a k))) = (bAE D).equivFun a := by
  funext k
  simp only [rc, fc, Homeomorph.symm_apply_apply, Module.Basis.equivFun_apply]
  rfl

def coordInv (D : D7) (m n : ℕ) (pq : XR D m n × XF D m n) : Mx D m n :=
  Matrix.of fun i j => (bAE D).equivFun.symm fun k =>
    (show AF D.host.F from ((GroundTheory.Global.homeomorphMixedSpace D.host.F).symm (pq.1 i j k), pq.2 i j k))

def coordH (D : D7) (m n : ℕ) : Mx D m n ≃ₜ XR D m n × XF D m n where
  toFun z := (RCh D m n z, FCh D m n z)
  invFun := coordInv D m n
  left_inv z := by
    ext i j
    simp only [coordInv, Matrix.of_apply]
    exact (congrArg (bAE D).equivFun.symm (pair_eq (z i j))).trans ((bAE D).equivFun.symm_apply_apply _)
  right_inv pq := by
    refine Prod.ext ?_ ?_
    · funext i j k
      show GroundTheory.Global.homeomorphMixedSpace D.host.F (fstA D.host.F ((bAE D).repr (coordInv D m n pq i j) k)) = _
      rw [← Module.Basis.equivFun_apply, coordInv, Matrix.of_apply, LinearEquiv.apply_symm_apply]
      exact Homeomorph.apply_symm_apply _ _
    · funext i j k
      show sndA D.host.F ((bAE D).repr (coordInv D m n pq i j) k) = _
      rw [← Module.Basis.equivFun_apply, coordInv, Matrix.of_apply, LinearEquiv.apply_symm_apply]
      rfl
  continuous_toFun := (continuous_RCh m n).prodMk (continuous_FCh m n)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    refine continuous_repr_symm.comp (continuous_pi fun k => ?_)
    have h1 : Continuous fun pq : XR D m n × XF D m n => pq.1 i j k := by fun_prop
    have h2 : Continuous fun pq : XR D m n × XF D m n => pq.2 i j k := by fun_prop
    exact ((GroundTheory.Global.homeomorphMixedSpace D.host.F).symm.continuous.comp h1).prodMk h2

theorem coordH_apply {m n : ℕ} (z : Mx D m n) : coordH D m n z = (RCh D m n z, FCh D m n z) := rfl

end GlobalTheory.AscFinInhab

namespace GlobalTheory.AscFinInhab

open scoped Classical
open Topology Metric

variable {D : D7}

set_option synthInstance.maxSize 1024 in

theorem bump_core {m n : ℕ} (x : Mx D m n) (A' : AddSubgroup (XF D m n)) (ho : IsOpen (A' : Set (XF D m n)))
    (hc : IsCompact (A' : Set (XF D m n))) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Mx D m n → ℝ, IsBump (fun z => (b z : ℂ)) ∧ b x = 1 ∧ (∀ z, 0 ≤ b z ∧ b z ≤ 1) ∧
      (∀ z, b z ≠ 0 → ‖RCh D m n z - RCh D m n x‖ < ε ∧ FCh D m n z - FCh D m n x ∈ A') ∧
      (∀ u z, RCh D m n u = 0 → FCh D m n u ∈ A' → b (z + u) = b z) := by
  let φ : ContDiffBump (0 : XR D m n) := ⟨ε / 2, ε, by positivity, by linarith⟩
  let g : XR D m n → ℝ := φ.toFun
  have hg1 : Continuous g := φ.continuous
  have hg2 : ContDiff ℝ ∞ g := φ.contDiff
  have hg3 : ∀ p, g p ≠ 0 → ‖p‖ < ε := fun p hp => by
    have h3 : p ∈ ball (0 : XR D m n) ε := φ.support_eq.subset hp
    rwa [mem_ball, dist_zero_right] at h3
  have hg4 : g 0 = 1 := φ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  have hg5 : ∀ p, 0 ≤ g p := fun p => φ.nonneg
  have hg6 : ∀ p, g p ≤ 1 := fun p => φ.le_one
  let S : Set (Mx D m n) := {z | FCh D m n z - FCh D m n x ∈ A'}
  let b : Mx D m n → ℝ := fun z => g (RCh D m n z - RCh D m n x) * S.indicator 1 z
  have hcl : IsClosed (A' : Set (XF D m n)) := AddSubgroup.isClosed_of_isOpen A' ho
  have hS : IsClopen S :=
    IsClopen.preimage ⟨hcl, ho⟩ ((continuous_FCh m n).sub continuous_const)
  have hb : Continuous b :=
    (hg1.comp ((continuous_RCh m n).sub continuous_const)).mul
      (IsClopen.continuous_indicator hS continuous_const)
  have hsupp : ∀ z, b z ≠ 0 → ‖RCh D m n z - RCh D m n x‖ < ε ∧ FCh D m n z - FCh D m n x ∈ A' := by
    intro z hz
    have h1 : g (RCh D m n z - RCh D m n x) ≠ 0 := fun h => hz (by simp only [b, h, zero_mul])
    have h2 : z ∈ S := by
      by_contra h
      exact hz (by simp only [b, Set.indicator_of_notMem h, mul_zero])
    exact ⟨hg3 _ h1, h2⟩
  have hper : ∀ u z, RCh D m n u = 0 → FCh D m n u ∈ A' → b (z + u) = b z := by
    intro u z hu hu'
    have e1 : RCh D m n (z + u) - RCh D m n x = RCh D m n z - RCh D m n x := by
      rw [map_add, hu, add_zero]
    have e2 : (z + u ∈ S) ↔ (z ∈ S) := by
      show FCh D m n (z + u) - FCh D m n x ∈ A' ↔ FCh D m n z - FCh D m n x ∈ A'
      rw [map_add, add_sub_right_comm]
      exact A'.add_mem_cancel_right hu'
    simp only [b, e1, Set.indicator_apply, e2, Pi.one_apply]
  refine ⟨b, ⟨Complex.continuous_ofReal.comp hb, ?_, ?_, ?_⟩, ?_, fun z => ?_, hsupp, hper⟩
  ·
    let K : Set (Mx D m n) := coordH D m n ⁻¹'
      (closedBall (RCh D m n x) ε ×ˢ ((fun q => q - FCh D m n x) ⁻¹' (A' : Set (XF D m n))))
    have hK : IsCompact K := by
      refine (coordH D m n).isCompact_preimage.2 ((isCompact_closedBall _ _).prod ?_)
      exact (Homeomorph.subRight (FCh D m n x)).isCompact_preimage.2 hc
    have hKc : IsClosed K :=
      (isClosed_closedBall.prod (hcl.preimage (continuous_id.sub continuous_const))).preimage
        (coordH D m n).continuous
    refine HasCompactSupport.intro' hK hKc fun z hz => ?_
    by_contra h
    have h' : b z ≠ 0 := fun h0 => h (by simp only [h0, Complex.ofReal_zero])
    obtain ⟨h1, h2⟩ := hsupp z h'
    apply hz
    rw [Set.mem_preimage, coordH_apply]
    exact ⟨mem_closedBall_iff_norm.2 h1.le, h2⟩
  · refine ⟨A'.comap (FCh D m n), ho.preimage (continuous_FCh m n), fun u hu hu0 z => ?_⟩
    rw [hper u z ((RCh_eq_zero_iff u).2 hu0) hu]
  · intro k l hl hl0 w
    let L : (Fin k → ℝ) →L[ℝ] XR D m n := ((RCh D m n).comp l).toRealLinearMap ((continuous_RCh m n).comp hl)
    have hL : ∀ t, RCh D m n (l t) = L t := fun t => rfl
    have hF : ∀ t, FCh D m n (l t) = 0 := fun t => (FCh_eq_zero_iff _).2 (hl0 t)
    have e : (fun t => ((b (w + l t) : ℝ) : ℂ)) = fun t =>
        (((g (RCh D m n w - RCh D m n x + L t)) * S.indicator 1 w : ℝ) : ℂ) := by
      funext t
      have e2 : (w + l t ∈ S) ↔ (w ∈ S) := by
        show FCh D m n (w + l t) - FCh D m n x ∈ A' ↔ FCh D m n w - FCh D m n x ∈ A'
        rw [map_add, hF t, add_zero]
      simp only [b, map_add, hL, Set.indicator_apply, e2, add_sub_right_comm, Pi.one_apply]
    rw [e]
    exact Complex.ofRealCLM.contDiff.comp ((hg2.comp (contDiff_const.add L.contDiff)).mul contDiff_const)
  · show g (RCh D m n x - RCh D m n x) * S.indicator 1 x = 1
    have hx : x ∈ S := by
      show FCh D m n x - FCh D m n x ∈ A'
      rw [sub_self]; exact A'.zero_mem
    rw [sub_self, Set.indicator_of_mem hx, Pi.one_apply, mul_one, hg4]
  · have h1 := hg5 (RCh D m n z - RCh D m n x)
    have h2 := hg6 (RCh D m n z - RCh D m n x)
    simp only [b, Set.indicator_apply]
    split_ifs
    · simp only [Pi.one_apply, mul_one]; exact ⟨h1, h2⟩
    · simp

end GlobalTheory.AscFinInhab

namespace GlobalTheory.AscFinInhab

open scoped Classical
open Topology Metric

variable {D : D7}

theorem mxAt_true_iff {m n : ℕ} (a : Mx D m n) : MxAt (fun _ => True) a ↔ a.map (infPart D) = 0 := by
  constructor
  · intro h
    ext i j
    exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (h i j)).1
  · intro h i j
    refine Ideal.mem_inf.2 ⟨RingHom.mem_ker.2 (congrFun (congrFun h i) j), Ideal.mem_iInf.2 fun w => ?_⟩
    exact absurd trivial w.2

theorem coordH_symm_zero (m n : ℕ) : (coordH D m n).symm (0, 0) = 0 := by
  rw [Homeomorph.symm_apply_eq, coordH_apply, map_zero, map_zero]

theorem _root_.GlobalTheory.AscFin.exists_bump_le {m n : ℕ} (x : Mx D m n) (A : AddSubgroup (Mx D m n)) (hA : FinLat A) (U : Set (Mx D m n))
    (hU : U ∈ 𝓝 x) :
    ∃ b : Mx D m n → ℝ, IsBump (fun z => (b z : ℂ)) ∧ b x = 1 ∧ (∀ z, 0 ≤ b z ∧ b z ≤ 1) ∧
      (∀ z, b z ≠ 0 → ∃ r : Mx D m n, r.map (finPart D) = 0 ∧ x + r ∈ U ∧ z - (x + r) ∈ A) ∧
      (∀ a ∈ A, ∀ z, b (z + a) = b z) := by
  have hR : ∀ a ∈ A, RCh D m n a = 0 := fun a ha =>
    (RCh_eq_zero_iff a).2 ((mxAt_true_iff a).1 (hA.fin a ha))
  let A' : AddSubgroup (XF D m n) := A.map (FCh D m n)
  have hc : IsCompact (A' : Set (XF D m n)) := by
    rw [AddSubgroup.coe_map]
    exact hA.cpt.image (continuous_FCh m n)
  have ho : IsOpen (A' : Set (XF D m n)) := by
    refine AddSubgroup.isOpen_of_mem_nhds A' (g := 0) ?_
    obtain ⟨U0, hU0o, h0, hU0⟩ := hA.opn
    let ι0 : XF D m n → Mx D m n := fun q => (coordH D m n).symm (0, q)
    have hι : Continuous ι0 := (coordH D m n).symm.continuous.comp (continuous_const.prodMk continuous_id)
    have hι0 : ι0 0 = 0 := coordH_symm_zero m n
    refine Filter.mem_of_superset ((hU0o.preimage hι).mem_nhds (by rw [Set.mem_preimage, hι0]; exact h0)) ?_
    intro q hq
    have e : coordH D m n (ι0 q) = (0, q) := (coordH D m n).apply_symm_apply _
    rw [coordH_apply] at e
    have hA0 : ι0 q ∈ A := hU0 _ hq ((mxAt_true_iff _).2 ((RCh_eq_zero_iff _).1 (congrArg Prod.fst e)))
    exact ⟨ι0 q, hA0, congrArg Prod.snd e⟩
  have hcont : Continuous fun p => (coordH D m n).symm (p, FCh D m n x) :=
    (coordH D m n).symm.continuous.comp (continuous_id.prodMk continuous_const)
  have hx : (coordH D m n).symm (RCh D m n x, FCh D m n x) = x := by
    rw [← coordH_apply]; exact (coordH D m n).symm_apply_apply x
  have hpre : (fun p => (coordH D m n).symm (p, FCh D m n x)) ⁻¹' U ∈ 𝓝 (RCh D m n x) :=
    hcont.continuousAt.preimage_mem_nhds (by rw [hx]; exact hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨b, hb, hbx, hb01, hsupp, hper⟩ := bump_core x A' ho hc hε
  refine ⟨b, hb, hbx, hb01, fun z hz => ?_, fun a ha z => hper a z (hR a ha) (AddSubgroup.mem_map_of_mem _ ha)⟩
  obtain ⟨h1, h2⟩ := hsupp z hz
  obtain ⟨a, ha, hae⟩ := AddSubgroup.mem_map.1 h2
  refine ⟨z - x - a, (FCh_eq_zero_iff _).1 ?_, ?_, by abel_nf; exact ha⟩
  · rw [map_sub, map_sub, hae, sub_self]
  · have e : x + (z - x - a) = (coordH D m n).symm (RCh D m n z, FCh D m n x) := by
      rw [Homeomorph.eq_symm_apply, coordH_apply, map_add, map_add, map_sub, map_sub, map_sub, map_sub, hR a ha, hae]
      congr 1 <;> abel
    rw [e]
    exact hball (by rw [mem_ball, dist_eq_norm]; exact h1)

end GlobalTheory.AscFinInhab

namespace GlobalTheory.AscFin

end GlobalTheory.AscFin
