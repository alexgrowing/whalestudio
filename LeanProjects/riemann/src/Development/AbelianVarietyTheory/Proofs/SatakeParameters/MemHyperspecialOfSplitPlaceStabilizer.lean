import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = dotProduct (fun i => σ (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_smul_left (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (fun i => a * x i) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [hform_eq, dotProduct, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (fun i => a * y i) = a * Formalism.UG.hform σ J x y := by
  have : (fun i => a * y i) = a • y := rfl
  rw [hform_eq, hform_eq, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform σ J x y := by
  have e : (fun i => σ (g.mulVec x i)) = Matrix.vecMul (fun i => σ (x i)) (Formalism.UG.cT σ g) := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem stab_of_half (I : AddSubgroup A) (L : AddSubgroup (Fin n → A))
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, Formalism.UG.hform σ J z y ∈ I) {p : A}
    (hp : ∀ y ∈ L, (fun i => p * y i) ∈ L) (hq : ∀ y ∈ L, (fun i => σ p * y i) ∈ L)
    {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J)
    (hs : ∀ i j, (p + σ p) * (g - 1) i j = (g - 1) i j)
    (h1 : ∀ y ∈ L, (fun i => p * g.mulVec y i) ∈ L)
    (h2 : ∀ y ∈ L, ∃ z ∈ L, (fun i => p * y i) = fun i => p * g.mulVec z i) (y : Fin n → A) :
    y ∈ L ↔ g.mulVec y ∈ L := by
  have fwd : ∀ y ∈ L, g.mulVec y ∈ L := by
    intro y hy
    have hc : (fun i => σ p * g.mulVec y i) ∈ L := by
      refine (hL _).2 fun z hz => ?_
      obtain ⟨z', hz', e⟩ := h2 z hz
      rw [hform_smul_right, ← hform_smul_left, e, hform_smul_left, hform_mulVec σ J hg, ← hform_smul_right]
      exact (hL _).1 (hq y hy) z' hz'
    have hs' : (p + σ p) • (g - 1) = g - 1 := Matrix.ext hs
    have e : (p + σ p) • (g.mulVec y - y) = g.mulVec y - y := by
      have := congrArg (fun m => Matrix.mulVec m y) hs'
      simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
    have e2 : g.mulVec y = y + ((fun i => p * g.mulVec y i) + (fun i => σ p * g.mulVec y i) -
        (fun i => p * y i) - fun i => σ p * y i) := by
      funext i
      have := congrFun e i
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
      linear_combination -this
    rw [e2]
    exact add_mem hy (sub_mem (sub_mem (add_mem (h1 y hy) hc) (hp y hy)) (hq y hy))
  refine ⟨fwd y, fun hy => (hL _).2 fun z hz => ?_⟩
  rw [← hform_mulVec σ J hg]
  exact (hL _).1 hy _ (fwd z hz)

theorem supp_map {B : Type} [CommRing B] (φ : A →+* B) {f : A} {g : Matrix (Fin n) (Fin n) A}
    (hs : ∀ i j, f * (g - 1) i j = (g - 1) i j) (i j : Fin n) :
    φ f * (g.map φ - 1) i j = (g.map φ - 1) i j := by
  have e : (g.map φ - 1) i j = φ ((g - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_mul, hs]

end Alg

variable {D : D7}

theorem finPart_conj (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem finMat_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) *
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram * finMat D.sp.cm.sig V.gram g =
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := by
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
      JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (fun m => Matrix.map m (finPart D)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (JR (AF D.host.F) V.gram).map (finPart D) = JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := rfl
  have e2 : (mt V g).map (finPart D) = finMat D.sp.cm.sig V.gram g := rfl
  have e3 : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (finPart D) =
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) := by
    ext i j
    exact finPart_conj _
  rwa [e1, e2, e3] at h2

theorem mem_ksph_of_split : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  intro D V e g he hs h1 h2
  obtain ⟨hd, hm⟩ := GlobalTheory.LatDual.lamHat_selfDual_and_module V
  obtain ⟨i1, -, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have hp : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, i1])
  have hq : sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ← RingHom.map_mul, i1])
  refine ⟨?_, ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  · have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h6 := congrArg (infPart D) (hs i j)
    rw [RingHom.map_mul, h5, zero_mul, Matrix.sub_apply, RingHom.map_sub] at h6
    have h7 : infPart D (mt V g i j) = infPart D ((1 : Matrix _ _ (Formalism.L2.Theta.AE D)) i j) :=
      sub_eq_zero.1 h6.symm
    refine h7.trans ?_
    rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  · refine stab_of_half (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
      (JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram) (intAE D) (LamHat V) hd (p := finPart D e)
      (hm _ hp) (hm _ hq) (finMat_unitary V g) (fun i j => ?_) h1 h2
    rw [← finPart_conj, ← RingHom.map_add]
    exact supp_map (finPart D) hs i j

end GlobalTheory.SplitStab
