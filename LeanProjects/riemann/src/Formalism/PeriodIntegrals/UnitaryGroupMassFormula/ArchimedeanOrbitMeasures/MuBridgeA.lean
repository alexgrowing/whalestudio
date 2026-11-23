import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BridgeC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMu

noncomputable section

namespace PI.AprimeInfW.MuB

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix ComplexConjugate

section Tr

variable {D : D7} (X : HidaSetting D)

theorem emb_real (v : InfinitePlace X.B.I.F) (a : X.B.I.F) : conj (v.embedding a) = v.embedding a := by
  have hv : v.IsReal := totReal_of X v
  have h := NumberField.ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hv)
  have := RingHom.congr_fun h a
  simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this

theorem phi_star (v : InfinitePlace X.B.I.F) (e : X.B.I.E) : X.B.I.φ v (star e) = conj (X.B.I.φ v e) :=
  X.B.I.cm.cmUnram.2.1 _ e

theorem phi_notReal (v : InfinitePlace X.B.I.F) : ¬ ∀ e : X.B.I.E, conj (X.B.I.φ v e) = X.B.I.φ v e := by
  intro h
  have hr : NumberField.ComplexEmbedding.IsReal (X.B.I.φ v) := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext e
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq, h e]
  have hc := X.B.I.cm.cmUnram.1.isComplex (InfinitePlace.mk (X.B.I.φ v))
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) (InfinitePlace.isReal_mk_iff.2 hr)

theorem emb_trace (v : InfinitePlace X.B.I.F) (e : X.B.I.E) :
    v.embedding (Algebra.trace X.B.I.F X.B.I.E e) = X.B.I.φ v e + conj (X.B.I.φ v e) := by
  classical
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  letI : Algebra X.B.I.F ℂ := v.embedding.toAlgebra
  let φA : X.B.I.E →ₐ[X.B.I.F] ℂ := { X.B.I.φ v with commutes' := X.B.I.φ_over v }
  let ψA : X.B.I.E →ₐ[X.B.I.F] ℂ :=
    { (starRingEnd ℂ).comp (X.B.I.φ v) with
      commutes' := fun a => by
        show conj (X.B.I.φ v (algebraMap X.B.I.F X.B.I.E a)) = v.embedding a
        rw [X.B.I.φ_over, emb_real] }
  have hne : φA ≠ ψA := by
    intro h
    apply phi_notReal X v
    intro e
    have := congrArg (fun f : X.B.I.E →ₐ[X.B.I.F] ℂ => f e) h
    exact this.symm
  have hcard : Fintype.card (X.B.I.E →ₐ[X.B.I.F] ℂ) = 2 := by
    rw [AlgHom.card X.B.I.F X.B.I.E ℂ, X.B.I.cm.deg2]
  have huniv : (Finset.univ : Finset (X.B.I.E →ₐ[X.B.I.F] ℂ)) = {φA, ψA} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hne]
  have h := trace_eq_sum_embeddings (K := X.B.I.F) (L := X.B.I.E) ℂ (x := e)
  rw [huniv, Finset.sum_pair hne] at h
  exact h

theorem evInf_conj (v : InfinitePlace X.B.I.F) (a : Ainf X.B.I.F) :
    conj (PI.AprimeInfU.evInf X v a) = PI.AprimeInfU.evInf X v a := by
  have hv : v.IsReal := totReal_of X v
  show conj (InfinitePlace.Completion.extensionEmbedding v (a v)) =
    InfinitePlace.Completion.extensionEmbedding v (a v)
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv]
  exact Complex.conj_ofReal _

theorem evInf_alg (v : InfinitePlace X.B.I.F) (a : X.B.I.F) :
    PI.AprimeInfU.evInf X v (algebraMap X.B.I.F (Ainf X.B.I.F) a) = v.embedding a :=
  evV_algebraMap X.B.I v a

theorem trace_one_tmul (e : X.B.I.E) :
    Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) =
      algebraMap X.B.I.F (Ainf X.B.I.F) (Algebra.trace X.B.I.F X.B.I.E e) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem evInf_trace (v : InfinitePlace X.B.I.F) (z : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.evInf X v (Algebra.trace (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) z) =
      PI.AprimeInfU.thetaInf X v z + conj (PI.AprimeInfU.thetaInf X v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h1 : a ⊗ₜ[X.B.I.F] e = a • ((1 : Ainf X.B.I.F) ⊗ₜ[X.B.I.F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, trace_one_tmul, smul_eq_mul, map_mul, evInf_alg, emb_trace, ← h1, thetaInf_tmul, map_mul,
      evInf_conj]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]; ring

theorem theta_sigR (v : InfinitePlace X.B.I.F) (t : Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (sigR (Ainf X.B.I.F) X.B.I.cm.sig t) = conj (PI.AprimeInfU.thetaInf X v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : sigR (Ainf X.B.I.F) X.B.I.cm.sig (a ⊗ₜ[X.B.I.F] e) = a ⊗ₜ[X.B.I.F] (star e) := rfl
    rw [h, thetaInf_tmul, thetaInf_tmul, map_mul, evInf_conj, phi_star]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem theta_hR (v : InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    PI.AprimeInfU.thetaInf X v (hR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J x y) =
      ∑ i, ∑ j, conj (PI.AprimeInfU.thetaInf X v (x i)) * X.B.I.φ v (X.B.I.J i j) *
        PI.AprimeInfU.thetaInf X v (y j) := by
  simp only [hR, Formalism.UG.hform, map_sum, map_mul, theta_sigR, JR, Matrix.map_apply, thetaInf_inclR]

end Tr

section Form

theorem form_dot {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj (p i) * M i j * q j = star p ⬝ᵥ (M *ᵥ q) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_P {n : ℕ} (P A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n → ℂ) :
    ∑ i, ∑ j, conj ((P *ᵥ p) i) * A i j * (P *ᵥ q) j = ∑ i, ∑ j, conj (p i) * (Pᴴ * A * P) i j * q j := by
  rw [form_dot, form_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem form_Jm {n : ℕ} (ε : Fin n → Bool) (p q : Fin n → ℂ) :
    (∑ i, ∑ j, conj (p i) * Formalism.REAL.Jm ε i j * q j).re =
      ∑ i, (if ε i then 1 else -1 : ℝ) * ((p i).re * (q i).re + (p i).im * (q i).im) := by
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

end Form

section Beta

variable {D : D7} (X : HidaSetting D)

theorem theta_col (v : InfinitePlace X.B.I.F) (Y : TupI X) (b : Fin (D.R.rS + 1 + D.R.rS)) :
    (fun j => PI.AprimeInfU.thetaInf X v (Y b j)) = X.B.I.P v *ᵥ fun i => betaV X v Y i b := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have : (fun i => betaV X v Y i b) = (X.B.I.P v)⁻¹ *ᵥ fun j => PI.AprimeInfU.thetaInf X v (Y b j) := by
    funext i
    simp [betaV]
  rw [this, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]

theorem re_evInf_BR (v : InfinitePlace X.B.I.F) (Y Z : TupI X) :
    (PI.AprimeInfU.evInf X v (BR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J Y Z)).re =
      ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v Y i b).re * (betaV X v Z i b).re + (betaV X v Y i b).im * (betaV X v Z i b).im)) := by
  simp only [BR, map_sum, Complex.re_sum, evInf_trace, Complex.add_re, Complex.conj_re]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [theta_hR]
  have e1 := theta_col X v Y b
  have e2 := theta_col X v Z b
  have hY : ∀ i, PI.AprimeInfU.thetaInf X v (Y b i) = (X.B.I.P v *ᵥ fun i => betaV X v Y i b) i :=
    fun i => congrFun e1 i
  have hZ : ∀ i, PI.AprimeInfU.thetaInf X v (Z b i) = (X.B.I.P v *ᵥ fun i => betaV X v Z i b) i :=
    fun i => congrFun e2 i
  simp only [hY, hZ]
  have hJ : ∀ i j, X.B.I.φ v (X.B.I.J i j) = (X.B.I.J.map (X.B.I.φ v)) i j := fun _ _ => rfl
  simp only [hJ]
  rw [form_P, X.B.I.P_spec v, form_Jm, ← two_mul, Finset.mul_sum]

theorem betaI_bridge (x y : EuclideanSpace ℝ (KapI X)) :
    betaI X x y = ∑ v, ∑ b, ∑ i, 2 * ((if X.B.I.ε v i then 1 else -1 : ℝ) *
        ((betaV X v ((tupCoord X).symm x) i b).re * (betaV X v ((tupCoord X).symm y) i b).re +
          (betaV X v ((tupCoord X).symm x) i b).im * (betaV X v ((tupCoord X).symm y) i b).im)) := by
  simp only [betaI]
  refine Finset.sum_congr rfl fun v _ => ?_
  exact re_evInf_BR X v _ _

end Beta

end PI.AprimeInfW.MuB
