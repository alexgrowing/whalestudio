import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace GlobalTheory.InvJump

section Generic

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem eq_zero_of_mem_Fil_one (c : K) (h : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hc
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ h
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one] at this
  exact PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h1 PD.mem_filtration_one)

theorem isJumpV_zero_of_invariant [CharZero Qp] (ρ : Representation LL G V) (x : V) (hx : x ≠ 0)
    (hinv : ∀ g, ρ g x = x) (τ : K →ₐ[Qp] LL) : IsJumpV PD ρ τ 0 := by
  classical
  haveI := PD.finK
  let b := Module.finBasis Qp K
  let b' := b.traceDual
  let y : V ⊗[Qp] BdR := ∑ i, (τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b i)
  have e1 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b' j) • b j := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b.sum_repr z, Finset.sum_mul, map_sum]
    simp only [b', smul_mul_assoc, map_smul, Module.Basis.trace_mul_traceDual]
    simp
  have e2 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b j) • b' j := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b'.sum_repr z]
    simp [b', Finset.sum_mul, Module.Basis.trace_traceDual_mul]
  have h0 : y ∈ FildR PD ρ τ 0 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      simp [y, actVdR, map_sum, hinv]
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero, LinearMap.smul_apply]
      intro c
      have l : mulVdR (LL := LL) (V := V) c y =
          ∑ i, ∑ j, Algebra.trace Qp K (c * b i * b' j) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, map_sum, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
          LinearMap.mulLeft_apply, ← map_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [e1 (c * b i), map_sum, tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← tmul_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      have r : τ c • y =
          ∑ j, ∑ i, Algebra.trace Qp K (c * b' j * b i) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, Finset.smul_sum, smul_tmul', smul_smul, ← map_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        conv_lhs => rw [e2 (c * b' j), map_sum, Finset.sum_smul, sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_assoc]
      rw [l, r, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_right_comm]
    · refine Submodule.sum_mem _ fun i _ => ⟨(τ (b' i) • x) ⊗ₜ ⟨algebraMap K BdR (b i), ?_⟩, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem
  intro h
  rw [← h] at h0
  obtain ⟨w, hw⟩ := h0.2
  obtain ⟨φ, hφ⟩ : ∃ φ : LL →ₗ[Qp] Qp, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ := (Algebra.linearMap Qp LL).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap Qp LL).injective)
    exact ⟨φ, by simpa using LinearMap.congr_fun hφ 1⟩
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[LL] LL, f x = 1 := Module.Projective.exists_dual_eq_one LL hx
  let m : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (φ ∘ₗ f.restrictScalars Qp).rTensor BdR
  have hm : ∀ w, m (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil (0 + 1)).restrictScalars Qp).subtype w) ∈ (PD.Fil (0 + 1)).restrictScalars Qp := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using ((PD.Fil (0 + 1)).restrictScalars Qp).smul_mem (φ (f v)) c.2
    | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  have h1 := hm w
  rw [hw] at h1
  have h2 : m y = algebraMap K BdR (∑ i, φ (τ (b' i)) • b i) := by
    simp only [y, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [m, hf, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [h2] at h1
  have h3 := eq_zero_of_mem_Fil_one PD _ (by rw [zero_add] at h1; exact h1)
  have h4 : ∀ i, φ (τ (b' i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
  have h5 : φ ∘ₗ τ.toLinearMap = 0 := b'.ext fun i => by simpa using h4 i
  have := LinearMap.congr_fun h5 1
  simp [hφ] at this

end Generic

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

open scoped Pointwise in

theorem noInv_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  intro D bkP i s hJ v hv A hA x hx
  by_contra hx0
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) (D.nd.plOm.2 v) hA
  let Bw := bkP.br i v hv
  have inj : Function.Injective Bw.toLL := Subtype.val_injective.comp Bw.eO.injective
  let ψ : FractionRing (D.ntw.O0 i) →+* ↥Bw.LL.1 := IsFractionRing.lift inj
  have hψ : ∀ a, ψ (algebraMap _ _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap inj a
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) ↥Bw.LL.1 := fun g => (Tmat i s g).map Bw.toLL
  have hM : ∀ g g', M (g * g') = M g * M g' := fun g g' => by
    simp only [M, ← Tgl_coe, map_mul, Units.val_mul, Matrix.map_mul]
  have hM1 : M 1 = 1 := by
    simp only [M, ← Tgl_coe, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let z : Fin D.R.r → ↥Bw.LL.1 := fun a => ψ (x a)
  have hz : ∀ g ∈ Dec (F := D.host.E) A, (M g).mulVec z = z := fun g hg => by
    funext a
    have := congrArg ψ (congrFun (hx g hg) a)
    simpa [Matrix.mulVec, dotProduct, map_sum, hψ, M, z] using this
  have hz0 : (M k⁻¹).mulVec z ≠ 0 := fun h => hx0 (by
    have h1 := congrArg (M k).mulVec h
    rw [Matrix.mulVec_mulVec, ← hM, mul_inv_cancel, hM1, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    funext a
    exact ψ.injective (by simpa [z] using congrFun h1 a))
  let τ : EmbV bkP i v hv := Bw.Kw.1.val.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split Bw.Kw.1.val)
  have hj := isJumpV_zero_of_invariant (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) _ hz0 (fun g => by
    have hg : k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹ ∈ Dec (F := D.host.E) A := by
      have h : (Bw.e.symm g : Gen.GE D.nd) • D.nd.plOm.1 v = D.nd.plOm.1 v := (Bw.e.symm g).2
      show (k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹) • A = A
      rw [← hk, mul_smul, inv_smul_smul, mul_smul, h]
    have e : repV bkP i v hv (Tgl i s) g ((M k⁻¹).mulVec z) =
        (M (Bw.e.symm g : Gen.GE D.nd)).mulVec ((M k⁻¹).mulVec z) := by
      simp only [M, ← Tgl_coe]
      rfl
    rw [e]
    conv_rhs => rw [← hz _ hg]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ← hM, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel, one_mul]) τ
  have := hJ v hv τ 0 hj
  omega

end GlobalTheory.InvJump

end
