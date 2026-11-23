import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct Pointwise

namespace UpperTheory.TNZ

namespace P_indExt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hne : ((ϖ : k) ^ r) ≠ 0 := pow_ne_zero _ fun h => hϖ.ne_zero (Subtype.ext h)
  have e : {x : k | InPow r x} = ((ϖ : k) ^ r) • (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_ofPred_eq, InPow, Set.mem_smul_set, smul_eq_mul]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      exact ⟨(z : k), z.2, by simp only [map_mul, map_pow]; rw [mul_comm]; rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨ϖ ^ r * ⟨z, hz⟩, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), by simp only [map_mul, map_pow]; rfl⟩
  have hO : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  rw [e]
  exact hO.smul₀ hne

theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩ ⋂ i, ⋂ j,
      (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  exact (isOpen_inPow r).preimage ((Units.continuous_val.matrix_elem i j).sub continuous_const)

theorem one_mem_KC (n r : ℕ) : (1 : GL (Fin n) k) ∈ KC k n r := by
  refine ⟨one_mem _, fun i j => ⟨0, zero_mem _, ?_⟩⟩
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

section Ext

variable {n : ℕ} (G : Grp k n) {X : Fin G.s → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  (σ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (X a))

def extFun (φ : ↥(KO k (Fin n)) → ℂ) (v : ⨂[ℂ] a, X a) (x : GL (Fin n) k) : ⨂[ℂ] a, X a :=
  (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e (MultiIrr.exists_parab_mul G.e x).choose) : ℂ) •
    piTensor σ (leviProj k G.e (MultiIrr.exists_parab_mul G.e x).choose)
      (φ ⟨(MultiIrr.exists_parab_mul G.e x).choose_spec.choose,
        (MultiIrr.exists_parab_mul G.e x).choose_spec.choose_spec.1⟩ • v)

variable {G σ}

theorem expr_eq (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v)
    (p p' : parab k G.e) (w w' : GL (Fin n) k) (hw : w ∈ KO k (Fin n)) (hw' : w' ∈ KO k (Fin n))
    (he : (p : GL (Fin n) k) * w = p' * w') :
    (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p') : ℂ) • piTensor σ (leviProj k G.e p') (φ ⟨w', hw'⟩ • v) =
      (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p) : ℂ) • piTensor σ (leviProj k G.e p) (φ ⟨w, hw⟩ • v) := by
  obtain ⟨hφ1, -⟩ := hφ
  obtain ⟨q, rfl⟩ : ∃ q : parab k G.e, p = p' * q := ⟨p'⁻¹ * p, (mul_inv_cancel_left p' p).symm⟩
  have hw'eq : w' = (q : GL (Fin n) k) * w := by
    rw [Subgroup.coe_mul, mul_assoc] at he
    exact (mul_left_cancel he).symm
  have hqK : (q : GL (Fin n) k) ∈ KO k (Fin n) := by
    have : (q : GL (Fin n) k) = w' * w⁻¹ := by rw [hw'eq, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hw' (inv_mem hw)
  subst hw'eq
  have h1 : φ ⟨(q : GL (Fin n) k) * w, hw'⟩ = G.lam (q : GL (Fin n) k) * φ ⟨w, hw⟩ :=
    hφ1 ⟨q, hqK⟩ ⟨hqK, q.2⟩ ⟨w, hw⟩
  have hP' := hP k G.s n G.d G.hd q hqK
  have hδ : deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e q) = 1 := hP'.2
  have hρ : piTensor σ (leviProj k G.e q) v = G.lam (q : GL (Fin n) k) • v := by
    rw [hv _ hP'.1, hL k n G q hqK]
  rw [(leviProj k G.e).map_mul p' q, (deltaHalf k (fun a => Fin (G.d a))).map_mul, hδ, mul_one,
    (piTensor σ).map_mul, Module.End.mul_apply, map_smul (piTensor σ (leviProj k G.e q)), hρ, h1, smul_smul, mul_comm]

theorem extFun_mul (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v)
    (p : parab k G.e) (w : GL (Fin n) k) (hw : w ∈ KO k (Fin n)) :
    extFun G σ φ v ((p : GL (Fin n) k) * w) =
      (deltaHalf k (fun a => Fin (G.d a)) (leviProj k G.e p) : ℂ) • piTensor σ (leviProj k G.e p) (φ ⟨w, hw⟩ • v) := by
  obtain ⟨hw', he⟩ := (MultiIrr.exists_parab_mul G.e ((p : GL (Fin n) k) * w)).choose_spec.choose_spec
  exact expr_eq hL hP hφ hv p _ w _ hw hw' he

theorem extFun_mem (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) :
    extFun G σ φ v ∈ indSpace (parab k G.e)
      ((twist (piTensor σ) (deltaHalf k (fun a => Fin (G.d a)))).comp (leviProj k G.e)) := by
  intro h g
  obtain ⟨p, w, hw, rfl⟩ := MultiIrr.exists_parab_mul G.e g
  rw [← mul_assoc, ← Subgroup.coe_mul, extFun_mul hL hP hφ hv (h * p) w hw, extFun_mul hL hP hφ hv p w hw]
  generalize φ ⟨w, hw⟩ • v = x
  rw [MonoidHom.comp_apply, twist_apply, map_smul, smul_smul, (leviProj k G.e).map_mul,
    (deltaHalf k (fun a => Fin (G.d a))).map_mul, Units.val_mul, (piTensor σ).map_mul, Module.End.mul_apply]

theorem exists_ext (hL : LeviSubgroupRestriction) (hP : ParabolicInductionKernel) {φ : ↥(KO k (Fin n)) → ℂ} (hφ : φ ∈ G.V0sp)
    {v : ⨂[ℂ] a, X a}
    (hv : ∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) :
    ∃ F : IndSp G.e (piTensor σ), ∀ κ : ↥(KO k (Fin n)), F.1.1 κ = φ κ • v := by
  have hφ' := hφ
  obtain ⟨-, hφ2⟩ := hφ'
  refine ⟨⟨⟨extFun G σ φ v, extFun_mem hL hP hφ hv⟩, ?_⟩, fun κ => ?_⟩
  · refine mem_smoothPart_of_nhds (Filter.mem_of_superset ((isOpen_KC n G.lev).mem_nhds (one_mem_KC n G.lev))
      fun u hu => ?_)
    refine Subtype.ext (funext fun x => ?_)
    show extFun G σ φ v (x * u) = extFun G σ φ v x
    obtain ⟨p, w, hw, rfl⟩ := MultiIrr.exists_parab_mul G.e x
    have h2 : φ ⟨w * u, mul_mem hw hu.1⟩ = φ ⟨w, hw⟩ := hφ2 ⟨w, hw⟩ ⟨u, hu.1⟩ hu
    rw [mul_assoc, extFun_mul hL hP hφ hv p (w * u) (mul_mem hw hu.1), h2, extFun_mul hL hP hφ hv p w hw]
  · have h := extFun_mul hL hP hφ hv 1 κ κ.2
    rw [Subgroup.coe_one, one_mul] at h
    show extFun G σ φ v κ = _
    rw [h, map_one, map_one, map_one, Units.val_one, one_smul, Module.End.one_apply]

end Ext

end P_indExt

theorem step_indExt : InductionExtension := by
  intro hL hP k _ _ _ _ n G X _ _ σ v hv φ hφ
  exact P_indExt.exists_ext hL hP hφ hv

end UpperTheory.TNZ
