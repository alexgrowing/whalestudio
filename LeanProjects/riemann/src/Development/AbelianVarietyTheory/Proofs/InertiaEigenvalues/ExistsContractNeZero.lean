import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContractMultilinearApply

noncomputable section

namespace GlobalTheory.SmGL.DepthZero

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.StepData ValuativeRel
open scoped TensorProduct

section Tensor

variable {α : Type} [Fintype α] [dec : DecidableEq α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def contract (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) : (⨂[ℂ] b, X b) →ₗ[ℂ] X a := GlobalTheory.MultilinearContraction.contract φ a

theorem contract_tprod (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (x : ∀ b, X b) :
    contract φ a (PiTensorProduct.tprod ℂ x) = (∏ b ∈ Finset.univ.erase a, φ b (x b)) • x a :=
  GlobalTheory.MultilinearContraction.contract_tprod φ a x

theorem exists_contract_ne_zero {w : ⨂[ℂ] b, X b} (hw : w ≠ 0) (a : α) :
    ∃ φ : ∀ a, X a →ₗ[ℂ] ℂ, contract φ a w ≠ 0 := by
  let b := fun i => Module.Free.chooseBasis ℂ (X i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr w p ≠ 0 := by
    by_contra! h
    exact hw (B.repr.injective (by ext p; simp [h p]))
  refine ⟨fun i => (b i).coord (p i), fun h => hp ?_⟩
  have key : (b a).coord (p a) ∘ₗ contract (fun i => (b i).coord (p i)) a = B.coord p := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, contract_tprod, map_smul,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  have := congrArg (fun L => L w) key
  simp only [LinearMap.comp_apply, h, map_zero, Module.Basis.coord_apply] at this
  exact this.symm

theorem contract_piTensor {Γ : α → Type} [∀ a, Group (Γ a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (φ : ∀ a, X a →ₗ[ℂ] ℂ) (a : α) (g : Γ a) (w : ⨂[ℂ] b, X b) :
    contract φ a (piTensor ρ (Pi.mulSingle a g) w) = ρ a g (contract φ a w) := by
  induction w using PiTensorProduct.induction_on with
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul_tprod c x =>
    simp only [map_smul, piTensor_tprod, contract_tprod, Pi.mulSingle_eq_same]
    congr 2
    exact Finset.prod_congr rfl fun b hb => by
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hb)]; simp

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_KOne₁ : IsCompact (KOne k n : Set (GL n k)) :=
  SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ isOpen_KOne) KOne_le_KO

theorem conj_mem_KOne₁ {w g : GL n k} (hw : w ∈ KO k n) (hg : g ∈ KOne k n) : w⁻¹ * g * w ∈ KOne k n := by
  refine mem_KOne.2 ?_
  have : (w⁻¹ * g * w).val - 1 = (w⁻¹).val * (g.val - 1) * w.val := by
    simp [mul_sub, sub_mul]
  rw [this]
  exact ((mem_KO.1 hw).2.mul_maxM (mem_KOne.1 hg)).mul_intM (mem_KO.1 hw).1

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem leviEmb_mem_KOne₁ (e : (Σ a, m a) ≃ n) {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) :
    leviEmb k e g ∈ KOne k n := by
  refine mem_KOne.2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := mem_KOne.1 (hg a) i j
    simpa [Matrix.sub_apply, Matrix.one_apply] using this
  · have h' : e ⟨a, i⟩ ≠ e ⟨b, j⟩ := fun h' => h (congrArg Sigma.fst (e.injective h'))
    simp [Matrix.sub_apply, leviEmb_apply_ne k e g h, Matrix.one_apply_ne h']

theorem deltaHalf_eq_one {g : Levi k m} (hg : ∀ a, g a ∈ KOne k (m a)) : deltaHalf k m g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => tame_det_of_mem_KOne (fun x hx => isUnram_absPow k _ x ?_) (hg a)
  simpa using Valuation.map_one_add_of_lt _ hx

theorem exists_fixed_of_parInd (e : (Σ a, m a) ≃ n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k m) W) {f : IndSp e ρ} (hf : f ∈ fixed (parInd e ρ) (KOne k n)) (h0 : f ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ ∀ g : Levi k m, (∀ a, g a ∈ KOne k (m a)) → ρ g w = w := by
  obtain ⟨x, hx⟩ : ∃ x, f.1.1 x ≠ 0 := by
    by_contra! h
    exact h0 (Subtype.ext (Subtype.ext (funext h)))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  refine ⟨f.1.1 c, fun h => hx (by rw [parInd_law, h]; simp), fun g hg => ?_⟩
  have h1 := parInd_law e ρ f ⟨_, leviEmb_mem_parab k e g⟩ c
  rw [leviProj_leviEmb, deltaHalf_eq_one hg, Units.val_one, one_smul] at h1
  have h2 := hf ⟨_, conj_mem_KOne₁ hc (leviEmb_mem_KOne₁ e hg)⟩
  have h3 := congrArg (fun F : IndSp e ρ => F.1.1 c) h2
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul] at h3
  rw [← h1, ← h3]
  group

theorem fixed_of_isSubquotient (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL n k) V} (h : IsSubquotient π (multiProd e σ))
    (hv : ∃ v ∈ fixed π (KOne k n), v ≠ 0) (a : α) : ∃ v ∈ fixed (σ a) (KOne k (m a)), v ≠ 0 := by
  obtain ⟨S, F, hF⟩ := h
  obtain ⟨v, hv, hv0⟩ := hv
  obtain ⟨u, rfl⟩ := hF v
  have hS : IsSmooth S.toRepresentation := fun y => by
    have := isSmooth_parInd e (piTensor σ) y.1
    convert this using 3 with g
    exact Subtype.ext_iff
  obtain ⟨y, hy, hyu⟩ := IwahoriOnto.exists_fixed_map_eq hS isCompact_KOne₁ F.toLinearMap u fun g hg => by
    have h1 := hv ⟨g, hg⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact (F.isIntertwining _ _ g u).trans h1
  have hy0 : y.1 ≠ 0 := fun h => hv0 (by
    have : y = 0 := Subtype.ext h
    rw [this, map_zero] at hyu
    exact hyu.symm)
  obtain ⟨w, hw0, hw⟩ := exists_fixed_of_parInd e (piTensor σ) (f := y.1)
    (fun g => congrArg Subtype.val (hy g)) hy0
  obtain ⟨φ, hφ⟩ := exists_contract_ne_zero hw0 a
  refine ⟨_, fun g => ?_, hφ⟩
  rw [← contract_piTensor, hw _ fun b => ?_]
  · simp
  · by_cases hb : b = a
    · subst hb; simp
    · rw [Pi.mulSingle_eq_of_ne hb]; exact one_mem _

end GlobalTheory.SmGL.DepthZero

namespace GlobalTheory.SmGL

open GlobalTheory.PRep GlobalTheory.SplitRead

theorem depthZeroSupport : GlobalTheory.Published.DepthZeroSupport := by
  intro k _ _ _ _ n π s d σ h hv a
  obtain ⟨-, -, e, he⟩ := h
  exact DepthZero.fixed_of_isSubquotient e (fun a => (σ a).π) he hv a

end GlobalTheory.SmGL

end
