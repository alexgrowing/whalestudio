import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel Matrix NumberField
open scoped Pointwise TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.FrameCong

variable {D : D7}

theorem intAt_mul_mem {S : HSp D} {L : Lat S} {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (fun i => a * y i) ∈ latV S L (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have hint : a * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAt D (· = v) := by
      refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
      rw [RingHom.map_mul]
      exact FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩)
    have h := FrameLat.int_mul_mem hint hx
    have h1 : ∀ i, (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D (x i) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i) := fun i => by
      change _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simpa only [mul_assoc, h1] using h
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem inc_mul_mem {S : HSp D} {L : Lat S} {P : Pl D → Prop} {𝔪 : Ideal (𝓞 D.host.E)} {m : 𝓞 D.host.E} (hm : m ∈ 𝔪)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα0, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα0, 1, rfl, m • x, Submodule.smul_mem_smul hm hx, ?_⟩
    funext i
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul]
    rfl
  | zero => simp only [Pi.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => simp only [Pi.add_apply, mul_add]; exact add_mem hx hy
  | neg x _ hx => simp only [Pi.neg_apply, mul_neg]; exact neg_mem hx

theorem sub_one_mulVec_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (n : Type) [Fintype n]
    [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n),
    β.IsLat L (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ),
    (∃ m ∈ 𝔪, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k],
      (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E))) →
    ∀ k₀ : GL n 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d) →
    ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = p.v) →
    (fun i => p.e * ((mt S (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) - 1) *ᵥ y) i) ∈
      latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p S L n _ _ β hβ 𝔪 d ⟨m, hm, hmd⟩ k₀ hk y hy
  have hpi : ∀ x : n → k, x ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) ↔ ∀ j, x j ∈ 𝒪[k] := by
    intro x
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    refine forall_congr' fun j => ⟨?_, fun h => ⟨⟨x j, h⟩, rfl⟩⟩
    rintro ⟨z, hz⟩
    rw [← hz]; exact z.2
  set g : GL n k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ with hg
  set Y : Fin S.rank → k := fun i => p.pr (y i) with hY
  set x : n → k := β.b' *ᵥ Y with hx
  have hbx : β.b *ᵥ x = Y := by rw [hx, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
  have hxint : ∀ j, x j ∈ 𝒪[k] := by
    rw [← hpi, hβ x, hbx]
    simp only [hY, p.sec_pr]
    exact intAt_mul_mem (FrameLat.e_mem_intAt p) hy
  let x₀ : n → 𝒪[k] := fun j => ⟨x j, hxint j⟩
  have hz : ∀ i, ((k₀.1 - 1) *ᵥ x₀) i ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d := fun i =>
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hk i j)
  choose c hc hcz using fun i => hmd _ (hz i)
  have hgx : (g.val - 1) *ᵥ x = p.pr (incA D (m : D.host.E)) • c := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← hcz i]
    have h1 : g.val - 1 = (k₀.1 - 1).map (algebraMap 𝒪[k] k) := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    rw [h1]
    exact (RingHom.map_mulVec (algebraMap 𝒪[k] k) (k₀.1 - 1) x₀ i).symm
  have hpr : ∀ i, p.pr (((mt S (β.gl g) - 1) *ᵥ y) i) = p.pr (incA D (m : D.host.E)) * (β.b *ᵥ c) i := by
    intro i
    rw [RingHom.map_mulVec, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), β.gl_mat g]
    have h2 : β.b * g.val * β.b' - 1 = β.b * (g.val - 1) * β.b' := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, β.bb']
    rw [h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (β.b *ᵥ ((g.val - 1) *ᵥ x)) i = _
    rw [hgx, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hc' := (hβ c).1 ((hpi c).2 hc)
  have h := inc_mul_mem hm hc'
  have heq : (fun i => p.e * ((mt S (β.gl g) - 1) *ᵥ y) i) =
      fun i => incA D (m : D.host.E) * p.sec ((β.b *ᵥ c) i) := by
    funext i
    rw [← p.sec_pr, hpr, mul_comm (incA D _), FrameLat.sec_mul_right, mul_comm]
  rw [heq]
  exact h

end GlobalTheory.FinPl.FrameCong
