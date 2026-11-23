import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lastCol {n : ℕ} (u : MirUin k n) : Fin n → k :=
  fun i => (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

theorem continuous_lastCol (n : ℕ) : Continuous (lastCol k (n := n)) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun u : MirUin k n =>
      (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact h.matrix_elem _ _

theorem thetaA_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (u : MirUin k n) :
    thetaA k ψ a u = Circle.toUnits (ψ (a ⬝ᵥ lastCol k u)) := by
  obtain ⟨w, hw⟩ : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n := Subgroup.mem_subgroupOf.1 u.2
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hw.symm
  have hcol : lastCol k u = w.toAdd := by
    funext i
    simp only [lastCol, ← hw]
    exact unip_apply_castSucc_last k n w i
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)).toAdd)) = _
  rw [key, hcol]

theorem isOpen_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ψ x = 1 := hx
  have ht : Filter.Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  filter_upwards [ht (cball_mem_nhds s)] with y hy
  have h1 : ψ (y - x) = 1 := hs _ hy
  have h2 : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  show ψ y = 1
  rw [h2, h1, hx', one_mul]

theorem thetaOpen : ThetaOpen k := by
  intro ψ hψ n a
  have hc : Continuous fun u : MirUin k n => a ⬝ᵥ lastCol k u := by
    have h := continuous_lastCol k n
    simp only [dotProduct]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp h)
  have he : ((thetaA k ψ a).ker : Set (MirUin k n)) =
      (fun u : MirUin k n => a ⬝ᵥ lastCol k u) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, thetaA_apply, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (isOpen_addChar_eq_one k ψ hψ).preimage hc

end GlobalTheory.CompanionTheory.BZFun

end
