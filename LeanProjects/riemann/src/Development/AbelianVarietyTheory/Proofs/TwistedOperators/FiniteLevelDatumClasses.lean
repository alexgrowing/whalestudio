import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

def vmvBil (E : Type) [Field E] [NumberField E] (n r : ℕ) :
    (Fin n → E) →ₗ[𝓞 E] (Fin r → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin r) E :=
  LinearMap.mk₂ (𝓞 E) (fun v u => vecMulVec v u)
    (fun v v' u => by ext i j; simp [vecMulVec, add_mul])
    (fun a v u => by ext i j; simp [vecMulVec, smul_mul_assoc])
    (fun v u u' => by ext i j; simp [vecMulVec, mul_add])
    (fun a v u => by ext i j; simp [vecMulVec, mul_smul_comm])

theorem tens_quot_finite {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)
    (hΛ : Λ.FG) (hL : L.FG) (𝔞 𝔪 : Ideal (𝓞 E)) (hm : 𝔪 ≠ ⊥) :
    Finite (tens Λ (𝔞 • L) ⧸ (tens Λ ((𝔞 * 𝔪) • L)).addSubgroupOf (tens Λ (𝔞 • L))) := by
  set A := tens Λ (𝔞 • L) with hA
  set B := tens Λ ((𝔞 * 𝔪) • L) with hB
  have hM : (Submodule.map₂ (vmvBil E n r) Λ L).FG := hΛ.map₂ _ hL
  have hMZ : ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).FG := hM.restrictScalars
  have hle : A.toIntSubmodule ≤ (Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ := by
    intro x hx
    have hsub : A ≤ ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).toAddSubgroup := by
      rw [hA, tens, AddSubgroup.closure_le]
      rintro y ⟨v, hv, u, hu, rfl⟩
      exact Submodule.apply_mem_map₂ (vmvBil E n r) hv (Submodule.smul_le_right hu)
    exact hsub hx
  have hAfg : A.toIntSubmodule.FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ hMZ)) _ hle
  haveI : AddGroup.FG A := by
    have : Module.Finite ℤ A.toIntSubmodule := Module.Finite.iff_fg.mpr hAfg
    exact (Module.Finite.iff_addGroup_fg).mp this
  set N := Ideal.absNorm 𝔪 with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
  have hNA : ∀ x ∈ A, N • x ∈ B := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨v, hv, N • u, ?_, ?_⟩
      · have h1 : ((N : 𝓞 E)) • u ∈ 𝔪 • (𝔞 • L) := Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hu
        rw [← Submodule.mul_smul, mul_comm] at h1
        rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      · ext i j; simp [vecMulVec]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hNA x x.2

theorem lvCls_finite : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  intro D S T C Lv
  exact tens_quot_finite _ _ (Submodule.fg_span (Set.finite_range _)) C.X.Λ_fg _ _ Lv.ne_bot

end GlobalTheory.LiftLevel

end
