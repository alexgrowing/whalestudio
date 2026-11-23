import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct

namespace GlobalTheory.St.G.LinkCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)

theorem mem_Mq (x : Fin (D.R.N 0) → D.host.E) : x ∈ Mq wt ↔ (∑ j, x j • qFr wt j) ∈ (VS D).L0 := by
  simp [Mq, Fintype.linearCombination_apply]

theorem embA_add (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (x + y) = embA X wt ιA x + embA X wt ιA y := by
  simp [embA, add_smul, Finset.sum_add_distrib]

theorem embA_smul (a : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (a • x) = ιA.symm a • embA X wt ιA x := by
  simp [embA, Finset.smul_sum, mul_smul]

theorem embA_rep (h : X.B.I.Gf)
    (y : UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
    (hr : RepF X wt ιA h y) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    X.B.I.fmat h *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  unfold embA
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hr _, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ∀ f : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F, ιA.symm (∑ j, f j) = ∑ j, ιA.symm (f j) :=
    fun f => map_sum ιA.symm.toAddEquiv.toAddMonoidHom f Finset.univ
  simp only [Matrix.mulVec, dotProduct, hs, RingEquiv.map_mul, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem embA_rat (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) =
      incl X.B.I (X.crd (∑ j, x j • qFr wt j)) := by
  have h1 : ∀ a : D.host.E, ιA.symm (inclE (F := D.host.F) (Ad D.host.F) a) =
      inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm a) := by
    intro a
    rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]
  funext i
  simp [embA, qA, incl, HidaSetting.crd, crdOf, h1, Finset.sum_apply]

theorem embA_mem (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) (hx : x ∈ Mq wt) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) ∈ X.B.I.Lf := by
  rw [embA_rat X wt ιA hι]
  have hL : X.crd (∑ j, x j • qFr wt j) ∈ X.B.I.L := by
    rw [X.L_eq]
    simp only [HidaSetting.crd, crdOf, RingEquiv.apply_symm_apply, Module.Basis.sum_repr]
    exact (mem_Mq wt x).1 hx
  exact Submodule.subset_span ⟨⟨_, hL⟩, rfl⟩

theorem link_unique (u : D.what₂.Word) (Fr Fr' : FrQ D wt) (h : FrLink X u wt ιA Fr) (h' : FrLink X u wt ιA Fr') :
    Fr.eps = Fr'.eps ∧ Fr.psi = Fr'.psi ∧
      (∀ i, embA X wt ιA (Fr.b i) - embA X wt ιA (Fr'.b i) ∈ mL X.B.I X.B.g) ∧
      ∀ i, embA X wt ιA (Fr.bd i) - embA X wt ιA (Fr'.bd i) ∈ mL X.B.I X.B.g := by
  refine ⟨h.1.trans h'.1.symm, funext fun a => (h.2.2.2 a).trans (h'.2.2.2 a).symm, fun i => ?_, fun i => ?_⟩
  · simpa using (mL X.B.I X.B.g).sub_mem (h.2.1 i) (h'.2.1 i)
  · simpa using (mL X.B.I X.B.g).sub_mem (h.2.2.1 i) (h'.2.2.1 i)

theorem level_rank : X.B.g = D.host.g 0 * D.host.g 1 ∧ D.R.N 0 = D.R.k :=
  ⟨X.g_eq, by simp [Ranks.N]⟩

end GlobalTheory.St.G.LinkCheck

end
