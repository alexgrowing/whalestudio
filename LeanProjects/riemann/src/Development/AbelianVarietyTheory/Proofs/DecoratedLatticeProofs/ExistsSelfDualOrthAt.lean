import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrthSumLat

variable {D : D7}

theorem rat_mulVec_mem_latV {S T : HSp D} (m : Matrix (Fin T.rank) (Fin S.rank) D.host.E) {L : Lat S} {L' : Lat T}
    (h : ∀ x ∈ L, m *ᵥ x ∈ L') {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (rat m : Mx D T.rank S.rank) *ᵥ y ∈ latV T L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hα', c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨α, hα, hα', 1, rfl, m *ᵥ x, h x hx, ?_⟩
    funext i
    simp only [mulVec, dotProduct, one_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] m i j) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [mulVec_neg]; exact neg_mem hx

theorem dsum_eq' {S : HSp D} (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA' {S A B : HSp D} (o : OrthDec S A B) (a : Fin A.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (o.iA *ᵥ a) ⬝ᵥ S.gram *ᵥ y = star a ⬝ᵥ A.gram *ᵥ (o.qA *ᵥ y) := by
  have h : A.gram * o.qA = o.iAᴴ * S.gram := by
    rw [OrthDec.qA, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det A), Matrix.one_mul]
  rw [mulVec_mulVec, h, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star a)]

theorem exists_selfDual_orthAt : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B) (LA : Lat A) (LB : Lat B), IsSelfDualC A LA →
    IsSelfDualC B LB → ∃ L : Lat S, IsSelfDualC S L ∧ ∀ v, OrthAt o L LA LB v := by
  intro D S A B o LA LB hA hB
  let fA := (mulVecLin o.iA).restrictScalars (𝓞 D.host.E)
  let fB := (mulVecLin o.iB).restrictScalars (𝓞 D.host.E)
  have hsum : ∀ y : Fin S.rank → D.host.E, y = o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.iA_qA_add, one_mulVec]
  have hiA : ∀ x ∈ LA, o.iA *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_left ⟨x, hx, rfl⟩
  have hiB : ∀ x ∈ LB, o.iB *ᵥ x ∈ LA.map fA ⊔ LB.map fB := fun x hx => Submodule.mem_sup_right ⟨x, hx, rfl⟩
  have hmem : ∀ y, y ∈ LA.map fA ⊔ LB.map fB ↔ o.qA *ᵥ y ∈ LA ∧ o.qB *ᵥ y ∈ LB := fun y => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
      change o.qA *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LA ∧ o.qB *ᵥ (o.iA *ᵥ a + o.iB *ᵥ b) ∈ LB
      simp only [mulVec_add, mulVec_mulVec, o.qA_iA, o.qA_iB, o.qB_iA, o.qB_iB, one_mulVec, zero_mulVec, add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rw [hsum y]; exact add_mem (hiA _ h.1) (hiB _ h.2)
  refine ⟨LA.map fA ⊔ LB.map fB, ⟨⟨(hA.1.fg.map _).sup (hB.1.fg.map _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩,
    fun v y => ⟨fun hy => ⟨rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).1) hy,
      rat_mulVec_mem_latV _ (fun x hx => ((hmem x).1 hx).2) hy⟩, fun h => ?_⟩⟩
  · rw [eq_top_iff]
    intro y _
    have key : ∀ {C : HSp D} (m : Matrix (Fin S.rank) (Fin C.rank) D.host.E) (LC : Lat C), IsSelfDualC C LC →
        (∀ x ∈ LC, m *ᵥ x ∈ LA.map fA ⊔ LB.map fB) → ∀ z, m *ᵥ z ∈ Submodule.span D.host.E
          ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E)) := by
      intro C m LC hC hm z
      have hz : z ∈ Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) := by rw [hC.1.span_eq_top]; trivial
      have : Submodule.span D.host.E (LC : Set (Fin C.rank → D.host.E)) ≤ Submodule.comap (mulVecLin m)
          (Submodule.span D.host.E ((LA.map fA ⊔ LB.map fB : Lat S) : Set (Fin S.rank → D.host.E))) :=
        Submodule.span_le.2 fun x hx => Submodule.subset_span (hm x hx)
      exact this hz
    rw [hsum y]
    exact add_mem (key _ LA hA hiA _) (key _ LB hB hiB _)
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hA.2 _).1 ((hmem y).1 hy).1 a ha
    obtain ⟨d, hd⟩ := (hB.2 _).1 ((hmem y).1 hy).2 b hb
    refine ⟨c + d, ?_⟩
    rw [dsum_eq'] at hc hd ⊢
    change _ = star (o.iA *ᵥ a + o.iB *ᵥ b) ⬝ᵥ _
    have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
    rw [star_add, add_dotProduct, pair_iA', e2, ← hc, ← hd]
    rfl
  · refine (hmem y).2 ⟨(hA.2 _).2 fun a ha => ?_, (hB.2 _).2 fun b hb => ?_⟩
    · have := h _ (hiA a ha)
      rwa [dsum_eq', pair_iA', ← dsum_eq'] at this
    · have := h _ (hiB b hb)
      have e2 : star (o.iB *ᵥ b) ⬝ᵥ S.gram *ᵥ y = star b ⬝ᵥ B.gram *ᵥ (o.qB *ᵥ y) := pair_iA' o.symm b y
      rwa [dsum_eq', e2, ← dsum_eq'] at this
  · have e : y = o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, o.sum_eq_one, one_mulVec]
    rw [e]
    exact add_mem (rat_mulVec_mem_latV _ hiA h.1) (rat_mulVec_mem_latV _ hiB h.2)

end GlobalTheory.OrthSumLat
