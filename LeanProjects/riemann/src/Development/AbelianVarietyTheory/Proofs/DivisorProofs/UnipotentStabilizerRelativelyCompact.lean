import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv.PowSet

theorem mul_quad {R A : Type} [CommRing R] [Ring A] [Algebra R A] (M : A) (h : M ^ 3 = 0) (s t s' t' : R) :
    (1 + s • M + t • M ^ 2) * (1 + s' • M + t' • M ^ 2) = 1 + (s + s') • M + (t + t' + s * s') • M ^ 2 := by
  have h1 : M * M ^ 2 = 0 := by rw [← h, pow_succ' M 2]
  have h2 : M ^ 2 * M = 0 := by rw [← h, pow_succ M 2]
  have h3 : M ^ 2 * M ^ 2 = 0 := by rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, h, zero_mul]
  have h4 : M * M = M ^ 2 := (pow_two M).symm
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h1, h2, h3, h4, smul_zero, add_zero,
    add_smul, smul_smul, mul_comm s' s]
  module

theorem mul_mem_intAt {F : Type} [Field F] [NumberField F] {v : Pl F} {a b : AF F}
    (ha : a ∈ GlobalTheory.LatAtClosed.intAt F v) (hb : b ∈ GlobalTheory.LatAtClosed.intAt F v) :
    a * b ∈ GlobalTheory.LatAtClosed.intAt F v := by
  refine ⟨fun u hu => ?_, ?_⟩
  · have := ha.1 u hu
    rw [smul_eq_mul] at this ⊢
    rw [← mul_assoc, this, zero_mul]
  · rw [map_mul]; exact mul_mem ha.2 hb.2

theorem exists_compact_zpowers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Y : Spc F E n) (v : Pl F) (x : Fin n → E) (q : stabAt σ Y (evFin F v) x), (mat q.1.1 - 1) ^ 3 = 0 →
    ∃ P : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact P ∧
      ∀ g ∈ Subgroup.zpowers q, mat g.1.1 ∈ P ∧ mat g.1.1⁻¹ ∈ P := by
  intro F E _ _ _ _ _ σ n Y v x q hq
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  set M : Matrix (Fin n) (Fin n) (AE F E) := mat q.1.1 - 1 with hM
  let f : AF F × AF F → Matrix (Fin n) (Fin n) (AE F E) := fun st => 1 + st.1 • M + st.2 • M ^ 2
  have hf : Continuous f := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun st : AF F × AF F =>
      (1 : Matrix (Fin n) (Fin n) (AE F E)) i j + st.1 • M i j + st.2 • (M ^ 2) i j
    exact (continuous_const.add (continuous_fst.smul continuous_const)).add (continuous_snd.smul continuous_const)
  let R : Set (AF F) := GlobalTheory.LatAtClosed.intAt F v
  let P := f '' (R ×ˢ R)
  let S : Subgroup (stabAt σ Y (evFin F v) x) :=
    { carrier := {g | mat g.1.1 ∈ P}
      one_mem' := ⟨(0, 0), ⟨zero_mem (GlobalTheory.LatAtClosed.intAt F v), zero_mem (GlobalTheory.LatAtClosed.intAt F v)⟩, by
        show f (0, 0) = mat (1 : UA σ Y.J)
        rw [GlobalTheory.StabHaar.mat_one]; simp [f]⟩
      mul_mem' := by
        rintro g h ⟨⟨s, t⟩, ⟨hs, ht⟩, hg⟩ ⟨⟨s', t'⟩, ⟨hs', ht'⟩, hh⟩
        refine ⟨(s + s', t + t' + s * s'), ⟨add_mem hs hs', add_mem (add_mem ht ht') (mul_mem_intAt hs hs')⟩, ?_⟩
        show _ = mat (g.1.1 * h.1.1)
        rw [GlobalTheory.StabHaar.mat_mul, ← hg, ← hh]
        exact (mul_quad M hq s t s' t').symm
      inv_mem' := by
        rintro g ⟨⟨s, t⟩, ⟨hs, ht⟩, hg⟩
        refine ⟨(-s, s * s - t), ⟨neg_mem hs, sub_mem (mul_mem_intAt hs hs) ht⟩, ?_⟩
        show _ = mat g.1.1⁻¹
        have h1 : mat g.1.1 * f (-s, s * s - t) = 1 := by
          rw [← hg]
          refine (mul_quad M hq s t (-s) (s * s - t)).trans ?_
          rw [add_neg_cancel, show t + (s * s - t) + s * -s = 0 by ring]; simp
        have h2 : mat g.1.1⁻¹ * mat g.1.1 = 1 := by
          rw [← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one]
        rw [← one_mul (f _), ← h2, mul_assoc, h1, mul_one] }
  have hqS : q ∈ S := by
    refine ⟨(GlobalTheory.LatVac.liftV v 1, 0), ⟨⟨GlobalTheory.LatVac.at_liftV v 1, ?_⟩, zero_mem (GlobalTheory.LatAtClosed.intAt F v)⟩, ?_⟩
    · show evFin F v (GlobalTheory.LatVac.liftV v 1) ∈ _
      rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
    · have h : At (evFin F v) M := q.1.2
      have h' : GlobalTheory.LatVac.liftV v 1 • M = M := GlobalTheory.ThK.partFin_of_at h
      show 1 + GlobalTheory.LatVac.liftV v 1 • M + (0 : AF F) • M ^ 2 = _
      rw [h', zero_smul, add_zero, hM, add_sub_cancel]
  refine ⟨P, ((GlobalTheory.LatAtClosed.isCompact_intAt v).prod (GlobalTheory.LatAtClosed.isCompact_intAt v)).image hf, fun g hg => ?_⟩
  have hgS : g ∈ S := (Subgroup.zpowers_le.2 hqS) hg
  exact ⟨hgS, S.inv_mem hgS⟩

end GlobalTheory.ThK.LemF.QuotInv.PowSet
