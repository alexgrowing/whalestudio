import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR
namespace RDecomp

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem blocks_of_mem_R {r : GL (n ⊕ Fin c) k} (hr : r ∈ R k n c p) :
    ∃ x : GL n k, r.val.toBlocks₁₁ = x.val ∧ (r⁻¹).val.toBlocks₁₁ = (x⁻¹).val := by
  obtain ⟨x, u, hu, rfl⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R hr
  refine ⟨x, GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu, ?_⟩
  have e : (embX c x * u)⁻¹ = embX c x⁻¹ * (embX c x * u⁻¹ * (embX c x)⁻¹) := by
    rw [map_inv]; group
  rw [e]
  exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x⁻¹ (GlobalTheory.RootEx.Radical.conj_mem x (inv_mem hu))

def gpart (r : R k n c p) : GL n k :=
  ⟨(r : GL (n ⊕ Fin c) k).val.toBlocks₁₁, ((r : GL (n ⊕ Fin c) k)⁻¹).val.toBlocks₁₁,
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.mul_inv],
    by obtain ⟨x, h1, h2⟩ := blocks_of_mem_R r.2; rw [h1, h2, Units.inv_mul]⟩

theorem gpart_prodR (q : GL n k × N k n c p) : gpart (prodR p q) = q.1 :=
  Units.ext (GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul q.1 q.2.2)

theorem mem_N_of_mem_R (r : R k n c p) : (embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k) ∈ N k n c p := by
  obtain ⟨x, u, hu, e⟩ := GlobalTheory.RootEx.Radical.exists_of_mem_R r.2
  have : gpart r = x := Units.ext (by
    change (r : GL (n ⊕ Fin c) k).val.toBlocks₁₁ = _
    rw [e]; exact GlobalTheory.RootEx.Radical.toBlocks₁₁_embX_mul x hu)
  rw [this, e, inv_mul_cancel_left]
  exact hu

def upart (r : R k n c p) : N k n c p := ⟨(embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k), mem_N_of_mem_R r⟩

end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem continuous_gpart (p : ℕ) : Continuous (gpart (k := k) (n := n) (c := c) (p := p)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp continuous_subtype_val
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (GlobalTheory.RootEx.VolN.continuous_entry (Sum.inl i) (Sum.inl j)).comp (continuous_subtype_val.inv)

def prodRHomeo (p : ℕ) : GL n k × N k n c p ≃ₜ R k n c p where
  toFun := prodR p
  invFun r := (gpart r, upart r)
  left_inv q := by
    have h := gpart_prodR (c := c) q
    refine Prod.ext h (Subtype.ext ?_)
    change (embX c (gpart (prodR p q)))⁻¹ * (embX c q.1 * (q.2 : GL (n ⊕ Fin c) k)) = _
    rw [h, inv_mul_cancel_left]
  right_inv r := Subtype.ext (by
    change embX c (gpart r) * ((embX c (gpart r))⁻¹ * (r : GL (n ⊕ Fin c) k)) = _
    rw [mul_inv_cancel_left])
  continuous_toFun := Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun := (continuous_gpart p).prodMk (Continuous.subtype_mk
    ((GlobalTheory.RootEx.QuotStep.continuous_embX.comp (continuous_gpart p)).inv.mul continuous_subtype_val) _)

end

end RDecomp
open RDecomp

theorem finite_r : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts ((m.prod (volN ν n c p)).map (prodR p)) := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν hν m hm
  haveI := hν
  haveI := hm
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : BorelSpace (GL n k) := GlobalTheory.SplitFlip.borel_GL
  haveI : BorelSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.borel_GL
  haveI : SecondCountableTopology (GL n k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (n ⊕ Fin c) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : (volN ν n c p).IsHaarMeasure := GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν p
  haveI : LocallyCompactSpace (N k n c p) := (GlobalTheory.RootEx.VolN.isClosed_N p).locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  have e : ⇑(prodRHomeo (k := k) (n := n) (c := c) p) = prodR p := rfl
  rw [← e]
  exact Measure.IsFiniteMeasureOnCompacts.map _ (prodRHomeo p)

end GlobalTheory.HaarR
