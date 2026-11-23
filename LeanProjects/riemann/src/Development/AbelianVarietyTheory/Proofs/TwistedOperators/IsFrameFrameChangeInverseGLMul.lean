import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapAFrPMulFrPinv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ReVec

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem hatL_mulVec_mem (M : Matrix (Fin n) (Fin n) E) (Λ Λ' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    M.map (Algebra.TensorProduct.includeLeftRingHom : E →+* E ⊗[F] Formalism.L2.Herm.Af F) *ᵥ x ∈
      Formalism.L2.Herm.hatL (F := F) Λ' := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at *
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ z, h z hz, ?_⟩
    funext i
    simp [Matrix.mulVec, dotProduct, Formalism.UG.inclE, map_sum]
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hy

end General

theorem sum_smul_frame_frP {D : D7} (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (y : Fin S.rank → D.host.E) :
    ∑ i, y i • b i = ∑ j, (frP S b *ᵥ y) j • S.frame j := by
  simp only [frP, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [← S.frame.sum_repr (b i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

theorem mem_stdL_iff {D : D7} (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V)
    (hO : StdFrame.OrthFrame (reS S b)) (y : Fin S.rank → D.host.E) :
    y ∈ stdL D.host.E S.rank ↔ ∑ i, y i • b i ∈ S.L0 := by
  have hpi : (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)) =
      stdL D.host.E S.rank := by
    apply le_antisymm
    · intro x hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun a _ => ?_
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a trivial)
      have : (Pi.single a (x a) : Fin S.rank → D.host.E) = c • (Pi.single a 1 : Fin S.rank → D.host.E) := by
        rw [← Pi.single_smul, ← hc, Algebra.smul_def, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, rfl⟩ j -
      by_cases h : j = a
      · subst h
        exact Submodule.mem_one.2 ⟨1, by simp⟩
      · simp [h]
  rw [← hpi, Submodule.mem_pi]
  exact (⟨fun k a => k a trivial, fun k a _ => k a⟩ : _ ↔ _).trans (hO.mem_iff (V := reS S b) y).symm

theorem isFrame_frPinvGL_mul : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := by
  intro D S b βS ΛS hO hΛ hfr
  change Formalism.L2.DIV.IsFrame _ (stdL D.host.E S.rank)
  have hA : ∀ y ∈ stdL D.host.E S.rank, frP S b *ᵥ y ∈ ΛS := by
    intro y hy
    have h1 : frP S b *ᵥ y ∈ (ΛS : Set (Fin S.rank → D.host.E)) := by
      rw [hΛ]
      show ∑ j, (frP S b *ᵥ y) j • S.frame j ∈ S.L0
      rw [← sum_smul_frame_frP]
      exact (mem_stdL_iff S b hO y).1 hy
    exact h1
  have hB : ∀ y ∈ ΛS, frPinv S b *ᵥ y ∈ stdL D.host.E S.rank := by
    intro y hy
    rw [mem_stdL_iff S b hO, sum_smul_frame_frP, Matrix.mulVec_mulVec, frameMatrix_mul_frameMatrixInv, Matrix.one_mulVec]
    have h1 : y ∈ (ΛS : Set (Fin S.rank → D.host.E)) := hy
    rw [hΛ] at h1
    exact h1
  unfold Formalism.L2.DIV.IsFrame at hfr ⊢
  intro x
  have hinv : ((frPinvGL S b * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val *ᵥ x =
      (βS⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val *ᵥ ((frP S b).map (eToEAf D) *ᵥ x) := by
    rw [_root_.mul_inv_rev, Units.val_mul, frPinvGL_inv_val, Matrix.mulVec_mulVec]
  rw [hinv, ← hfr]
  constructor
  · intro hx
    exact hatL_mulVec_mem (frP S b) _ ΛS hA x hx
  · intro hx
    have h2 := hatL_mulVec_mem (F := D.host.F) (frPinv S b) ΛS _ hB _ hx
    have h3 : (frPinv S b).map (eToEAf D) *ᵥ ((frP S b).map (eToEAf D) *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, frPinv_mul_frP, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.one_mulVec]
    exact h3 ▸ h2

end GlobalTheory.AdSpan.ReVec
