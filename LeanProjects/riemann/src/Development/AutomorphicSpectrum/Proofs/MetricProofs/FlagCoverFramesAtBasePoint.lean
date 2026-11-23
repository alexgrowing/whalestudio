import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorOfRegularMatrixValueStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem regAt_valAt_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  obtain ⟨h0, -, v0, -, hst⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, v0⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨-, r, -, v⟩ := hst _ _ hfa ih1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨r, v.trans (by rw [ih2])⟩

theorem coE_regAt_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal zb) → M.GoodAt F (mCoordIdeal (zb ∘ Cv.v)) → ∀ (p : Ψ × Fin N) (q : Σ k, ι k) (r : Σ k, ι' k), RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧ valAt M'.x (coE Cv F' F p q r) zb = ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2), valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb F' F hz hF' hF hG' hG p q r
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M'.x zb hz
  have hT : ∀ a b, RegAt M'.x (mCoordIdeal zb) (trMat Cv F' F p.1 a b) := fun a b =>
    (Cv.agree zb hz F' F hF' hF hG' hG p.1 a b).1
  have hmin := fun I I' => GlobalTheory.T.minor_of_regular_matrix_value _ _ _ M'.x zb N (trMat Cv F' F p.1) hz hT I I'
  have hu := fun I => GlobalTheory.T.flag_cover_base_point_regular K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb (F.u q I) hz (hG.2.1 q I).1
  have hu' := fun I' => (hG'.2.1 r I').2
  have hterm : ∀ I I', RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) ∧
      valAt M'.x (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) zb =
        valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
    intro I I'
    obtain ⟨r1, -, v1, -⟩ := hst _ _ (hu I).1 (hmin I I').1
    obtain ⟨r2, -, v2, -⟩ := hst _ _ r1 (hu' I')
    refine ⟨r2, v2.trans ?_⟩
    rw [v1, (hu I).2, (hmin I I').2]
    rfl
  have hin := fun I => regAt_valAt_sum hz (Finset.univ.filter (IsStepRows N j p.2)) _
    fun I' _ => (hterm I I').1
  have hout := regAt_valAt_sum hz Finset.univ _ fun I _ => (hin I).1
  refine ⟨hout.1, ?_⟩
  refine hout.2.trans (Finset.sum_congr rfl fun I _ => ?_)
  rw [(hin I).2]
  exact Finset.sum_congr rfl fun I' _ => (hterm I I').2

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
