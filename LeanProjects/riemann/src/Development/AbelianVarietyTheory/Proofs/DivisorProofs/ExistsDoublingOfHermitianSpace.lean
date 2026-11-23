import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAdeleE
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)

noncomputable section

namespace GlobalTheory.HermDouble

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero, Complex.zero_re] at this
  exact lt_irrefl _ this

theorem isHermND_of_isHerm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : IsHermND σ X.J := by
  refine ⟨hX.herm, fun h0 => ?_⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  apply det_ne_zero_of_isCartan (hX.cartan w)
  have := RingHom.map_det ((B.emb w).1 : E →+* ℂ) X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem exists_isDbl : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n r s' : ℕ) (X : Spc F E n), X.IsHerm σ B r s' →
    ∃ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ := by
  intro _ F E _ _ _ _ _ σ B hB n r s' X hX
  let X₂ : Spc F E (n + n) :=
    { J := dblGram finSumFinEquiv X.J
      L := sumLat finSumFinEquiv X.L X.L
      θ := fun w => blkMat finSumFinEquiv (X.θ w) (-X.θ w)
      bas := fun v => blkGL finSumFinEquiv (X.bas v, X.bas v) }
  have hK := GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X₂
  refine ⟨X₂, GlobalTheory.DefDoubling.ioA σ X.J, GlobalTheory.StabHaar.stabK (σ := σ) B X₂, rfl, rfl, fun _ => rfl, fun _ _ => rfl, hK, ?_⟩
  exact (GlobalTheory.DblIwasawa.isCompact_and_iwasawaOf F E σ hB.cm hB.unram B n X (isHermND_of_isHerm hX) hX.lat hX.dual
    hX.cartan X₂ rfl rfl (fun _ => rfl) _ hK).2

end GlobalTheory.HermDouble

end
