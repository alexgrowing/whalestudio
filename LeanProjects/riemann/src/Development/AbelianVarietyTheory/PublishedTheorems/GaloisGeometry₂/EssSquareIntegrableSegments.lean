import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.Published

def EssSquareIntegrableSegments : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL k), 1 ≤ δ.1 →
    ((∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) ↔ ∃ Δ : Segment k, IsLSeg Δ δ.rep)

namespace EssSquareIntegrableSegments

open MeasureTheory

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_adGL_one : Subsingleton (AdGL k 1) := by
  refine QuotientGroup.subsingleton_iff.2 (eq_top_iff.2 fun g _ => Subgroup.mem_center_iff.2 fun h => ?_)
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [Matrix.mul_apply, mul_comm]

theorem isSqIntCoeff_of_trivial {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 1) k) V}
    (h : ∀ g v, π g v = v) : IsSqIntCoeff π := by
  intro _ _ μ hμ v l _
  have := subsingleton_adGL_one (k := k)
  have : IsFiniteMeasure μ := ⟨(Set.toFinite _).isCompact.measure_lt_top⟩
  exact ⟨fun _ => ‖l v‖, fun g => by rw [h], memLp_const _⟩

theorem both_sides_ofChar (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    1 ≤ (IrrGL.ofChar χ hχ).1 ∧
      (∃ (ψ : kˣ →* ℂˣ) (hψ : IsSmoothChar ψ), IsSqIntCoeff ((IrrGL.ofChar χ hχ).tw ψ hψ).rep) ∧
        ∃ Δ : Segment k, IsLSeg Δ (IrrGL.ofChar χ hχ).rep := by
  have hi : IsSmoothChar χ⁻¹ := by
    have : χ⁻¹.ker = χ.ker := by ext; simp
    unfold IsSmoothChar; rw [this]; exact hχ
  refine ⟨le_rfl, ⟨χ⁻¹, hi, ?_⟩, _, (single_spec (IrrGL.isCusp_ofChar χ hχ)).2.1⟩
  have e : (IrrGL.ofChar χ hχ).tw χ⁻¹ hi = IrrGL.ofChar 1 isSmoothChar_one := by
    simp only [IrrGL.tw_ofChar, mul_inv_cancel]
  rw [e]
  refine @isSqIntCoeff_of_trivial k _ _ _ _ _ _ _ _ fun g v => ?_
  let φ := equivRep (IrrRep.det (k := k) (Fin 1) 1 isSmoothChar_one)
  obtain ⟨w, rfl⟩ := φ.toLinearEquiv.surjective v
  refine (φ.toIntertwiningMap.isIntertwining _ _ g w).symm.trans (congrArg φ ?_)
  show ((detChar (Fin 1) (1 : kˣ →* ℂˣ) g : ℂˣ) : ℂ) • w = w
  simp

end EssSquareIntegrableSegments

end GlobalTheory.Published
