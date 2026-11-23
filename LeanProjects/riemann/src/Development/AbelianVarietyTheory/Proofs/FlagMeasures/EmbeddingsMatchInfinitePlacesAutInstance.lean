import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.Place

theorem comap_mk_phi (I : AutInst) (v : InfinitePlace I.F) :
    (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E) = v := by
  have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem placeMatch : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  intro I xf
  have hb := GlobalTheory.Count.FrameMajorant.comap_bijective I
  refine ⟨⟨fun v v' h => ?_, fun w => ⟨w.comap (algebraMap I.F I.E), hb.1 (comap_mk_phi I _)⟩⟩, fun v => ?_⟩
  · have h' : InfinitePlace.mk (I.φ v) = InfinitePlace.mk (I.φ v') := h
    rw [← comap_mk_phi I v, h', comap_mk_phi]
  · have he := GlobalTheory.PointEquivariance.embedding_eq I (InfinitePlace.mk (I.φ v))
    have hu : ∀ u, uMat ((((1, xf) : I.GA)).1 u) = 1 := fun u => rfl
    rw [comap_mk_phi] at he
    unfold frm
    rw [comap_mk_phi, hu, Matrix.mul_one]
    by_cases h : (InfinitePlace.mk (I.φ v)).embedding = I.φ v
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨he.resolve_left h, if_neg h⟩

end GlobalTheory.RadCov.Place
