import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeFrameBasis

open GlobalTheory.VolTransport

theorem eq_conj {A : Type} [CommRing A] {M : ℕ} {T T' x y : Matrix (Fin M) (Fin M) A}
    (h : T * T' = 1) (k : x * T' = T' * y) : y = T * x * T' := by
  rw [Matrix.mul_assoc, k, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem conj_rel {A : Type} [CommRing A] {M : ℕ} {T T' : Matrix (Fin M) (Fin M) A}
    (h : T' * T = 1) (x : Matrix (Fin M) (Fin M) A) : x * T' = T' * (T * x * T') := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem frame_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ M J J' P hJ
  have h0 : IsoPair (σ : E →+* E) J J' ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
      (P : Matrix (Fin M) (Fin M) E) := by
    refine ⟨Units.inv_mul P, Units.mul_inv P, ?_, hJ.symm⟩
    rw [hJ]
    calc _ = Formalism.UG.cT (σ : E →+* E) ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) * J *
          ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have h : IsoPair (sigR R σ) (JR R J) (JR R J')
      (((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R))
      ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)) :=
    h0.map (inclR (F := F) R) (fun _ => rfl)
  let e0 : HA R σ J ≃* HA R σ J' := conjE h
  have hm : ∀ g, ((HA.mat R σ J' (e0 g) : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) *
        ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
        (P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) := fun _ => rfl
  have hu : ∀ e : HA R σ J ≃* HA R σ J',
      (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → e = e0 := by
    intro e he
    ext g
    apply Subtype.ext
    apply Units.ext
    refine Eq.trans ?_ (hm g).symm
    exact eq_conj h.1 (he g)
  refine ⟨⟨e0, fun g => ?_, hu⟩, fun e he => ?_⟩
  · exact conj_rel h.2.1 _
  · rw [hu e he]
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    exact ⟨conjU_continuous h, conjU_continuous h.symm⟩

end GlobalTheory.GaugeFrameBasis
