import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def CoreLF : Prop :=
  ∀ (k p m n : ℕ) (e : p + m = n), 1 ≤ p → ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k m Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p m Bj.z) = B0.z → D.castV e (liftVec k p m Bj.z') = B0.z' →
    (∀ y : B.Mat k m, Bj.π' y = B0.π' (D.castM e (ιLev k p m y))) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p m e) →
    Bj.μN = D.muN k m → B0.μN = D.muN k n →
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k n),
      (∀ x, sx x ∈ Sset k n B0.z) ∧
      ∀ g ∈ JF.Om k m Bj.z Bj.z', ∀ H : B.Mat k n → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g)))) μ ∧
        B.JF Bj (U.PhiFun (s := 0) k m σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
            (fun a => a.elim0)) g =
          ∫ x, ℓ x (PBG.Kr B0 H (sx x * D.castM e (U.mMap k p m (U.hMat σ d) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
