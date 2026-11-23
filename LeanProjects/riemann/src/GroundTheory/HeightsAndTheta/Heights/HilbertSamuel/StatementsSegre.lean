import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} (F : Type) [Field F]

def segreMap : MRing (fun _ : Unit => ∀ k, ι k) F →ₐ[F] MRing ι F :=
  aeval fun v => ∏ k, X ⟨k, v.2 k⟩

def segrePrime (q : Ideal (MRing ι F)) : Ideal (MRing (fun _ : Unit => ∀ k, ι k) F) :=
  q.comap (segreMap F)

theorem segreMap_X (f : ∀ k, ι k) :
    segreMap F (X ⟨(), f⟩ : MRing (fun _ : Unit => ∀ k, ι k) F) = ∏ k, X ⟨k, f k⟩ :=
  aeval_X _ _

instance segrePrime.isPrime (q : Ideal (MRing ι F)) [q.IsPrime] : (segrePrime F q).IsPrime :=
  Ideal.comap_isPrime _ _

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
