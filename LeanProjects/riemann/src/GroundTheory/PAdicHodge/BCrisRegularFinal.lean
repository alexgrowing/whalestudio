import Mathlib
import GroundTheory.PAdicHodge.BCrisRegularSenTate
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Module

variable {p : ℕ} [hp : Fact p.Prime]

namespace ACris

local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in

theorem isUnit_of_galB_eigen {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
    {b : BCris hε} (hb0 : b ≠ 0)
    (hb : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], galB hε σ b = algebraMap ℚ_[p] (BCris hε) q * b) :
    IsUnit b :=
  isUnit_of_forall_galB_eq_mul hε hζ senTateCharacters hb0 hb

include hζ in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bCris_isRegular {K : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K] :
    letI := isDomain_bCris hε hζ
    letI := galBAction (K := K) hε
    haveI := smulCommClass_galBAction (K := K) hε
    IsRegular Gal(PadicAlgCl p/K) ℚ_[p] (BCris hε) :=
  isRegular_bCris hε hζ senTateCharacters

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/K) V)

def IsCrystalline : Prop :=
  letI := galBAction (K := K) hε
  haveI := smulCommClass_galBAction (K := K) hε
  IsAdmissible (BCris hε) ρ

end ACris

end GroundTheory.PAdicHodge
