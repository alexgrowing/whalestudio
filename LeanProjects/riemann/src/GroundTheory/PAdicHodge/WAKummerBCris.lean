import Mathlib
import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

set_option maxHeartbeats 1600000 in

theorem algebraMap_padicInt_bCris {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (a : ℤ_[p]) :
    algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)
      (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (IsPerfectoidField.padicIntToWitt p a))) =
      algebraMap ℚ_[p] (BCris hε) (a : ℚ_[p]) :=
  iotaB_injective hε hζ (((iotaB_algebraMap hε hζ _).trans (congrArg (algebraMap 𝔹 𝔹dR)
    ((iotaPlus_algebraMap _).trans (iota_padicInt a)))).trans
    ((iotaB_algebraMap_padic hε hζ _).trans (IsScalarTower.algebraMap_apply ℚ_[p] 𝔹 𝔹dR _)).symm)

set_option maxHeartbeats 1600000 in

theorem galB_periodTCris {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (σ : Gal(PadicAlgCl p/K)) :
    galB hε σ (periodTCris hε) =
      algebraMap ℚ_[p] (BCris hε) ((cycloChar K σ : ℤ_[p]) : ℚ_[p]) * periodTCris hε :=
  (galB_algebraMap hε σ _).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    ((gal_smul_algebraMap_plus σ _).trans (congrArg (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p))
      (gal_smul_periodT σ hε)))).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
      (map_mul _ _ _)).trans ((map_mul _ _ _).trans
        (congrArg (· * periodTCris hε) (algebraMap_padicInt_bCris hε hζ _)))))

abbrev logTeichB {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) {x : 𝒪♭}
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) : BCris hε :=
  algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (logTeich hx))

set_option maxHeartbeats 1600000 in

theorem phiB_logTeichB {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) {x : 𝒪♭}
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    phiB hε (logTeichB hε hx) = (p : BCris hε) * logTeichB hε hx :=
  (phiB_algebraMap hε _).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    ((phiPlus_algebraMap _).trans (congrArg (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p))
      (phi_logTeich hx)))).trans (by simp only [map_mul, map_natCast]))

set_option maxHeartbeats 1600000 in

theorem galB_logTeichB {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {x : 𝒪♭} (hx0 : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]))
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) (σ : Gal(PadicAlgCl p/K)) :
    galB hε σ (logTeichB hε hx) = logTeichB hε hx +
      algebraMap ℚ_[p] (BCris hε) (kummerCocycle hε hζ hx0 hfix σ : ℚ_[p]) * periodTCris hε :=
  (galB_algebraMap hε σ _).trans ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    ((gal_smul_algebraMap_plus σ _).trans (congrArg (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p))
      (gal_smul_logTeich_eq hε hζ hx0 hfix hx σ)))).trans
    ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (map_add _ _ _)).trans
      ((map_add _ _ _).trans (congrArg (logTeichB hε hx + ·)
        ((congrArg (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (map_mul _ _ _)).trans
          ((map_mul _ _ _).trans
            (congrArg (· * periodTCris hε) (algebraMap_padicInt_bCris hε hζ _))))))))

end ACris

end GroundTheory.PAdicHodge
