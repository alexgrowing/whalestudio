import Mathlib
import GroundTheory.PAdicHodge.BCrisEigenFixed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

include hζ in
set_option maxHeartbeats 1600000 in
theorem iotaB_algebraMap_padic_bdRPlus (q : ℚ_[p]) :
    iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) q) = algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ (iotaPlus_algebraMap_padic q))

def aInfToBCris : AInf ℂ_[p] p →+* BCris hε :=
  (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)).comp
    ((algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)))

include hζ in
set_option maxHeartbeats 1600000 in
theorem iotaB_aInfToBCris (w : AInf ℂ_[p] p) :
    iotaB hε hζ (aInfToBCris hε w) =
      algebraMap 𝔹 𝔹dR (wittToBDeRhamPlus (normInteger ℂ_[p]) p w) :=
  (iotaB_algebraMap hε hζ _).trans (congrArg _ ((iotaPlus_algebraMap _).trans (iota_algebraMap w)))

include hζ in
set_option maxHeartbeats 1600000 in
theorem iotaB_periodTCris_eq :
    iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (fontaineT ε hε) :=
  (iotaB_periodTCris hε hζ).trans (congrArg _ (iota_periodT hε))

variable {L : IntermediateField ℚ_[p] (PadicAlgCl p)}

include hζ in
set_option maxHeartbeats 1600000 in
theorem galB_eq_of_smul_iotaB (σ : Gal(PadicAlgCl p/L)) {B : BCris hε}
    (h : σ • iotaB hε hζ B = iotaB hε hζ B) : galB hε σ B = B :=
  iotaB_injective hε hζ ((iotaB_galB (K := L) hε hζ σ B).trans h)

include hζ in
set_option maxHeartbeats 3200000 in

theorem isUnit_of_galB_fixed [FiniteDimensional ℚ_[p] L] {B : BCris hε} (hB0 : B ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/L), galB hε σ B = B) : IsUnit B := by
  obtain ⟨k, hk, hBk⟩ := bCris_fixed_mem_maxUnramified hε hζ (K := L) B h
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hB0
    apply iotaB_injective hε hζ
    rw [hBk, map_zero, map_zero, map_zero]
  obtain ⟨B', -, hB'⟩ := exists_bCris_fixed (K := L) hε hζ (inv_mem hk)
  have e : algebraMap 𝔹 𝔹dR (algClToBdR p k) * algebraMap 𝔹 𝔹dR (algClToBdR p k⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hk0, map_one, map_one]
  have h1 : B * B' = 1 := iotaB_injective hε hζ ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) hBk hB').trans (e.trans (map_one _).symm)))
  exact isUnit_iff_exists_inv.2 ⟨B', h1⟩

end ACris

end GroundTheory.PAdicHodge
