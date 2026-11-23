import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdelicHermitianHyperbolicEAnisotropicEqZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SkewHermitianApproximation

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

theorem mf_gA {D : D7} (X : HidaSetting D) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) 1 Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : Mf X (gA X le_rfl hY hYs).2 = cay (2 * D.R.rS + 2) (Y.map (ic X)) := by
  have hf : X.B.I.fmat (gA X le_rfl hY hYs).2 = (gE X Y).map (ic X) := rfl
  have h1 : (Bm' X).map (ic X) * (Bm X).map (ic X) = 1 := by
    rw [← Matrix.map_mul, Bm'_mul_Bm, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Mf Bf Bf'
  rw [hf, gE, Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [← Matrix.mul_assoc]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem nDense_of (h1 : NfPat) (h2 : NfOfPat) (h3 : CayInvR) (h4 : SkewApprox) (h5 : CayCont)
    (h6 : KgOfClose) : Formalism.L2.SG.Pf.SlabCoverPf.NDense := by
  intro D X u n hn U hU hnU
  obtain ⟨Z, hZ, hZs, hZc⟩ := h3 D X n (h1 D X u n hn)
  have hO : IsOpen {k : X.B.I.Gf | n * k ∈ U} := hU.preimage (continuous_mul_left n)
  have hN : {k : X.B.I.Gf | n * k ∈ U} ∈ nhds (1 : X.B.I.Gf) := hO.mem_nhds (by simpa using hnU)
  obtain ⟨g, hg, hgU⟩ := X.B.I.topf_basis _ hN
  obtain ⟨c, hc, hcK⟩ := h6 D X n g hg
  obtain ⟨c', hc', hcc⟩ := h5 D X Z c hc
  obtain ⟨Y, hY, hYs, hYc⟩ := h4 D X Z hZ hZs c' hc'
  refine ⟨gA X le_rfl hY hYs, (Formalism.MainNotions.LeviCoordinates.rr_mem_GF _ _).2 (gA_GF X le_rfl hY hYs),
    gA_ninf X u le_rfl hY hYs, ?_, ?_⟩
  · apply h2 D X u
    rw [mf_gA]
    exact cay_sub_one _ (inPat_map (ic X) hY)
  · have hK : n⁻¹ * (gA X le_rfl hY hYs).2 ∈ X.B.I.Kg g := hcK _ (by rw [mf_gA, ← hZc]; exact hcc _ hYc)
    have := hgU hK
    simpa using this

theorem nDense_of_two (h4 : SkewApprox) (h6 : KgOfClose) : Formalism.L2.SG.Pf.SlabCoverPf.NDense :=
  nDense_of pattern_of_nilradical nilradical_of_pattern cayley_inverse_right h4 cayley_continuous h6

theorem nilradical_strong_approximation : Formalism.L2.SG.Pf.SlabCoverPf.NDense :=
  nDense_of_two skew_hermitian_approximation level_of_close_element

end Formalism.L2.SG.Pf.SlabNDensePf
