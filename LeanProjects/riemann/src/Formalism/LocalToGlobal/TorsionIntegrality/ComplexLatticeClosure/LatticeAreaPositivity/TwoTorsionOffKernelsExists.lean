import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LatticeAreaPositivity.ThetaTranslationOperatorApply
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Th0TranslateProduct
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar

noncomputable section
open scoped ComplexConjugate

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem altE_twist (L : PeriodPair) (c x y : ℂ) (hc : c.re = 1 / 2) :
    F.altE L (c * x) y - F.altE L (c * y) x = F.altE L x y := by
  unfold F.altE F.herm
  simp only [Complex.div_ofReal_im, Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, hc]
  ring

theorem altE_half (L : PeriodPair) (c x y : ℂ) : F.altE L (c * x) y = 2 * F.altE L (c * (x / 2)) y := by
  unfold F.altE F.herm
  simp only [Complex.div_ofReal_im]
  have : c * x * conj y = 2 * (c * (x / 2) * conj y) := by ring
  rw [this]
  simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem not_all_killed (L : PeriodPair) (c : ℂ) (hc : c.re = 1 / 2) : ∃ x ∈ L.lattice, c * (x / 2) ∉ L.lattice := by
  by_contra h
  push_neg at h
  have h1 := h _ L.ω₁_mem_lattice
  have h2 := h _ L.ω₂_mem_lattice
  obtain ⟨k1, hk1⟩ := F.altEInt L _ _ h1 L.ω₂_mem_lattice
  obtain ⟨k2, hk2⟩ := F.altEInt L _ _ h2 L.ω₁_mem_lattice
  have h3 := altE_twist L c L.ω₁ L.ω₂ hc
  rw [altE_half L c L.ω₁, altE_half L c L.ω₂, hk1, hk2, F.altEBasis L] at h3
  split_ifs at h3
  · have : (2 * k1 - 2 * k2 : ℤ) = -1 := by exact_mod_cast h3
    omega
  · have : (2 * k1 - 2 * k2 : ℤ) = 1 := by exact_mod_cast h3
    omega

theorem two_torsion_off_kernels_exists : ExistsTwoTorsionOffKernels := by
  intro d L
  have hre : (F.cmTheta 1 d).re = 1 / 2 := by simp [F.cmTheta]
  have hre' : (1 - F.cmTheta 1 d).re = 1 / 2 := by rw [Complex.sub_re, hre]; norm_num
  obtain ⟨x, hx, hx1⟩ := not_all_killed L _ hre
  obtain ⟨y, hy, hy1⟩ := not_all_killed L _ hre'
  by_cases hx2 : (1 - F.cmTheta 1 d) * (x / 2) ∈ L.lattice
  · by_cases hy2 : F.cmTheta 1 d * (y / 2) ∈ L.lattice
    · refine ⟨x + y, add_mem hx hy, fun h => hx1 ?_, fun h => hy1 ?_⟩
      · have := sub_mem h hy2
        convert this using 1; ring
      · have := sub_mem h hx2
        convert this using 1; ring
    · exact ⟨y, hy, hy2, hy1⟩
  · exact ⟨x, hx, hx1, hx2⟩

theorem exp_pi_int (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem cm_sign_eq_period_sign (d : ℕ) (L : PeriodPair) (hst : HasCM d L.lattice.toAddSubgroup) (x : ℂ) (hx : x ∈ L.lattice) :
    al1 d L.lattice.toAddSubgroup x = SC.aa L d x := by
  obtain ⟨m, hm⟩ := (SC.semi (L := L) (d := d) hst).1 x hx
  unfold al1 SC.aa
  rw [koszul_homology_eq, hm, exp_pi_int]
  have : Real.sqrt d / 2 * (F.herm L x x).re = (m : ℝ) := hm
  rw [this, round_intCast]

theorem theta_zero_witness_holds : ThetaZeroWitness := by
  intro d L ω₀ hd hst h0 hθ hθ'
  have hhalf : ω₀ / 2 ∉ L.lattice := SC.half_notMem (L := L) (d := d) hst h0 hθ hθ'
  obtain ⟨hdiff, hone, -, -, hq⟩ := F.th0Basic L ω₀ h0 hhalf
  refine ⟨hdiff, fun x hx z => ?_, hone⟩
  have hx' : x ∈ L.lattice := hx
  have hchar := SC.char_eq (L := L) (d := d) hst h0 hθ hθ' hd x hx'
  have hpm := (SC.semi (L := L) (d := d) hst).2.1 x hx'
  rw [cm_sign_eq_period_sign d L hst x hx', thetaTranslationOperator_apply]
  unfold F.opU
  rw [hq x hx' z]
  have hc : F.semiChar L x * Complex.exp ((Real.pi : ℂ) * Complex.I * (F.altE L x ω₀ : ℂ)) = SC.aa L d x := hchar.symm
  rw [hc]
  have hsq : SC.aa L d x * SC.aa L d x = 1 := by
    rcases hpm with h | h <;> rw [h] <;> norm_num
  have hexp : Complex.exp ((Real.pi : ℂ) * F.herm L z x + (Real.pi : ℂ) * F.herm L x x / 2)
      * Complex.exp (-(Real.pi : ℂ) * F.herm L z x - (Real.pi : ℂ) * F.herm L x x / 2) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    ring
  calc _ = (SC.aa L d x * SC.aa L d x) * (Complex.exp ((Real.pi : ℂ) * F.herm L z x + (Real.pi : ℂ) * F.herm L x x / 2)
      * Complex.exp (-(Real.pi : ℂ) * F.herm L z x - (Real.pi : ℂ) * F.herm L x x / 2)) * F.th0 L (ω₀ / 2) z := by ring
    _ = _ := by rw [hsq, hexp]; ring

theorem theta_zero_exists_holds : ThetaZeroExistence := by
  rintro d Λ hd ⟨L, rfl⟩ hst
  obtain ⟨ω₀, h0, hθ, hθ'⟩ := two_torsion_off_kernels_exists d L
  exact ⟨_, theta_zero_witness_holds d L ω₀ hd hst h0 hθ hθ'⟩

end Formalism.L2.Th1.F2
