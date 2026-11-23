import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.IwasawaCovolume
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBoundPower
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemV
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGen
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeVolRatio

noncomputable section

namespace Formalism.L2.S.S7.ZsCovR

open NumberField Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.IwasawaCovolume

theorem volgU_le (N : ℕ) : volgU N ≤ 7 ^ (N * N) := by
  unfold volgU
  calc ∏ i ∈ Finset.range N, (2 * Real.pi) ^ (i + 1) / ((i.factorial : ℕ) : ℝ)
      ≤ ∏ _i ∈ Finset.range N, (7 : ℝ) ^ N := by
        refine Finset.prod_le_prod (fun i _ => by positivity) fun i hi => ?_
        have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
        have hf : (1 : ℝ) ≤ ((i.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero i)
        have h2pi : 2 * Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
        calc (2 * Real.pi) ^ (i + 1) / ((i.factorial : ℕ) : ℝ) ≤ (2 * Real.pi) ^ (i + 1) :=
              div_le_self (by positivity) hf
          _ ≤ 7 ^ (i + 1) := pow_le_pow_left₀ (by positivity) h2pi _
          _ ≤ 7 ^ N := pow_le_pow_right₀ (by norm_num) hi'
    _ = (7 : ℝ) ^ (N * N) := by rw [Finset.prod_const, Finset.card_range, ← pow_mul]

theorem mass_chain (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd) (E : Type) [Field E] [NumberField E] [StarRing E]
    (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (n : ℕ) (hn : 2 ≤ n) :
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) =
      Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E 2) (Formalism.MainNotions.StandardLattice.stdLat E 2) *
        ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide E M := by
  induction n, hn using Nat.le_induction with
  | base => rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty, mul_one]
  | succ n hn ih =>
    have h3 : 3 ≤ n + 1 := by omega
    have hr := hMR E hE (n + 1) h3
    replace hr : Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E (n + 1)) (Formalism.MainNotions.StandardLattice.stdLat E (n + 1)) /
        Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) = Formalism.HermitianLatticesTheory.massRatioRightSide E (n + 1) := hr
    have hpos := Formalism.MainNotions.MassRatioBoundPower.massRatio_pos (K := E) h3
    have hne : Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) ≠ 0 := by
      intro h0; rw [h0, div_zero] at hr; exact hpos.ne' hr.symm
    rw [div_eq_iff hne] at hr
    rw [hr, ih, Finset.prod_Icc_succ_top (by omega)]
    ring

theorem mass_nonneg (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    0 ≤ Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) := by
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs
  · exact Finset.sum_nonneg fun _ _ => by positivity
  · exact le_rfl

theorem fDeg_E (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces I.E
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank I.E
  rw [IsTotallyComplex.nrRealPlaces_eq_zero] at h1 h2
  rw [Formalism.MainNotions.BridgeLevelGen.finrank_E] at h2
  unfold Formalism.HermitianLatticesTheory.fDeg
  omega

theorem card_F (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have : IsTotallyReal I.F := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero] at h2
  simpa [AutInst.f] using h2

theorem two_vInv_E (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_E]; ring

def CasimirBaseCount : ℕ := 27 + Formalism.MainNotions.MassRatioBoundPower.cZ

theorem covolR_nonneg (X : CData) : 0 ≤ covolR X :=
  mul_nonneg (pow_nonneg (volgU_pos _).le _) (mass_nonneg _ _)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem covolR_le (hMR : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.MassRatioStd) (X : CData) {n₀ : ℕ} {A : ℝ}
    (hX : X.HypB n₀ A) (hn2 : 2 ≤ X.I.n) :
    covolR X ≤ cn_Y X ^ ((CasimirBaseCount : ℝ) * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ)) := by
  unfold covolR
  rw [card_F]
  obtain ⟨hset, -, -⟩ := hX
  have hb : (2 : ℝ) ≤ X.b := hset.2.2.1
  have hg : 1 ≤ X.g := hset.2.2.2.2.2.2.2.1
  have hf1 : 1 ≤ X.I.f := Formalism.MainNotions.BridgeVolRatio.one_le_f X.I
  have hrd : 1 ≤ X.I.rd := Formalism.MainNotions.BridgeVolRatio.one_le_rd X.I
  have hE : Formalism.HermitianLatticesTheory.IsCMUnram X.I.E := X.I.cm.cmUnram
  have hd : Module.finrank ℚ X.I.E ≤ 2 * Formalism.HermitianLatticesTheory.fDeg X.I.E := by
    rw [Formalism.MainNotions.BridgeLevelGen.finrank_E, fDeg_E]
  have hchain := mass_chain hMR X.I.E hE X.I.n hn2
  have hvI := two_vInv_E X.I
  have hfD := fDeg_E X.I
  set n := X.I.n with hndef
  set f := X.I.f with hfdef
  set Y := cn_Y X with hY
  have hYdef : Y = (n : ℝ) * f * X.I.rd * (X.g : ℝ) * X.b := rfl
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hf1' : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  have hg1 : (1 : ℝ) ≤ X.g := by exact_mod_cast hg
  have hb1 : (1 : ℝ) ≤ X.b := by linarith
  have hnf : (1 : ℝ) ≤ (n : ℝ) * f := one_le_mul_of_one_le_of_one_le hn1 hf1'
  have hnfr : (1 : ℝ) ≤ (n : ℝ) * f * X.I.rd := one_le_mul_of_one_le_of_one_le hnf hrd
  have hnfrg : (1 : ℝ) ≤ (n : ℝ) * f * X.I.rd * X.g := one_le_mul_of_one_le_of_one_le hnfr hg1
  have hY1' : (n : ℝ) * f * X.I.rd * X.g ≤ Y := by
    rw [hYdef]; exact le_mul_of_one_le_right (by linarith) hb1
  have hY2 : 2 ≤ Y := by rw [hYdef]; nlinarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hrdY : X.I.rd ≤ Y := by
    calc X.I.rd ≤ (n : ℝ) * f * X.I.rd := le_mul_of_one_le_left (by linarith) hnf
      _ ≤ (n : ℝ) * f * X.I.rd * X.g := le_mul_of_one_le_right (by linarith) hg1
      _ ≤ Y := hY1'
  have hnY : (n : ℝ) ≤ Y := by
    calc (n : ℝ) ≤ (n : ℝ) * f := le_mul_of_one_le_right (by linarith) hf1'
      _ ≤ (n : ℝ) * f * X.I.rd := le_mul_of_one_le_right (by linarith) hrd
      _ ≤ (n : ℝ) * f * X.I.rd * X.g := le_mul_of_one_le_right (by linarith) hg1
      _ ≤ Y := hY1'
  have hfY : (f : ℝ) ≤ Y := by
    calc (f : ℝ) ≤ (n : ℝ) * f := le_mul_of_one_le_left (by linarith) hn1
      _ ≤ (n : ℝ) * f * X.I.rd := le_mul_of_one_le_right (by linarith) hrd
      _ ≤ (n : ℝ) * f * X.I.rd * X.g := le_mul_of_one_le_right (by linarith) hg1
      _ ≤ Y := hY1'

  have hv : 2 * Formalism.HermitianLatticesTheory.vInv X.I.E ≤ Y := by rw [hvI]; exact hrdY
  have hfDY : (Formalism.HermitianLatticesTheory.fDeg X.I.E : ℝ) ≤ Y := by rw [hfD]; exact hfY
  have hprod := Formalism.MainNotions.MassRatioBoundPower.prod_massRatio_le (K := X.I.E) hd n hY2 hnY hv
  rw [hfD] at hprod
  have hmass2 := Formalism.MainNotions.BridgeLemV.mass_two_le_pow hE hY2 hv hfDY
  rw [hfD] at hmass2
  have h8 : (8 : ℝ) ≤ Y ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hY2 3
    norm_num at this
    linarith
  have hvol : volgU n ^ f ≤ Y ^ (3 * (n * n) * f) := by
    calc volgU n ^ f ≤ ((7 : ℝ) ^ (n * n)) ^ f := pow_le_pow_left₀ (volgU_pos n).le (volgU_le n) f
      _ ≤ ((Y ^ 3) ^ (n * n)) ^ f := by
          gcongr
          linarith
      _ = Y ^ (3 * (n * n) * f) := by rw [← pow_mul, ← pow_mul]; ring_nf

  have hpn : 0 ≤ ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide X.I.E M :=
    Finset.prod_nonneg fun M hM => Formalism.MainNotions.MassRatioBoundPower.mass_ratio_rhs_nonneg (Finset.mem_Icc.1 hM).1
  have hmn : Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm X.I.E n) (Formalism.MainNotions.StandardLattice.stdLat X.I.E n) ≤
      Y ^ (22 * f) * Y ^ ((2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f) := by
    rw [hchain]
    exact mul_le_mul hmass2 hprod hpn (by positivity)
  have hexp : 3 * (n * n) * f + (22 * f + (2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f) ≤ CasimirBaseCount * n ^ 2 * f := by
    have e1 : 3 * (n * n) * f + (22 * f + (2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f) =
        5 * (n * n * f) + 22 * f + Formalism.MainNotions.MassRatioBoundPower.cZ * (n * f) := by ring
    have e2 : CasimirBaseCount * n ^ 2 * f = 27 * (n * n * f) + Formalism.MainNotions.MassRatioBoundPower.cZ * (n * n * f) := by
      unfold CasimirBaseCount; ring
    have h1 : f ≤ n * n * f := Nat.le_mul_of_pos_left f (Nat.mul_pos (by omega) (by omega))
    have h2 : n * f ≤ n * n * f := Nat.mul_le_mul_right f (Nat.le_mul_of_pos_left n (by omega))
    have h3 := Nat.mul_le_mul_left Formalism.MainNotions.MassRatioBoundPower.cZ h2
    rw [e1, e2]
    linarith
  calc volgU n ^ f * Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm X.I.E n) (Formalism.MainNotions.StandardLattice.stdLat X.I.E n)
      ≤ Y ^ (3 * (n * n) * f) * (Y ^ (22 * f) * Y ^ ((2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f)) :=
        mul_le_mul hvol hmn (mass_nonneg _ _) (by positivity)
    _ = Y ^ (3 * (n * n) * f + (22 * f + (2 * n + Formalism.MainNotions.MassRatioBoundPower.cZ) * n * f)) := by
        rw [← pow_add, ← pow_add]
    _ ≤ Y ^ (CasimirBaseCount * n ^ 2 * f) := pow_le_pow_right₀ hY1 hexp
    _ = Y ^ ((CasimirBaseCount : ℝ) * (n : ℝ) ^ 2 * (f : ℝ)) := by
        rw [← Real.rpow_natCast]
        congr 1
        push_cast
        ring

end Formalism.L2.S.S7.ZsCovR

end
