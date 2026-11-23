import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SinvOfSwt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddWeightCycles.WOneOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStarOdd

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockEvaluationBounds

open BlockInvariants

variable {L : Type} [Field L] [NumberField L]

def Aev (m : ℕ) {q : ℕ} (x : Pat L q) : Chn (Gm L m) q →ₗ[ℝ] ℝ :=
  evL (emb L m) (intP (ext (AT (N := m) x))) (one L m)

theorem Aev_apply (m : ℕ) {q : ℕ} (x : Pat L q) (z : Chn (Gm L m) q) :
    Aev m x z = ev (emb L m) (intP (ext (AT (N := m) x))) (one L m) z := evL_apply _ _ _ _

theorem Aev_bd (hE : SEv) (hS : SStokes) (hG : AGood) (hWI : WInv) {m k : ℕ} (x : Pat L (k + 1))
    (z : Chn (Gm L m) (k + 1)) (hz : IsBd z) : Aev m x z = 0 := by
  have hI : ∀ g, FInv (ext (AT (N := m) x)) g := fInv_ext (hWI L m _ x)
  rw [Aev_apply]
  exact (hE (Gm L m) (Gp L m) (Pos L m) (emb L m) k _ (fun g y => intP_inv hI (emb L m g) y)
    (hG hS L m _ _ hI).2).1 _ z hz

theorem Aev_stab (hWP : WPad) (hWI : WInv) (hTS : TStab) (hPS : PStab) {n n' q : ℕ} (h : n ≤ n') (x : Pat L q)
    (z : Chn (Gm L n) q) : Aev n' x (cmap (stab (𝓞 L) n n' h) q z) = Aev n x z := by
  rw [Aev_apply, Aev_apply, ev_stab hTS]
  congr 1
  refine intP_congr fun p hp => ?_
  rw [ext_uniq (hPS L n n' _ h _ (fInv_ext (hWI L n' _ x))) hp]
  congr 1
  simp only [pullF]
  rw [padL_one, ext_one (hWI L n' _ x), hWP L n n' _ h x]

theorem Aev_blk (hWB : WBlk) (hWI : WInv) (hTB : TBlk) (hPB : PBlk) (d n : ℕ) {q : ℕ} (x : Pat L q)
    (z : Chn (Gm L n) q) : Aev (d * n) x (cmap (psi (𝓞 L) d n) q z) = (d : ℝ) ^ ncyc x.1 * Aev n x z := by
  rw [Aev_apply, Aev_apply, ev_blk hTB, ← ev_mul]
  congr 1
  rw [← intP_smul]
  refine intP_congr fun p hp => ?_
  rw [ext_uniq (hPB L d n _ _ (fInv_ext (hWI L (d * n) _ x))) hp]
  simp only [pullF, add_zero]
  rw [blkL_one, ext_one (hWI L (d * n) _ x), hWB L d n _ x, ext_smul]

theorem Aev_comb (hS : SStokes) (hG : AGood) (hWI : WInv) {m q : ℕ} (x y y' : Pat L q) (r : ℝ)
    (he : AT (N := m) x = r • (AT (N := m) y + AT (N := m) y')) (z : Chn (Gm L m) q) :
    Aev m x z = r * (Aev m y z + Aev m y' z) := by
  have hc : ∀ i : Fin 2, ContinuousOn (ext (![AT (N := m) y, AT (N := m) y'] i)) (Pos L m) := by
    intro i
    fin_cases i
    · exact (hG hS L m q _ (fInv_ext (hWI L m q y))).1
    · exact (hG hS L m q _ (fInv_ext (hWI L m q y'))).1
  have hsum : r • (AT (N := m) y + AT (N := m) y') =
      ∑ i : Fin 2, (fun _ => r) i • ![AT (N := m) y, AT (N := m) y'] i := by
    simp [Fin.sum_univ_two]
  have h1 : ext (AT (N := m) x) =
      fun h => ∑ i : Fin 2, (fun _ => r) i • ext (![AT (N := m) y, AT (N := m) y'] i) h := by
    funext h
    rw [he, hsum, ext_sum]
  have h2 := intP_sum (fun _ : Fin 2 => r) _ hc
  rw [Aev_apply, Aev_apply, Aev_apply, h1, h2, ev_sum]
  simp [Fin.sum_univ_two, mul_add]

theorem swtOdd (hE : SEv) (hS : SStokes) (hF : FFT) (hG : AGood) (hWP : WPad) (hWB : WBlk) (hWI : WInv)
    (hWC : WCyc) (hTS : TStab) (hTB : TBlk) (hPS : PStab) (hPB : PBlk) (hWO : WOneOdd) (hR : WRot) :
    SWtOdd := by
  intro L _ _ k hk
  classical
  have hodd : Odd (k + 1) := hk.add_one
  have hpos : 0 < k + 1 := Nat.succ_pos k
  have hrot : ncyc (finRotate (k + 1)) = 1 := hR (k + 1) hpos
  refine ⟨fun w n => Aev n ((finRotate (k + 1), fun _ => w, false) : Pat L (k + 1)) +
    Aev n ((finRotate (k + 1), fun _ => w, true) : Pat L (k + 1)), ?_, ?_⟩
  · intro w
    refine ⟨?_, ?_, ?_⟩
    · intro n z hz
      simp only [LinearMap.add_apply]
      rw [Aev_bd hE hS hG hWI _ z hz, Aev_bd hE hS hG hWI _ z hz, add_zero]
    · intro n n' h z _
      simp only [LinearMap.add_apply]
      rw [Aev_stab hWP hWI hTS hPS h, Aev_stab hWP hWI hTS hPS h]
    · intro d n z _ _
      simp only [LinearMap.add_apply]
      rw [Aev_blk hWB hWI hTB hPB, Aev_blk hWB hWI hTB hPB]
      simp only [hrot, pow_one]
      ring
  · intro N ω hω
    obtain ⟨c, hc⟩ := hF L N (k + 1) _ (uInv_of hω)
    have hone : ∀ x : Pat L (k + 1), ncyc x.1 = 1 → ∃ (r : ℝ) (w : InfinitePlace L),
        AT (N := N) x = r • (AT (N := N) ((finRotate (k + 1), fun _ => w, false) : Pat L (k + 1)) +
          AT (N := N) ((finRotate (k + 1), fun _ => w, true) : Pat L (k + 1))) :=
      fun x hx => hWO L N (k + 1) x hodd hx
    choose! rx wx hrw using hone
    refine ⟨fun w => ∑ x, if ncyc x.1 = 1 ∧ wx x = w then c x * rx x else 0,
      fun j n => ∑ x, (if ncyc x.1 = j then c x else 0) • Aev n x, ?_, ?_⟩
    · intro j _
      refine ⟨?_, ?_, ?_⟩
      · intro n z hz
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        exact Finset.sum_eq_zero fun x _ => by rw [Aev_bd hE hS hG hWI x z hz, mul_zero]
      · intro n n' h z _
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [Aev_stab hWP hWI hTS hPS h]
      · intro d n z _ _
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Aev_blk hWB hWI hTB hPB]
        split_ifs with hj
        · rw [hj]
          ring
        · simp
    · intro z _
      have hcont : ∀ x : Pat L (k + 1), ContinuousOn (ext (AT (N := N) x)) (Pos L N) :=
        fun x => (hG hS L N (k + 1) _ (fInv_ext (hWI L N (k + 1) x))).1
      have h1 : intP ω = fun p => ∑ x, c x * intP (ext (AT (N := N) x)) p := by
        rw [← intP_sum c _ hcont]
        apply intP_congr
        intro p hp
        rw [ext_uniq hω hp, hc, ext_sum]
      have e1 : ∀ x : Pat L (k + 1), (∑ w, (if ncyc x.1 = 1 ∧ wx x = w then c x * rx x else 0) *
          (Aev N ((finRotate (k + 1), fun _ => w, false) : Pat L (k + 1)) z +
            Aev N ((finRotate (k + 1), fun _ => w, true) : Pat L (k + 1)) z)) =
          if ncyc x.1 = 1 then c x * Aev N x z else 0 := by
        intro x
        by_cases h : ncyc x.1 = 1
        · simp only [h, true_and, if_true, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
          rw [Aev_comb hS hG hWI _ _ _ _ (hrw x h) z]
          ring
        · simp [h]
      have e2 : ∀ x : Pat L (k + 1), (∑ j ∈ Finset.Icc 2 (k + 1),
          (if ncyc x.1 = j then c x else 0) * Aev N x z) =
          if ncyc x.1 = 1 then 0 else c x * Aev N x z := by
        intro x
        have hb := hWC (k + 1) x.1 hpos
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_Icc]
        split_ifs with h1 h2 h2
        · omega
        · rfl
        · rfl
        · omega
      rw [h1, ev_sum]
      simp only [← Aev_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (InfinitePlace L))),
        Finset.sum_comm (s := Finset.Icc 2 (k + 1)), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [e1 x, e2 x]
      split_ifs <;> ring

end PositivityTheory.KB.BlockEvaluationBounds

end
