import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SimplexCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar

noncomputable section

open NumberField Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.BlockInvariants

variable {L : Type} [Field L] [NumberField L]

theorem ev_stab (hT : TStab) {n N q : ℕ} (h : n ≤ N) (ω : Form (HS L N) q) (z : Chn (Gm L n) q) :
    ev (emb L N) (intP ω) (one L N) (cmap (stab (𝓞 L) n N h) q z) =
      ev (emb L n) (intP (pullF ω (padL n N) (eL n N))) (one L n) z := by
  rw [ev_cmap]
  simp only [ev]
  apply Finsupp.sum_congr
  intro g _
  congr 1
  unfold intP
  rw [← intS_pull]
  congr 1
  funext j
  simp only [MonoidHom.comp_apply]
  exact hT L n N h _

theorem ev_blk (hT : TBlk) {d n q : ℕ} (ω : Form (HS L (d * n)) q) (z : Chn (Gm L n) q) :
    ev (emb L (d * n)) (intP ω) (one L (d * n)) (cmap (psi (𝓞 L) d n) q z) =
      ev (emb L n) (intP (pullF ω (blkL d n) 0)) (one L n) z := by
  rw [ev_cmap]
  simp only [ev]
  apply Finsupp.sum_congr
  intro g _
  congr 1
  unfold intP
  rw [← intS_pull]
  congr 1
  funext j
  simp only [MonoidHom.comp_apply, add_zero]
  exact hT L d n _

theorem padL_one (n N : ℕ) : padL n N (one L n).1 + eL n N = (one L N).1 := by
  unfold padL eL one
  simp
  apply HS_ext
  intro w
  simp only [mat_add, mat_mkHS]
  ext i j
  unfold padM padMat
  by_cases h : (i : ℕ) < n ∧ (j : ℕ) < n
  · simp [h, Matrix.one_apply, Fin.ext_iff]
  · simp [h, Matrix.one_apply]

theorem blkL_one (d n : ℕ) : blkL d n (one L n).1 = (one L (d * n)).1 := by
  unfold blkL one
  simp

private theorem uInv_sum_smul_AT_of_wInv (hWI : WInv) {m q : ℕ} (c : Pat L q → ℝ) : UInv (∑ x, c x • (AT (N := m) x)) := by
  intro u hu
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := congrArg (fun f => f v) (hWI L m q x u hu)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at this
  rw [this]

private theorem sum_smul_AT_comp_eq_of_intertwine {n m q : ℕ} (c : Pat L q → ℝ) (P : HS L n →L[ℝ] HS L m) (a : Pat L q → ℝ)
    (hP : ∀ x, (AT (N := m) x).compContinuousLinearMap P = a x • AT x) :
    (∑ x, c x • (AT (N := m) x)).compContinuousLinearMap P = ∑ x, (c x * a x) • AT (N := n) x := by
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have := congrArg (fun f => f v) (hP x)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, ContinuousAlternatingMap.smul_apply] at this
  rw [this, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_assoc]

private theorem fInv_ext_of_uInv {N q : ℕ} (β : HS L N [⋀^Fin q]→L[ℝ] ℝ) (hβ : UInv β) (g : Gp L N) : FInv (ext β) g := by
  intro h hh
  unfold ext
  have h1 : actL (sec h)⁻¹ (one L N : HS L N) = h := by
    rw [← actL_sec hh, ← actL_mul, inv_mul_cancel, actL_one]
  have hu : actL (sec (actL g h) * g * (sec h)⁻¹) (one L N : HS L N) = (one L N : HS L N) := by
    rw [actL_mul, h1, actL_mul, actL_sec (actL_pos g hh)]
  conv_rhs => rw [← hβ _ hu]
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  congr 1
  funext i
  rw [← actL_mul, ← actL_mul, inv_mul_cancel_right]

private theorem apply_eq_ext_apply_one_of_fInv_of_mem_Pos {N q : ℕ} (ω : Form (HS L N) q) (hω : ∀ g : Gp L N, FInv ω g) (h : HS L N)
    (hh : h ∈ Pos L N) : ω h = ext (ω (one L N)) h := by
  have := hω (sec h) h hh
  rw [actL_sec hh] at this
  unfold ext
  exact this.symm

private theorem uInv_apply_one_of_fInv {N q : ℕ} (ω : Form (HS L N) q) (hω : ∀ g : Gp L N, FInv ω g) : UInv (ω (one L N)) := by
  intro u hu
  have := hω u _ (one L N).2
  rw [hu] at this
  exact this

theorem swt (hE : SEv) (hS : SStokes) (hF : FFT) (hG : AGood) (hWP : WPad) (hWB : WBlk) (hWI : WInv)
    (hWO : WOne) (hWC : WCyc) (hTS : TStab) (hTB : TBlk) (hPS : PStab) (hPB : PBlk) : SWt := by
  intro L' _ _ N k hk ω hω
  obtain ⟨c, hc⟩ := hF L' N (k + 1) (ω (one L' N)) (uInv_apply_one_of_fInv ω hω)
  set cj : ℕ → Pat L' (k + 1) → ℝ := fun j x => if ncyc x.1 = j then c x else 0 with hcj
  have hU : ∀ j m, UInv (∑ x, cj j x • (AT (N := m) x)) := fun j m => uInv_sum_smul_AT_of_wInv hWI (cj j)
  have hFI : ∀ j m (g : Gp L' m), FInv (ext (∑ x, cj j x • (AT (N := m) x))) g :=
    fun j m g => fInv_ext_of_uInv _ (hU j m) g
  have hGd : ∀ j m, Good (ext (∑ x, cj j x • (AT (N := m) x))) := fun j m => hG hS L' m (k + 1) _ (hFI j m)
  refine ⟨fun j m => evL (emb L' m) (intP (ext (∑ x, cj j x • (AT (N := m) x)))) (one L' m), ?_, ?_⟩
  · intro j _
    refine ⟨?_, ?_, ?_⟩
    · intro m z hz
      rw [evL_apply]
      exact (hE _ _ _ (emb L' m) k _ (fun g y => intP_inv (hFI j m) (emb L' m g) y) (hGd j m).2).1 _ z hz
    · intro n n' h z _
      rw [evL_apply, evL_apply, ev_stab hTS h]
      congr 1
      apply intP_congr
      intro p hp
      rw [apply_eq_ext_apply_one_of_fInv_of_mem_Pos _ (hPS L' n n' (k + 1) h _ (hFI j n')) p hp]
      congr 1
      unfold pullF
      rw [padL_one, ext_one (hU j n'),
        sum_smul_AT_comp_eq_of_intertwine (cj j) (padL n n') (fun _ => 1) (fun x => by rw [hWP L' n n' (k + 1) h x, one_smul])]
      simp only [mul_one]
    · intro d n z _ _
      rw [evL_apply, evL_apply, ev_blk hTB]
      rw [intP_congr (ω' := fun p => ((d : ℝ) ^ j) • ext (∑ x, cj j x • (AT (N := n) x)) p)]
      · rw [intP_smul]
        simp only [ev, Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro g _
        ring
      · intro p hp
        rw [apply_eq_ext_apply_one_of_fInv_of_mem_Pos _ (hPB L' d n (k + 1) _ (hFI j (d * n))) p hp, ← ext_smul]
        congr 1
        unfold pullF
        rw [blkL_one, add_zero, ext_one (hU j (d * n)),
          sum_smul_AT_comp_eq_of_intertwine (cj j) (blkL d n) (fun x => (d : ℝ) ^ ncyc x.1) (fun x => hWB L' d n (k + 1) x),
          Finset.smul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [smul_smul]
        congr 1
        simp only [hcj]
        split_ifs with hx
        · rw [hx, mul_comm]
        · simp
  · intro z hz
    have hsum : ∀ p ∈ Pos L' N, ω p =
        ∑ j : ↥(Finset.Icc 2 (k + 1)), (1 : ℝ) • ext (∑ x, cj j x • (AT (N := N) x)) p := by
      intro p hp
      rw [apply_eq_ext_apply_one_of_fInv_of_mem_Pos ω hω p hp, hc, ext_sum]
      simp only [ext_sum, one_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [← Finset.sum_smul, Finset.sum_coe_sort (Finset.Icc 2 (k + 1)) (fun j => cj j x)]
      simp only [hcj, Finset.sum_ite_eq]
      split_ifs with hm
      · rfl
      · have h1 := hWC (k + 1) x.1 (by omega)
        have h2 : ncyc x.1 = 1 := by
          simp only [Finset.mem_Icc] at hm
          omega
        rw [hWO L' N (k + 1) x hk.add_one h2, ext_zero, smul_zero, zero_smul]
    rw [intP_congr hsum, intP_sum (ι := ↥(Finset.Icc 2 (k + 1))) (fun _ => 1)
      (fun j => ext (∑ x, cj j x • (AT (N := N) x))) (fun j => (hGd j N).1), ev_sum]
    simp only [one_mul, evL_apply]
    exact Finset.sum_coe_sort (Finset.Icc 2 (k + 1))
      (fun j => ev (emb L' N) (intP (ext (∑ x, cj j x • (AT (N := N) x)))) (one L' N) z)

theorem sinv_of_swt (hC : SChain) (hP : SPsi) (hS : SStokes) (hG : AGood) (hW : SWt) : SInv := by
  intro L' _ _ N k ω hω
  refine ⟨hG hS L' N (k + 1) ω hω, ?_⟩
  intro hk n h z hz hpz
  obtain ⟨a, ha, hev⟩ := hW L' N k hk ω hω
  have hcz : IsCyc (cmap (stab (𝓞 L') n N h) (k + 1) z) := by
    unfold IsCyc at hz ⊢
    rw [hC.2.1, hz, map_zero]
  rw [hev _ hcz]
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨hb, hst, hps⟩ := ha j hj
  rw [hst n N h z hz]
  have e1 := hb _ _ (hP (𝓞 L') 1 n k (by omega) z hz hpz)
  rw [map_sub, map_smul, hps (1 + 1) n z (by norm_num) hz, hst n _ _ z hz, smul_eq_mul] at e1
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  have h4 : (4 : ℝ) ≤ 2 ^ j := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj2
  push_cast at e1
  have hx : ((2 : ℝ) ^ j - 2) * a j n z = 0 := by
    norm_num at e1
    linarith
  exact (mul_eq_zero.mp hx).resolve_left (by linarith)

end PositivityTheory.KB.BlockInvariants

end
