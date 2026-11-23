import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IteratedHeckeBounds.LemLz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStar

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.JoinReconstruction

open PositivityTheory.KB

theorem lem_form (hHt : SHt) (hPU : SPU) (hWhit : SWhit) (hCen : SCen) (L : Type) [Field L] [NumberField L]
    (hC : IsTotallyComplex L) (k a N : ℕ) (h1N : 1 ≤ N) (hPUa : Nonempty (PU L N fun x => ht x ^ a))
    (c : (Fin (k + 2) → Gm L N) → ℝ) (hcI : Inv (MonoidHom.id (Gm L N)) c) (hcd : dC c = 0) :
    ∃ ω' : Form (HS L N) (k + 1), Good ω' ∧ (∀ γ, FInv ω' (emb L N γ)) ∧ (∀ s, FInv ω' (scal L N s)) ∧
      (∀ z : Chn (Gm L N) (k + 1), IsCyc z →
        ev (emb L N) (intP ω') (one L N) z = ev (MonoidHom.id (Gm L N)) c 1 z) ∧
      ∃ K, ∀ x, ‖fr ω' x‖ ≤ K * ht x ^ (a * (k + 1)) := by
  obtain ⟨P⟩ := hPUa
  obtain ⟨_, hHtinv, ⟨c0, hc0, hc0le⟩, hHtK⟩ := hHt L hC N h1N
  have hht0 : ∀ x, 0 ≤ ht x := fun x => hc0.le.trans (hc0le x)
  obtain ⟨ω, hωG, hωγ, hωs, hωz, C1, hC1⟩ := hWhit L N k (fun x => ht x ^ a) P
    (fun γ x => by simp only [hHtinv]) (fun x => pow_nonneg (hht0 x) _) c hcI hcd
  obtain ⟨p, hp⟩ : ∃ p, p = a * (k + 1) := ⟨_, rfl⟩
  have hfrB : ∀ x, ‖fr ω x‖ ≤ |C1| * ht x ^ p := fun x => by
    calc ‖fr ω x‖ ≤ C1 * (ht x ^ a) ^ (k + 1) := hC1 x
      _ ≤ |C1| * (ht x ^ a) ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (pow_nonneg (hht0 x) _) _)
      _ = |C1| * ht x ^ p := by rw [hp, ← pow_mul]
  have hB : ∀ K : Set (Gp L N), IsCompact K →
      ∃ C, ∀ g ∈ K, ∀ x, |C1| * ht (x * g) ^ p ≤ C * (|C1| * ht x ^ p) := by
    intro K hK
    obtain ⟨C, hC⟩ := hHtK K hK
    refine ⟨|C| ^ p, fun g hg x => ?_⟩
    have h1 : ht (x * g) ≤ |C| * ht x :=
      (hC g hg x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hht0 x))
    calc |C1| * ht (x * g) ^ p ≤ |C1| * (|C| * ht x) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hht0 _) h1 p) (abs_nonneg _)
      _ = |C| ^ p * (|C1| * ht x ^ p) := by rw [mul_pow]; ring
  obtain ⟨ω', hω'G, hω'γ, hω's, hω'z, C2, hC2⟩ :=
    hCen L N k ω hωG hωγ hωs (fun x => |C1| * ht x ^ p) hB hfrB
  refine ⟨ω', hω'G, hω'γ, hω's, fun z hz => (hω'z z hz).trans (hωz z hz), |C2| * |C1|, fun x => ?_⟩
  rw [← hp]
  calc ‖fr ω' x‖ ≤ C2 * (|C1| * ht x ^ p) := hC2 x
    _ ≤ |C2| * (|C1| * ht x ^ p) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (abs_nonneg _) (pow_nonneg (hht0 x) _))
    _ = |C2| * |C1| * ht x ^ p := by ring

theorem key (hPrime : SPrime) (hHecke : SHecke) (hHt : SHt) (hPU : SPU) (hMom : SMom) (hWhit : SWhit)
    (hCen : SCen) (hGap : SGap) (hLoc : SLoc) (hMean : SMean) (hInv : SInv) : SSurj := by
  intro L _ _ hC k hkr n₀
  obtain ⟨π, hπ, hπ25⟩ := hPrime L
  obtain ⟨a, hPUa⟩ := hPU L hC
  obtain ⟨N₀, hN₀⟩ := hHecke L hC k hkr π hπ
  obtain ⟨N₁, hN₁⟩ := hMom L hC (2 * (a * (k + 1)))
  obtain ⟨N, hN⟩ : ∃ N, N = max (max N₀ N₁) (max n₀ 3) := ⟨_, rfl⟩
  have hN0 : N₀ ≤ N := by rw [hN]; exact (le_max_left N₀ N₁).trans (le_max_left _ _)
  have hN1 : N₁ ≤ N := by rw [hN]; exact (le_max_right N₀ N₁).trans (le_max_left _ _)
  have hn₀ : n₀ ≤ N := by rw [hN]; exact (le_max_left n₀ 3).trans (le_max_right _ _)
  have h3N : 3 ≤ N := by rw [hN]; exact (le_max_right n₀ 3).trans (le_max_right _ _)
  have h1N : 1 ≤ N := by omega
  refine ⟨N, hn₀, fun c hcI hcd => ?_⟩
  obtain ⟨d, hd⟩ := hN₁ N hN1
  obtain ⟨ω', hω'G, hω'γ, hω's, hω'z, K, hK⟩ :=
    lem_form hHt hPU hWhit hCen L hC k a N h1N (hPUa N h1N) c hcI hcd
  obtain ⟨_, _, ⟨c0, hc0, hc0le⟩, _⟩ := hHt L hC N h1N
  have hht0 : ∀ x, 0 ≤ ht x := fun x => hc0.le.trans (hc0le x)
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.2 d.fin.ne
  have hsq' : IntegrableOn (fun x => ‖fr ω' (ofS L N x)‖ ^ 2) d.D d.μ := by
    refine Integrable.mono' (hd.const_mul (K ^ 2)) ((lem_meas d hω'G.1).norm.pow 2)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖‖fr ω' (ofS L N x)‖ ^ 2‖ ≤ K ^ 2 * ht (ofS L N x) ^ (2 * (a * (k + 1)))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm 2 (a * (k + 1)), pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK _) 2
  have hint' : IntegrableOn (fun x => fr ω' (ofS L N x)) d.D d.μ := by
    refine Integrable.mono' (hsq'.add (integrable_const (1 : ℝ))) (lem_meas d hω'G.1)
      (Filter.Eventually.of_forall fun x => ?_)
    show ‖fr ω' (ofS L N x)‖ ≤ ‖fr ω' (ofS L N x)‖ ^ 2 + 1
    nlinarith [sq_nonneg (‖fr ω' (ofS L N x)‖ - 1)]
  obtain ⟨ωb, hωbI, hωbfr⟩ := hMean L N (k + 1) h1N d ω' hω'G.1 hω'γ hω's hint'
  have hωbG : Good ωb := (hInv L N k ωb hωbI).1
  have hγ0 : ∀ γ, FInv (ω' - ωb) (emb L N γ) := fun γ => finv_sub (hω'γ γ) (hωbI _)
  have hs0 : ∀ s, FInv (ω' - ωb) (scal L N s) := fun s => finv_sub (hω's s) (hωbI _)
  have hLz0 := lem_Lz d hω'G.1 hωbG.1 hγ0 hs0 hωbfr hint' hsq'
  have e2 : intP (ω' - ωb) = fun y => intP ω' y - intP ωb y := funext (intP_sub hω'G.1 hωbG.1)
  have hG0 : Good (ω' - ωb) := by
    refine ⟨hω'G.1.sub hωbG.1, ?_⟩
    rw [e2, dC_sub, hω'G.2, hωbG.2]
    funext y
    simp
  have hFI : Inv (toK L N) (fun y : Fin (k + 2) → GK L N => intP (ω' - ωb) fun j => toP L N (y j) • one L N) :=
    fun γ y => by
      show (intP (ω' - ωb) fun j => toP L N (toK L N γ • y j) • one L N) =
        intP (ω' - ωb) fun j => toP L N (y j) • one L N
      simp only [smul_eq_mul, map_mul, mul_smul]
      exact intP_inv (hγ0 γ) _
  have hFd : dC (fun y : Fin (k + 2) → GK L N => intP (ω' - ωb) fun j => toP L N (y j) • one L N) = 0 := by
    funext y
    have h4 := congrFun hG0.2 (fun j => toP L N (y j) • one L N)
    simp only [dC, Pi.zero_apply] at h4 ⊢
    exact h4
  have hF0 := hN₀ N hN0 _ hFI hFd fun z hz =>
    lem_bound hGap hLoc L hC π hπ hπ25 N k h3N d (ω' - ωb) hG0 hγ0 hs0 hLz0 z hz
  refine ⟨ωb, hωbI, fun z hz => ?_⟩
  have h5 := hF0 z hz
  rw [ev_toK _ (intP (ω' - ωb)) (fun y => rfl) z, e2, ev_sub] at h5
  rw [← hω'z z hz]
  linarith

end PositivityTheory.KB.JoinReconstruction

end
