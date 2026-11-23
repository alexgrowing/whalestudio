import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.BotMulVecExt
import Formalism.LocalToGlobal.ProjectiveLattices.UnifFrDet

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC bchar)
open scoped Matrix

namespace GlobalTheory.OrbitNfac

theorem span_bound {α : Type} (l : Filter α) {n m : ℕ} (L : α → Fin n → Fin m → ℂ) (L0 : Fin n → Fin m → ℂ)
    (hL : ∀ j i, Tendsto (fun w => L w j i) l (𝓝 (L0 j i))) (hs : Submodule.span ℂ (Set.range L0) = ⊤) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ w in l, ∀ (ℓ : Fin m → ℂ) (k : Fin m), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * L w j i‖ := by
  classical
  have hA : ∀ k : Fin m, ∃ A : Fin n → ℂ, ∑ j, A j • L0 j = Pi.single k 1 := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose A hA using hA
  set K : ℝ := ∑ k, ∑ j, ‖A k j‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hAK : ∀ k j, ‖A k j‖ ≤ K := fun k j =>
    (Finset.single_le_sum (f := fun j => ‖A k j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k => ∑ j, ‖A k j‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  have ht : Tendsto (fun w => K * ∑ j, ∑ i, ‖L0 j i - L w j i‖) l (𝓝 (K * ∑ j : Fin n, ∑ i : Fin m, (0 : ℝ))) := by
    refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ => ?_)
    have := ((tendsto_const_nhds (x := L0 j i)).sub (hL j i)).norm
    simpa using this
  simp only [Finset.sum_const_zero, mul_zero] at ht
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with w hw ℓ k
  set S : ℝ := ∑ j, ‖∑ i, ℓ i * L w j i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have key : ∀ k, ‖ℓ k‖ ≤ K * S + ‖ℓ‖ / 2 := by
    intro k
    have e1 : ℓ k = ∑ j, A k j * ((∑ i, ℓ i * L w j i) + ∑ i, ℓ i * (L0 j i - L w j i)) := by
      have e2 : ℓ k = ∑ i, ℓ i * (∑ j, A k j • L0 j) i := by
        rw [hA k]; simp [Pi.single_apply]
      rw [e2]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∀ j, ‖A k j * ((∑ i, ℓ i * L w j i) + ∑ i, ℓ i * (L0 j i - L w j i))‖ ≤
        K * ‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * (K * ∑ i, ‖L0 j i - L w j i‖) := by
      intro j
      have h1 : ‖∑ i, ℓ i * (L0 j i - L w j i)‖ ≤ ‖ℓ‖ * ∑ i, ‖L0 j i - L w j i‖ := by
        rw [Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ℓ i) (norm_nonneg _)
      rw [norm_mul]
      calc _ ≤ K * (‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * ∑ i, ‖L0 j i - L w j i‖) :=
            mul_le_mul (hAK k j) ((norm_add_le _ _).trans (by linarith)) (norm_nonneg _) hK0
        _ = _ := by ring
    calc ‖ℓ k‖ ≤ ∑ j, (K * ‖∑ i, ℓ i * L w j i‖ + ‖ℓ‖ * (K * ∑ i, ‖L0 j i - L w j i‖)) := by
          rw [e1]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => e3 j)
      _ = K * S + ‖ℓ‖ * (K * ∑ j, ∑ i, ‖L0 j i - L w j i‖) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ K * S + ‖ℓ‖ / 2 := by nlinarith [norm_nonneg ℓ]
  have h2 : ‖ℓ‖ ≤ K * S + ‖ℓ‖ / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).2 key
  have := norm_le_pi_norm ℓ k
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

theorem coord_le {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    (u : Fin N → ℂ) (i : Fin N) : ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ ≤ 1 + X.maj x τ u := by
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  have h := UnipMove.GraphH.maj_ortho X ho τ ((mat (rmul x b) τ)⁻¹ *ᵥ u)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hy τ).1), Matrix.one_mulVec,
    GlobalTheory.MajInv.maj_rmul X hx hb] at h
  have h2 : ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ ^ 2 ≤ X.maj x τ u := by
    rw [h]
    exact Finset.single_le_sum (f := fun j => ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith [sq_nonneg (‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖ - 1), sq_nonneg ‖((mat (rmul x b) τ)⁻¹ *ᵥ u) i‖]

theorem inv_diag {b : Frame X.Ψ N} (hb : b ∈ Bor X.Ψ N) (τ : X.Ψ) (i : Fin N) :
    (mat b τ)⁻¹ i i = (b τ i i)⁻¹ := by
  have hi := (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb τ).2
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (mat b τ) (Ne.isUnit (hb τ).1)) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_left h
  · intro a _ ha
    rcases lt_or_gt_of_ne ha with h1 | h1
    · have : (mat b τ)⁻¹ i a = 0 := hi i a h1
      rw [this, zero_mul]
    · have : mat b τ a i = 0 := (hb τ).2 a i h1
      rw [this, mul_zero]
  · simp

theorem quot_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    {n : ℕ} (v : Fin n → Fin N → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (ℓ : Fin (N - X.p0) → ℂ) (k : Fin (N - X.p0)), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * perFr X x (v j) τ.1 i‖)
    (i : Fin N) (hi : X.p0 ≤ i) : ‖b τ i i‖⁻¹ ≤ K * ∑ j, (1 + X.maj x τ (Data.emb τ.1 (v j))) := by
  have hinv := (ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb τ).2
  let e : Fin (N - X.p0) → Fin N := fun k => ⟨X.p0 + k, by have := k.2; omega⟩
  have h1 := h (fun k => (mat b τ)⁻¹ i (e k)) ⟨i - X.p0, by have := i.2; omega⟩
  have he : e ⟨i - X.p0, by have := i.2; omega⟩ = i := Fin.ext (by simp only [e]; omega)
  simp only [he] at h1
  rw [inv_diag X hb, norm_inv] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hK)
  have e1 : ∑ k : Fin (N - X.p0), (mat b τ)⁻¹ i (e k) * perFr X x (v j) τ.1 k =
      ((mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (v j)) i := by
    have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
    rw [e2, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    show _ = ∑ a, (mat b τ)⁻¹ i a * ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 (v j)) a
    refine Finset.sum_of_injOn e (fun a _ c _ hac => Fin.ext ?_)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun a _ ha => ?_) (fun k _ => ?_)
    · have := congrArg Fin.val hac
      simp only [e] at this
      omega
    · have ha' : (a : ℕ) < X.p0 := by
        by_contra hc
        exact ha ⟨⟨a - X.p0, by have := a.2; omega⟩, by simp, Fin.ext (by simp only [e]; omega)⟩
      have : (mat b τ)⁻¹ i a = 0 := hinv i a (by show (a : ℕ) < i; omega)
      rw [this, zero_mul]
    · rw [perFr_pos X x (v j) τ k (e k).2]
  rw [e1]
  exact coord_le X hx hb ho τ _ i

theorem fil_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b)) (τ : X.Ψ)
    {n : ℕ} (v : Fin n → Fin N → E) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ (ℓ : Fin X.p0 → ℂ) (k : Fin X.p0), ‖ℓ k‖ ≤ K * ∑ j, ‖∑ i, ℓ i * perFr X x (v j) (conjEmb τ.1) i‖)
    (i : Fin N) (hi : (i : ℕ) < X.p0) : ‖b τ i i‖ ≤ K * ∑ j, (1 + X.maj x τ (Data.emb τ.1 (v j))) := by
  have hp := X.p0_le
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  let e : Fin X.p0 → Fin N := fun k => ⟨X.p0 - 1 - k, by have := k.2; omega⟩
  have h1 := h (fun k => b τ (e k) i) ⟨X.p0 - 1 - i, by omega⟩
  have he : e ⟨X.p0 - 1 - i, by omega⟩ = i := Fin.ext (by simp only [e]; omega)
  simp only [he] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hK)
  have hc : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have e1 : ∑ k : Fin X.p0, b τ (e k) i * perFr X x (v j) (conjEmb τ.1) k =
      hermC τ.1 X.Gm (col (mat (rmul x b) τ) i) (Data.emb τ.1 (v j)) := by
    have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
    rw [e2, UnipMove.GraphH.col_mul, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left]
    refine Finset.sum_of_injOn e (fun a _ c _ hac => Fin.ext ?_)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun a _ ha => ?_) (fun k _ => ?_)
    · have := congrArg Fin.val hac
      simp only [e] at this
      have := a.2
      have := c.2
      omega
    · have ha' : X.p0 ≤ (a : ℕ) := by
        by_contra hc
        exact ha ⟨⟨X.p0 - 1 - a, by omega⟩, by simp, Fin.ext (by simp only [e]; omega)⟩
      have : col (mat b τ) i a = 0 := (hb τ).2 a i (by show (i : ℕ) < a; omega)
      rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, this, zero_mul]
    · rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left,
        perFr_neg X x (v j) (conjEmb τ.1) hc τ (Formalism.L2.Pj.conjEmb_conjEmb τ.1).symm k (e k).2]
      rfl
  rw [e1]
  refine le_trans (le_of_eq ?_) (coord_le X hx hb ho τ (Data.emb τ.1 (v j)) i)
  set c := (mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (v j) with hcdef
  have hv : Data.emb τ.1 (v j) = mat (rmul x b) τ *ᵥ c := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hy τ).1), Matrix.one_mulVec]
  have hg : ∀ a, hermC τ.1 X.Gm (col (mat (rmul x b) τ) i) (col (mat (rmul x b) τ) a) = if i = a then 1 else 0 := by
    intro a
    have := congrFun (congrFun (ho τ) i) a
    simpa [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.diagonal_apply, ReciprocityTheory.ChartRestriction.G.FD.sgn, hi] using this
  rw [hv, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right]
  simp_rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hg]
  simp

theorem nfac_ortho {y : Frame X.Ψ N} (ho : X.IsOrtho y) (la : Wt X.Ψ N) : X.nfac la y = 1 := by
  have h : ∀ τ i, ‖dmin X.Gm y τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rcases ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) with h | h <;> rw [h] <;> simp
  unfold Data.nfac
  simp [h]

theorem nfac_bound {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b))
    (la : Wt X.Ψ N) (hla : ∀ τ (j : Fin N), (X.p0 ≤ j → 0 ≤ la τ j) ∧ ((j : ℕ) < X.p0 → la τ j ≤ 0)) {R : ℝ}
    (h1 : ∀ τ (i : Fin N), X.p0 ≤ i → ‖b τ i i‖⁻¹ ≤ R) (h2 : ∀ τ (i : Fin N), (i : ℕ) < X.p0 → ‖b τ i i‖ ≤ R) :
    0 < X.nfac la x ∧ (X.nfac la x)⁻¹ ≤ R ^ (∑ τ, ∑ i, (la τ i).natAbs) := by
  have hpos : ∀ τ i, 0 < ‖b τ i i‖ := fun τ i => norm_pos_iff.2 (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bdiag_ne X hb τ i)
  have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
    unfold bchar
    simp only [norm_prod, norm_zpow]
  have hb0 : 0 < ‖bchar la b‖ := by
    rw [hbc]
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => zpow_pos (hpos τ i) _
  have h := ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_rightBorel_holds N X la x hx b hb
  rw [nfac_ortho X ho, eq_inv_mul_iff_mul_eq₀ hb0.ne', mul_one] at h
  rw [← h]
  refine ⟨hb0, ?_⟩
  rw [hbc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun τ _ => inv_nonneg.2 (Finset.prod_nonneg fun i _ => (zpow_pos (hpos τ i) _).le))
    fun τ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun i _ => inv_nonneg.2 (zpow_pos (hpos τ i) _).le) fun i _ => ?_
  rcases le_or_gt X.p0 i with hi | hi
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hla τ i).1 hi)
    rw [hm, zpow_natCast, Int.natAbs_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) (h1 τ i hi) m
  · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat ((hla τ i).2 hi)
    rw [hm, zpow_neg, inv_inv, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 τ i hi) m

theorem nfac_shift {T : ℝ} {M : ℕ} {γ : GL (Fin N) E} {x : ℂ → Frame X.Ψ N} (h : IsOrbit X T M γ x) (la : Wt X.Ψ N)
    (k : ℤ) : ∀ w : ℂ, T < w.im → X.nfac la (x (w + k * M)) = X.nfac la (x w) := by
  obtain ⟨-, hγ, -, hd, hs⟩ := h
  have one : ∀ w : ℂ, T < w.im → X.nfac la (x (w + M)) = X.nfac la (x w) := by
    intro w hw
    obtain ⟨b, hb, hb1, e⟩ := hs w hw
    rw [e, ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_rightBorel_holds N X la _ (GlobalTheory.MajInv.lact_mem_dom X (X.Γ_stab γ hγ) (hd w hw)) b hb,
      ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_leftAction_holds N X la γ hγ _ (hd w hw)]
    simp [bchar, hb1]
  induction k using Int.induction_on with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    rw [← ih w hw, ← one (w + ((k : ℤ) : ℂ) * M) (by simpa using hw)]
    congr 2
    push_cast
    ring
  | pred k ih =>
    intro w hw
    rw [← ih w hw, ← one (w + ((-(k : ℤ) - 1 : ℤ) : ℂ) * M) (by simpa using hw)]
    congr 2
    push_cast
    ring

theorem maj_strip {T : ℝ} {x : ℂ → Frame X.Ψ N} (hx : DifferentiableOn ℂ x {w | T < w.im})
    (hd : ∀ w : ℂ, T < w.im → x w ∈ X.dom) (M : ℝ) (τ : X.Ψ) (u : Fin N → ℂ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w : ℂ, T + 1 ≤ w.im → 1 ≤ w.im → |w.re| ≤ M → 1 + X.maj (x w) τ u ≤ D * w.im ^ 2 := by
  set w0 : ℂ := ⟨0, T + 1⟩ with hw0
  have h0 : T < w0.im := by simp [hw0]
  have hm : 0 ≤ X.maj (x w0) τ u := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X (hd w0 h0) τ u
  refine ⟨1 + (2 + M ^ 2 + (1 + |T + 1|) ^ 2) * X.maj (x w0) τ u, by positivity, fun w h1 h2 h3 => ?_⟩
  have h := GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x hx hd w0 w h0 (by linarith) τ u
  have e0 : w0.im - T = 1 := by simp [hw0]
  rw [e0, one_mul] at h
  have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (T + 1 - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [hw0]
    ring
  have hs : 1 ≤ w.im ^ 2 := by nlinarith
  have e2 : w.re ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have e3 : (T + 1 - w.im) ^ 2 ≤ ((1 + |T + 1|) * w.im) ^ 2 := by
    have a1 := le_abs_self (T + 1)
    have a2 := neg_abs_le (T + 1)
    have a3 := abs_nonneg (T + 1)
    exact sq_le_sq' (by nlinarith) (by nlinarith)
  have e4 : ‖w0 - w‖ ^ 2 / (w.im - T) ≤ ‖w0 - w‖ ^ 2 := div_le_self (sq_nonneg _) (by linarith)
  have e5 : 2 + ‖w0 - w‖ ^ 2 / (w.im - T) ≤ (2 + M ^ 2 + (1 + |T + 1|) ^ 2) * w.im ^ 2 := by
    rw [mul_pow] at e3
    nlinarith [sq_nonneg M]
  have e6 := mul_le_mul_of_nonneg_right e5 hm
  nlinarith

end GlobalTheory.OrbitNfac

namespace GlobalTheory

open OrbitNfac in

theorem nfac_inv_le_pow_of_isOrbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) (la : Wt X.Ψ N) (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → X.Ψ → Fin (N - X.p0) → ℂ) (Lm : Fin n → X.Ψ → Fin X.p0 → ℂ), IsOrbit X T M γ x → (∀ τ (j : Fin N), (X.p0 ≤ j → 0 ≤ la τ j) ∧ ((j : ℕ) < X.p0 → la τ j ≤ 0)) → ((∀ j (τ : X.Ψ) (i : Fin (N - X.p0)), Tendsto (fun w => perFr X (x w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : X.Ψ) (i : Fin X.p0), Tendsto (fun w => perFr X (x w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤) → ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C * w.im ^ B := by
  intro E _ _ _ N X T M γ x la n v Lp Lm hO hla ⟨hp, hm, hs⟩
  choose Kp hKp0 hKp using fun τ : X.Ψ =>
    span_bound imTop (fun w j (i : Fin (N - X.p0)) => perFr X (x w) (v j) τ.1 i) (fun j => Lp j τ)
      (fun j i => hp j τ i) (hs τ).1
  choose Km hKm0 hKm using fun τ : X.Ψ =>
    span_bound imTop (fun w j (i : Fin X.p0) => perFr X (x w) (v j) (conjEmb τ.1) i) (fun j => Lm j τ)
      (fun j i => hm j τ i) (hs τ).2
  choose D hD0 hD using fun (τ : X.Ψ) (j : Fin n) => maj_strip X hO.2.2.1 hO.2.2.2.1 M τ (Data.emb τ.1 (v j))
  have hall := (eventually_all.2 hKp).and (eventually_all.2 hKm)
  obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_comap.1 hall)
  set C : ℝ := ∑ τ, (Kp τ + Km τ) * ∑ j, D τ j with hC
  have hS0 : ∀ τ, 0 ≤ ∑ j, D τ j := fun τ => Finset.sum_nonneg fun j _ => hD0 τ j
  have hCτ : ∀ τ, (Kp τ + Km τ) * ∑ j, D τ j ≤ C := fun τ =>
    Finset.single_le_sum (f := fun τ => (Kp τ + Km τ) * ∑ j, D τ j)
      (fun τ _ => mul_nonneg (add_nonneg (hKp0 τ) (hKm0 τ)) (hS0 τ)) (Finset.mem_univ τ)
  refine ⟨C ^ (∑ τ, ∑ i, (la τ i).natAbs), 2 * ∑ τ, ∑ i, (la τ i).natAbs, ?_⟩
  have strip : ∀ w : ℂ, R ≤ w.im → T + 1 ≤ w.im → 1 ≤ w.im → |w.re| ≤ M →
      0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ (C * w.im ^ 2) ^ (∑ τ, ∑ i, (la τ i).natAbs) := by
    intro w h1 h2 h3 h4
    have hx := hO.2.2.2.1 w (by linarith)
    have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
    have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
    obtain ⟨k1, k2⟩ := hR w.im h1 w rfl
    have hsum : ∀ τ, ∑ j, (1 + X.maj (x w) τ (Data.emb τ.1 (v j))) ≤ (∑ j, D τ j) * w.im ^ 2 := fun τ => by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hD τ j w h2 h3 h4
    have fin : ∀ τ (K : ℝ), 0 ≤ K → K ≤ Kp τ + Km τ →
        K * ∑ j, (1 + X.maj (x w) τ (Data.emb τ.1 (v j))) ≤ C * w.im ^ 2 := fun τ K hK hK' =>
      calc _ ≤ K * ((∑ j, D τ j) * w.im ^ 2) := mul_le_mul_of_nonneg_left (hsum τ) hK
        _ = (K * ∑ j, D τ j) * w.im ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hK' (hS0 τ)).trans (hCτ τ)) (sq_nonneg _)
    exact nfac_bound X hx hb ho la hla
      (fun τ i hi => (quot_bound X hx hb ho τ v (hKp0 τ) (k1 τ) i hi).trans
        (fin τ _ (hKp0 τ) (le_add_of_nonneg_right (hKm0 τ))))
      (fun τ i hi => (fil_bound X hx hb ho τ v (hKm0 τ) (k2 τ) i hi).trans
        (fin τ _ (hKm0 τ) (le_add_of_nonneg_left (hKp0 τ))))
  refine eventually_comap.2 (eventually_atTop.2 ⟨max R (max (T + 1) 1), fun t ht w hw => ?_⟩)
  subst hw
  simp only [max_le_iff] at ht
  obtain ⟨h1, h2, h3⟩ := ht
  have hM : (0 : ℝ) < M := Nat.cast_pos.2 hO.1
  have him : (w + ((-⌊w.re / M⌋ : ℤ) : ℂ) * M).im = w.im := by simp
  have hre : (w + ((-⌊w.re / M⌋ : ℤ) : ℂ) * M).re = w.re - ⌊w.re / M⌋ * M := by simp; ring
  have h := strip (w + ((-⌊w.re / M⌋ : ℤ) : ℂ) * M) (him ▸ h1) (him ▸ h2) (him ▸ h3) (by
    rw [hre]
    have a1 := Int.sub_floor_div_mul_nonneg w.re hM
    have a2 := Int.sub_floor_div_mul_lt w.re hM
    rw [abs_of_nonneg a1]
    exact a2.le)
  rw [nfac_shift X hO la _ w (by linarith), him, mul_pow, ← pow_mul] at h
  exact h

end GlobalTheory
