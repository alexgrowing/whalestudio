import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFrameLimitsOfOrbit

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt hermC bchar)
open scoped Matrix

namespace GlobalTheory.OrbitNfacTwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

theorem hermC_col_norm {y : Frame X.Ψ N} (ho : X.IsOrtho y) (τ : X.Ψ) (hdet : (mat y τ).det ≠ 0)
    (u : Fin N → ℂ) (i : Fin N) : ‖hermC τ.1 X.Gm (col (mat y τ) i) u‖ = ‖((mat y τ)⁻¹ *ᵥ u) i‖ := by
  set c := (mat y τ)⁻¹ *ᵥ u with hcdef
  have hv : u = mat y τ *ᵥ c := by
    rw [hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.one_mulVec]
  have hg : ∀ a, hermC τ.1 X.Gm (col (mat y τ) i) (col (mat y τ) a) =
      if i = a then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (i : ℕ) : ℝ) : ℂ) else 0 := by
    intro a
    have := congrFun (congrFun (ho τ) i) a
    simpa [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.diagonal_apply] using this
  rw [hv, Data.mulVec_eq_sum_col, ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right]
  simp_rw [ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, hg]
  have hs : |ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (i : ℕ)| = 1 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> simp
  simp [hs]

theorem entry_eq (τ : X.Ψ) (z : Fin N → ℂ) (c : Fin N) :
    z c = ∑ d, hermC τ.1 X.Gm z (Data.emb τ.1 (Pi.single d 1)) * τ.1 (X.Gm⁻¹ d c) := by
  have hG : X.Gm * X.Gm⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit X.Gm_det)
  have h1 : ∀ d, hermC τ.1 X.Gm z (Data.emb τ.1 (Pi.single d 1)) = ∑ a, z a * τ.1 (X.Gm a d) := by
    intro d
    unfold hermC Data.emb
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  simp_rw [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ a, ∑ d, z a * τ.1 (X.Gm a d) * τ.1 (X.Gm⁻¹ d c) = z a * τ.1 ((X.Gm * X.Gm⁻¹) a c) := by
    intro a
    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul]; ring
  simp_rw [h2, hG]
  rw [Finset.sum_eq_single c]
  · simp
  · intro a _ ha; simp [Matrix.one_apply_ne ha]
  · simp

theorem diag_bounds {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b))
    (τ : X.Ψ) {P Q K : ℝ}
    (hP : ∀ (d : Fin N) (ρ : E →+* ℂ) (k : ℕ), ‖perFr X x (Pi.single d 1) ρ k‖ ≤ P)
    (hQ : ∀ d : Fin N, 1 + X.maj x τ (Data.emb τ.1 (Pi.single d 1)) ≤ Q)
    (hK : ∀ d c : Fin N, ‖τ.1 (X.Gm⁻¹ d c)‖ ≤ K) (i : Fin N) :
    (X.p0 ≤ (i : ℕ) → ‖b τ i i‖ ≤ N * (P * (N * (Q * K)))) ∧
    ((i : ℕ) < X.p0 → ‖b τ i i‖⁻¹ ≤ N * (Q * (N * (P * K)))) := by
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb
  have hxd : (mat x τ).det ≠ 0 := (hx τ).1
  have hyd : (mat (rmul x b) τ).det ≠ 0 := (hy τ).1
  have e2 : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  have sumb : ∀ (f g : Fin N → ℂ) (A B : ℝ), (∀ c, ‖f c‖ ≤ A) → (∀ c, ‖g c‖ ≤ B) →
      ‖∑ c, f c * g c‖ ≤ N * (A * B) := by
    intro f g A B hf hg
    calc ‖∑ c, f c * g c‖ ≤ ∑ c : Fin N, A * B := (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => by
          rw [norm_mul]; exact mul_le_mul (hf c) (hg c) (norm_nonneg _) ((norm_nonneg _).trans (hf c)))
      _ = N * (A * B) := by simp
  have hYe : ∀ c, ‖mat (rmul x b) τ c i‖ ≤ N * (Q * K) := by
    intro c
    have h := entry_eq X τ (col (mat (rmul x b) τ) i) c
    rw [show col (mat (rmul x b) τ) i c = mat (rmul x b) τ c i from rfl] at h
    rw [h]
    refine sumb _ _ _ _ (fun d => ?_) (fun d => hK d c)
    rw [hermC_col_norm X ho τ hyd]
    exact (GlobalTheory.OrbitNfac.coord_le X hx hb ho τ _ i).trans (hQ d)
  constructor
  · intro hi
    have hb' : b τ i i = ((mat x τ)⁻¹ * mat (rmul x b) τ) i i := by
      rw [e2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hxd), Matrix.one_mul]; rfl
    rw [hb', Matrix.mul_apply]
    refine sumb _ _ _ _ (fun c => ?_) hYe
    have hpe := perFr_pos X x (Pi.single c 1) τ ((i : ℕ) - X.p0) (by omega)
    have hi' : (⟨X.p0 + ((i : ℕ) - X.p0), by omega⟩ : Fin N) = i := Fin.ext (by simp; omega)
    rw [hi'] at hpe
    have he : (mat x τ)⁻¹ i c = ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 (Pi.single c 1)) i := by
      simp [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply]
    rw [he, ← hpe]
    exact hP _ _ _
  · intro hi
    have hinv : (mat b τ)⁻¹ = (mat (rmul x b) τ)⁻¹ * mat x τ := by
      rw [e2, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hxd), Matrix.mul_one]
    rw [← norm_inv, ← GlobalTheory.OrbitNfac.inv_diag X hb, hinv, Matrix.mul_apply]
    refine sumb _ _ _ _ (fun c => ?_) (fun c => ?_)
    · have he : (mat (rmul x b) τ)⁻¹ i c = ((mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (Pi.single c 1)) i := by
        simp [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply]
      rw [he]
      exact (GlobalTheory.OrbitNfac.coord_le X hx hb ho τ _ i).trans (hQ c)
    · have h := entry_eq X τ (col (mat x τ) i) c
      rw [show col (mat x τ) i c = mat x τ c i from rfl] at h
      rw [h]
      refine sumb _ _ _ _ (fun d => ?_) (fun d => hK d c)
      have hc : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
      have hpn := perFr_neg X x (Pi.single d 1) (conjEmb τ.1) hc τ (Formalism.L2.Pj.conjEmb_conjEmb τ.1).symm
        (X.p0 - 1 - (i : ℕ)) (by omega)
      have hi' : (⟨X.p0 - 1 - (X.p0 - 1 - (i : ℕ)), by omega⟩ : Fin N) = i := Fin.ext (by simp; omega)
      rw [hi'] at hpn
      rw [← hpn]
      exact hP _ _ _

theorem nfac_bound2 {x b : Frame X.Ψ N} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ N) (ho : X.IsOrtho (rmul x b))
    (la : Wt X.Ψ N) {R : ℝ}
    (h1 : ∀ τ (i : Fin N), ‖b τ i i‖⁻¹ ≤ R) (h2 : ∀ τ (i : Fin N), ‖b τ i i‖ ≤ R) :
    0 < X.nfac la x ∧ (X.nfac la x)⁻¹ ≤ R ^ (∑ τ, ∑ i, (la τ i).natAbs) := by
  have hpos : ∀ τ i, 0 < ‖b τ i i‖ := fun τ i => norm_pos_iff.2 (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bdiag_ne X hb τ i)
  have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
    unfold bchar
    simp only [norm_prod, norm_zpow]
  have hb0 : 0 < ‖bchar la b‖ := by
    rw [hbc]
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => zpow_pos (hpos τ i) _
  have h := ReciprocityTheory.ChartRestriction.G.AR.Inst.normFactor_rightBorel_holds N X la x hx b hb
  rw [GlobalTheory.OrbitNfac.nfac_ortho X ho, eq_inv_mul_iff_mul_eq₀ hb0.ne', mul_one] at h
  rw [← h]
  refine ⟨hb0, ?_⟩
  rw [hbc, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun τ _ => inv_nonneg.2 (Finset.prod_nonneg fun i _ => (zpow_pos (hpos τ i) _).le))
    fun τ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun i _ => inv_nonneg.2 (zpow_pos (hpos τ i) _).le) fun i _ => ?_
  rcases le_or_gt 0 (la τ i) with hi | hi
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hi
    rw [hm, zpow_natCast, Int.natAbs_natCast, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) (h1 τ i) m
  · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hi.le
    rw [hm, zpow_neg, inv_inv, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) (h2 τ i) m

end GlobalTheory.OrbitNfacTwo

namespace GlobalTheory

open OrbitNfac OrbitNfacTwo in

theorem nfac_inv_le_pow_of_isOrbit_of_perBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N) (la : Wt X.Ψ N) (n : ℕ) (v : Fin n → Fin N → E) (Lp : Fin n → X.Ψ → Fin (N - X.p0) → ℂ) (Lm : Fin n → X.Ψ → Fin X.p0 → ℂ), IsOrbit X T M γ x → ((∀ j (τ : X.Ψ) (i : Fin (N - X.p0)), Tendsto (fun w => perFr X (x w) (v j) τ.1 i) imTop (𝓝 (Lp j τ i))) ∧ (∀ j (τ : X.Ψ) (i : Fin X.p0), Tendsto (fun w => perFr X (x w) (v j) (conjEmb τ.1) i) imTop (𝓝 (Lm j τ i))) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun j => Lp j τ) = ⊤ ∧ Submodule.span ℂ (Set.range fun j => Lm j τ) = ⊤) → (∀ (u : Fin N → E) (R : ℝ), ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, |w.re| ≤ R → ∀ (ρ : E →+* ℂ) (i : ℕ), ‖perFr X (x w) u ρ i‖ ≤ C * w.im ^ B) → ∃ (C : ℝ) (B : ℕ), ∀ᶠ w in imTop, 0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ C * w.im ^ B := by
  intro E _ _ _ N X T M γ x la n v Lp Lm hO ⟨hp, hm, hs⟩ hper
  choose Kp hKp0 hKp using fun τ : X.Ψ =>
    span_bound imTop (fun w j (i : Fin (N - X.p0)) => perFr X (x w) (v j) τ.1 i) (fun j => Lp j τ)
      (fun j i => hp j τ i) (hs τ).1
  choose Km hKm0 hKm using fun τ : X.Ψ =>
    span_bound imTop (fun w j (i : Fin X.p0) => perFr X (x w) (v j) (conjEmb τ.1) i) (fun j => Lm j τ)
      (fun j i => hm j τ i) (hs τ).2
  choose D hD0 hD using fun (τ : X.Ψ) (j : Fin n) => maj_strip X hO.2.2.1 hO.2.2.2.1 M τ (Data.emb τ.1 (v j))
  choose D' hD0' hD' using fun (τ : X.Ψ) (d : Fin N) =>
    maj_strip X hO.2.2.1 hO.2.2.2.1 M τ (Data.emb τ.1 (Pi.single d 1 : Fin N → E))
  choose Cq Bq hq using fun d : Fin N => hper (Pi.single d 1) M
  have hall := (eventually_all.2 hKp).and ((eventually_all.2 hKm).and (eventually_all.2 hq))
  obtain ⟨R, hR⟩ := eventually_atTop.1 (eventually_comap.1 hall)
  set C : ℝ := ∑ τ, (Kp τ + Km τ) * ∑ j, D τ j with hC
  have hS0 : ∀ τ, 0 ≤ ∑ j, D τ j := fun τ => Finset.sum_nonneg fun j _ => hD0 τ j
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun τ _ => mul_nonneg (add_nonneg (hKp0 τ) (hKm0 τ)) (hS0 τ)
  have hCτ : ∀ τ, (Kp τ + Km τ) * ∑ j, D τ j ≤ C := fun τ =>
    Finset.single_le_sum (f := fun τ => (Kp τ + Km τ) * ∑ j, D τ j)
      (fun τ _ => mul_nonneg (add_nonneg (hKp0 τ) (hKm0 τ)) (hS0 τ)) (Finset.mem_univ τ)
  set Bp : ℕ := ∑ d, Bq d with hBp
  set Cp : ℝ := ∑ d, max (Cq d) 0 with hCp
  set DQ : ℝ := ∑ τ, ∑ d, D' τ d with hDQ
  set K : ℝ := ∑ τ : X.Ψ, ∑ d, ∑ c, ‖τ.1 (X.Gm⁻¹ d c)‖ with hK
  set S : ℕ := ∑ τ, ∑ i, (la τ i).natAbs with hSdef
  have hCp0 : 0 ≤ Cp := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hDQ0 : 0 ≤ DQ := Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun d _ => hD0' τ d
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set A : ℝ := C + N * N * K * Cp * DQ with hA
  have hpowB : ∀ d, Bq d ≤ Bp := fun d =>
    Finset.single_le_sum (f := Bq) (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
  have hCpd : ∀ d, max (Cq d) 0 ≤ Cp := fun d =>
    Finset.single_le_sum (f := fun d => max (Cq d) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ d)
  have hDQd : ∀ τ d, D' τ d ≤ DQ := fun τ d =>
    (Finset.single_le_sum (f := fun d => D' τ d) (fun d _ => hD0' τ d) (Finset.mem_univ d)).trans
      (Finset.single_le_sum (f := fun τ => ∑ d, D' τ d)
        (fun τ _ => Finset.sum_nonneg fun d _ => hD0' τ d) (Finset.mem_univ τ))
  have hKd : ∀ (τ : X.Ψ) d c, ‖τ.1 (X.Gm⁻¹ d c)‖ ≤ K := fun τ d c =>
    ((Finset.single_le_sum (f := fun c => ‖τ.1 (X.Gm⁻¹ d c)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ c)).trans
      (Finset.single_le_sum (f := fun d => ∑ c, ‖τ.1 (X.Gm⁻¹ d c)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ d))).trans
      (Finset.single_le_sum (f := fun τ : X.Ψ => ∑ d, ∑ c, ‖τ.1 (X.Gm⁻¹ d c)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ))
  refine ⟨A ^ S, (Bp + 2) * S, ?_⟩
  have strip : ∀ w : ℂ, R ≤ w.im → T + 1 ≤ w.im → 1 ≤ w.im → |w.re| ≤ M →
      0 < X.nfac la (x w) ∧ (X.nfac la (x w))⁻¹ ≤ (A * w.im ^ (Bp + 2)) ^ S := by
    intro w h1 h2 h3 h4
    have hx := hO.2.2.2.1 w (by linarith)
    set b := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X (x w) with hbdef
    have hb : b ∈ Bor X.Ψ N := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
    have ho : X.IsOrtho (rmul (x w) b) := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
    obtain ⟨k1, k2, k3⟩ := hR w.im h1 w rfl
    have him0 : 0 ≤ w.im := by linarith
    have hsum : ∀ τ, ∑ j, (1 + X.maj (x w) τ (Data.emb τ.1 (v j))) ≤ (∑ j, D τ j) * w.im ^ 2 := fun τ => by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hD τ j w h2 h3 h4
    have fin : ∀ τ (K : ℝ), 0 ≤ K → K ≤ Kp τ + Km τ →
        K * ∑ j, (1 + X.maj (x w) τ (Data.emb τ.1 (v j))) ≤ C * w.im ^ 2 := fun τ K hK hK' =>
      calc _ ≤ K * ((∑ j, D τ j) * w.im ^ 2) := mul_le_mul_of_nonneg_left (hsum τ) hK
        _ = (K * ∑ j, D τ j) * w.im ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hK' (hS0 τ)).trans (hCτ τ)) (sq_nonneg _)
    have hP : ∀ (d : Fin N) (ρ : E →+* ℂ) (k : ℕ), ‖perFr X (x w) (Pi.single d 1) ρ k‖ ≤ Cp * w.im ^ Bp :=
      fun d ρ k => (k3 d h4 ρ k).trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg him0 _)).trans
        (mul_le_mul (hCpd d) (pow_le_pow_right₀ h3 (hpowB d)) (pow_nonneg him0 _) hCp0))
    have hQ : ∀ (τ : X.Ψ) (d : Fin N), 1 + X.maj (x w) τ (Data.emb τ.1 (Pi.single d 1)) ≤ DQ * w.im ^ 2 :=
      fun τ d => (hD' τ d w h2 h3 h4).trans (mul_le_mul_of_nonneg_right (hDQd τ d) (sq_nonneg _))
    have hgrow : w.im ^ 2 ≤ w.im ^ (Bp + 2) := pow_le_pow_right₀ h3 (by omega)
    have hpw : 0 ≤ w.im ^ (Bp + 2) := pow_nonneg him0 _
    have hsmall : C * w.im ^ 2 ≤ A * w.im ^ (Bp + 2) := by
      have : 0 ≤ (N * N * K * Cp * DQ) * w.im ^ (Bp + 2) := mul_nonneg (by positivity) hpw
      calc C * w.im ^ 2 ≤ C * w.im ^ (Bp + 2) := mul_le_mul_of_nonneg_left hgrow hC0
        _ ≤ _ := by rw [hA]; nlinarith
    have hmain : ∀ a : ℝ, a = (N * N * K * Cp * DQ) * w.im ^ (Bp + 2) → a ≤ A * w.im ^ (Bp + 2) := by
      intro a ha
      rw [ha, hA]
      nlinarith [mul_nonneg hC0 hpw]
    have hbd : ∀ τ (i : Fin N), ‖b τ i i‖⁻¹ ≤ A * w.im ^ (Bp + 2) ∧ ‖b τ i i‖ ≤ A * w.im ^ (Bp + 2) := by
      intro τ i
      have hdg := diag_bounds X hx hb ho τ hP (hQ τ) (hKd τ) i
      rcases le_or_gt X.p0 i with hi | hi
      · refine ⟨((quot_bound X hx hb ho τ v (hKp0 τ) (k1 τ) i hi).trans
          (fin τ _ (hKp0 τ) (le_add_of_nonneg_right (hKm0 τ)))).trans hsmall, (hdg.1 hi).trans (hmain _ ?_)⟩
        rw [pow_add]; ring
      · refine ⟨(hdg.2 hi).trans (hmain _ ?_), ((fil_bound X hx hb ho τ v (hKm0 τ) (k2 τ) i hi).trans
          (fin τ _ (hKm0 τ) (le_add_of_nonneg_left (hKp0 τ)))).trans hsmall⟩
        rw [pow_add]; ring
    exact nfac_bound2 X hx hb ho la (fun τ i => (hbd τ i).1) (fun τ i => (hbd τ i).2)
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
