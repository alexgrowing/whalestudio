import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothLevOfCk

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.Rad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma thr_big (k r m : ℕ) :
    JF.TransportedAlt k r (6 * (r : ℝ) * (m : ℝ) + 9 * ((r : ℝ) + 1) * (((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 1)) m := by
  unfold JF.TransportedAlt
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r]

theorem jf_smoothLev {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) :
    SmoothLev k r 0 (OmPlus k r D.z D.z') (B.JF D F) := by
  refine smoothLev_of_ck (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus _ _) fun m => ?_
  exact (Formalism.FourierDecayAlt.P.jacquet_derivative_formula k r Wp Wq D _ m F (thr_big k r m) (hF _ m)).1

lemma μE_one (i j : ℕ) : PI.QnWCellW.μE (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) i j =
    if i < k + 1 ∧ j < k + 1 ∧ i = j then 1 else 0 := by
  unfold PI.QnWCellW.μE
  by_cases h : i < k + 1 ∧ j < k + 1
  · rw [dif_pos h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [h]
    · rw [if_neg (by simpa [Fin.ext_iff] using hij), if_neg (by tauto)]
  · rw [dif_neg h, if_neg (by tauto)]

theorem wCell_last_eq (c : Fin r → ℂ) : wCell k r (Fin.last r) c = bigCell k r c 1 := by
  rw [PI.QnWCellW.wCell_last]
  ext p q
  rw [PI.QnWCellW.Wm_range_apply, PI.QnWCellW.bigCell_apply]
  simp only [μE_one, PI.QnWCellW.cf, Fin.ext_iff, PI.QnWCellW.swp_val]
  have hp := p.isLt
  have hq := q.isLt
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega) | (congr 3; omega) | (rw [show 2 * r + k - (q : ℕ) = (p : ℕ) by omega])

lemma glev_last_uwb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g ∈ B2.UWb k r := by
  exact ⟨hg.1, fun a => hg.2 a (by simp)⟩

lemma zetaL_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    zetaL k r z z' (Fin.last r) g = herm (Hpk k r) (g *ᵥ z') z := by
  simp only [zetaL, Formalism.FourierDecayAlt.P.Qx5.fvec_last]

theorem wCell_mem_omPlus {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (hG : 0 < GGl k r z z' g) :
    wCell k r (Fin.last r) c * g ∈ OmPlus k r z z' := by
  have hgz' : inWb k r (g *ᵥ z') := by
    intro i hi
    have hi0 := i.isLt
    rcases hi with hi | hi
    · have e1 := Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right (Hpk k r) (g *ᵥ z') (esI k r ⟨i.val, hi⟩)
      rw [← (hg.2 ⟨i.val, hi⟩ (by simpa using hi)).2, Formalism.FourierDecayAlt.P.Qx5.herm_UH hg.1,
        Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right] at e1
      have key : ∀ v : Fin (2 * r + k + 1) → ℂ, (Hpk k r *ᵥ v) (esI k r ⟨i.val, hi⟩) = v i := by
        intro v
        simp only [mulVec, dotProduct, Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rfl
      rw [key, key] at e1
      rw [← e1]
      exact hz' i (Or.inl hi)
    · have ha : 2 * r + k - i.val < r := by omega
      have e1 := Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right (Hpk k r) (g *ᵥ z') (eI k r ⟨_, ha⟩)
      rw [← (hg.2 ⟨_, ha⟩ (by simpa using ha)).1, Formalism.FourierDecayAlt.P.Qx5.herm_UH hg.1,
        Formalism.FourierDecayAlt.P.Qx5.herm_bvec_right] at e1
      have hi' : esI k r ⟨_, ha⟩ = i := Fin.ext (by simp only [esI]; omega)
      have key : ∀ v : Fin (2 * r + k + 1) → ℂ, (Hpk k r *ᵥ v) (eI k r ⟨_, ha⟩) = v i := by
        intro v
        simp only [mulVec, dotProduct, Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hi']
      rw [key, key] at e1
      rw [← e1]
      exact hz' i (Or.inr hi)
  have hwv : ∀ v, inWb k r v → bigCell k r c 1 *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv]
    rw [Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV, Matrix.one_mulVec, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv]
  have hZ : Zhat k r z z' (wCell k r (Fin.last r) c * g) = Matrix.diagonal fun a : Fin (r + 1) =>
      if h : a.val < r then c ⟨a.val, h⟩ else zetaL k r z z' (Fin.last r) g := by
    rw [zetaL_last, ← hwv _ hgz', ← Formalism.QuantumDeterminants.bigCellZhat k r z (g *ᵥ z') c 1 hz hgz', wCell_last_eq]
    ext a b
    simp only [Zhat]
    by_cases hb : b.val < r
    · simp only [fvec, dif_pos hb, ← mulVec_mulVec, (hg.2 ⟨b.val, hb⟩ (by simpa using hb)).1]
    · simp only [fvec, dif_neg hb, mulVec_mulVec]
  have hD := fun l => Formalism.QuantumDeterminants.BruhatBigCell.dmin_diag z z' _ _ hZ l
  have h0 : Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨r, by omega⟩ = ∏ a : Fin r, c a := by
    rw [hD]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [Fin.val_castLE, a.isLt, dif_pos]
  have h1 : Dmin k r z z' (wCell k r (Fin.last r) c * g) (Fin.last (r + 1)) =
      (∏ a : Fin r, c a) * zetaL k r z z' (Fin.last r) g := by
    rw [hD]
    refine (Fin.prod_univ_castSucc _).trans ?_
    congr 1
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp only [Fin.val_castLE, Fin.val_castSucc, a.isLt, dif_pos]
    · simp
  have hP : (∏ a : Fin r, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc a
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [hD]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have hi : (Fin.castLE (Nat.le_of_lt_succ l.isLt) i).val < r := by
      have := i.isLt
      simp only [Fin.val_castLE]
      omega
    simp only [dif_pos hi]
    exact hc _
  · unfold Gf
    rw [h1, h0, Complex.normSq_mul]
    have hP' : 0 < Complex.normSq (∏ a : Fin r, c a) := Complex.normSq_pos.mpr hP
    have hG' := hG
    unfold GGl at hG'
    nlinarith [mul_pos hP' hG']

theorem GGl_uw {z z' : Fin (2 * r + k + 1) → ℂ} {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z')
    (g : Mx k r) : GGl k r z z' (h * g * h') = GGl k r z z' g := by
  simp only [GGl, Formalism.FourierDecayAlt.P.Qx5.zeta_inv hh hh']

theorem domR_uw {z z' : Fin (2 * r + k + 1) → ℂ} {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ DomR k r z z')
    {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    (x.1, h * x.2 * h') ∈ DomR k r z z' := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨h1, ?_, ?_⟩
  · exact Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.UW_Glev hh _) h2)
      (Formalism.FourierDecayAlt.P.Qx5.UW_Glev hh' _)
  · show 0 < GGl k r z z' (h * x.2 * h')
    rw [GGl_uw hh hh']
    exact h3

theorem sf_resG {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} {J : Mx k r → E}
    (hJ : SmoothLev k r 0 D J) :
    SmoothFam k r (Fin.last r) {x | x.1 ∈ OmX r ∧ wCell k r (Fin.last r) x.1 * x.2 ∈ D}
      (resG k r (Fin.last r) J) := by
  have hWs : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ => wCell k r (Fin.last r) c) (OmX r) := by
    unfold wCell
    exact Formalism.FourierDecayAlt.P.Qx3.wlist_smooth _
  have hWG : ∀ c ∈ OmX r, wCell k r (Fin.last r) c ∈ Glev k r 0 := by
    intro c hc
    unfold wCell
    exact Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hG0 : ∀ x : (Fin r → ℂ) × Mx k r, x.1 ∈ OmX r → x.2 ∈ Glev k r (Fin.last r) →
      wCell k r (Fin.last r) x.1 * x.2 ∈ Glev k r 0 := fun x h1 h2 =>
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (hWG _ h1) (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) h2)
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hJ _ ⟨hG0 x₀ hx₀.1 hg₀, hx₀.2⟩
  have hM : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => wCell k r (Fin.last r) x.1 * x.2)
      {x | x.1 ∈ OmX r} :=
    Formalism.FourierDecayAlt.P.Qx3.cdo_mul (hWs.comp contDiffOn_fst (fun x hx => hx)) contDiffOn_snd
  have hρ : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ))
      (OmX r) := by
    have hp : ContDiffOn ℝ ∞ (fun c : Fin r → ℂ =>
        ∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1 : ℝ)) (OmX r) :=
      contDiffOn_prod fun a _ => by
        simp only [Fin.val_last, a.isLt, ↓reduceIte]
        exact Formalism.FourierDecayAlt.P.Qx3.cd_normPow a _
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hp
  refine ⟨{x | x.1 ∈ OmX r} ∩ (fun x => wCell k r (Fin.last r) x.1 * x.2) ⁻¹' U,
    fun x => ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖x.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
      F (wCell k r (Fin.last r) x.1 * x.2),
    hM.continuousOn.isOpen_inter_preimage ((Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).preimage continuous_fst) hU,
    ⟨hx₀.1, hmem⟩, ?_, ?_⟩
  · exact (hρ.comp contDiffOn_fst (fun x hx => hx.1)).smul
      (hF.comp (hM.mono Set.inter_subset_left) (fun x hx => hx.2))
  · intro x hx hxg
    simp only [resG]
    rw [hfF _ hx.2 (hG0 x hx.1 hxg)]

end Formalism.FourierDecayAlt.P5.Rad
