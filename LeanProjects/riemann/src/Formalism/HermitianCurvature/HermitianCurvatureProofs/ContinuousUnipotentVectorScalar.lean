import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosCoreQ

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.JCTx6 Formalism.FourierDecayAlt.P.JCTx6.Pos Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_unipotent_vector_scalar (n : ℕ) (v : G.UT (n + 1) → ℂ) : Continuous (fun t : ℂ => Zv n t v) := by
  show Continuous (fun t : ℂ => fun i j => (G.ptLong (n + 1) t * G.upper v) i j)
  have h : Continuous (fun t : ℂ => (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
    unfold G.ptLong
    exact (continuous_id.smul continuous_const).matrix_mul continuous_const
  exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp h)

set_option maxHeartbeats 1000000 in

theorem posCoreCont : ∃ Cc : ℝ, 0 ≤ Cc ∧
  ∀ (k ph n ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (z z' : Fin (2 * (ph + (n + 1) + ρ) + k + 1) → ℂ), inWb k (ph + (n + 1) + ρ) z → inWb k (ph + (n + 1) + ρ) z' →
    ∀ (Θ : B.DiffOp k (ph + (n + 1) + ρ) Wp Wq) (o κ : ℕ), U.InDD k (ph + (n + 1)) ρ o κ Θ →
    ∀ (χ : ℝ → ℝ) (A₀ ε : ℝ), C6.IsCut0 χ → 0 < ε →
    ∀ (σ : Equiv.Perm (Fin ph)) (d : Fin ph → ℂ) (t0 : ℂ), (∀ i, d i ≠ 0) → t0 ≠ 0 →
    ∀ (As mm : ℕ) (A : ℝ), o ≤ As → κ + (ph + (n + 1)) * o ≤ As → mm ≤ As →
      (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 ≤ As →
      A ≤ 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) →
      Cc * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
      ∃ ε' : ℝ, 0 < ε' ∧
      ∀ (f : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * As) f c →
      ∀ F : B.Mat k (ph + (n + 1) + ρ) → (Wq →L[ℂ] Wp),
        (∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
          F g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) z z' x / ε) : ℝ) : ℂ) • f x) g) →
        ∃ (δ Kb : ℝ) (Dd : ℂ → ℝ), 0 < δ ∧ Tendsto Dd (𝓝 t0) (𝓝 0) ∧ ∀ t : ℂ, dist t t0 < δ → t ≠ 0 ∧
          B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ) Kb ∧
          (∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ ≠ 0 →
            ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ z) (U.lowV k (ph + (n + 1)) ρ z') γ) ∧
          B.CCle A mm (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ - U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t0) z z' F (fun a => a.elim0) γ) (Dd t) := by
  have hIntG := Formalism.FourierDecayAlt.P.JCTx6.Int.intG
  have hTrans := Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable
  obtain ⟨CcU, hCcU⟩ := Formalism.FourierDecayAlt.P.corollary_u2_germ_hypothesis 127 0
  refine ⟨max CcU 0, le_max_right _ _, ?_⟩
  intro k ph n ρ Wp Wq _ _ _ _ _ _ z z' hz hz' Θ o κ hΘ χ A₀ ε hχ hε σ d t0 hd ht0 As mm A ho hκ
    hmm hAs hA hA₀

  have hw : (G.wMat (n + 1)).det ≠ 0 := Formalism.FourierDecayAlt.P.G2.det_wMat_ne_zero (n + 1)
  set c₀ : ℂ := (U.hMat σ d).det * (t0 ^ (n + 1) * (G.wMat (n + 1)).det) with hc₀def
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd) (mul_ne_zero (pow_ne_zero _ ht0) hw)
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.mpr hc₀
  obtain ⟨χD, hχD, hχD1, hχDs⟩ := bump_exists hc₀
  obtain ⟨δ, hδ, hχε⟩ := isCutG_scale hχ hε
  set ε' : ℝ := δ * ε / (2 * ‖c₀‖) ^ 2 with hε'def
  have hε' : 0 < ε' := by positivity
  let UD : U.UData k ph (n + 1) ρ Wp Wq Unit :=
    ⟨σ, d, z, z', fun _ => Θ, χD, fun x => χ (ε⁻¹ * x), δ * ε, ε', o, κ, 0, mm, As⟩
  have hAs1 : 1 ≤ As := le_trans (Nat.one_le_pow _ _ (by omega)) hAs
  have hOk : UD.Ok 0 := by
    refine ⟨hd, by omega, hz, hz', fun _ => hΘ, hχD, hχε, hε', ?_, ho, hκ, by simp [UD], hmm, hAs,
      by simpa using hAs1⟩
    intro w hw'
    have h2 := (hχDs w hw').2
    have h3 : ‖w‖ ^ 2 ≤ (2 * ‖c₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ε' * ‖w‖ ^ 2 ≤ ε' * (2 * ‖c₀‖) ^ 2 := mul_le_mul_of_nonneg_left h3 hε'.le
      _ = δ * ε := by rw [hε'def]; field_simp
  have hA₀U : CcU * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ := by
    refine le_trans ?_ hA₀
    gcongr
    exact le_max_left _ _
  obtain ⟨ha1, -, -, C, hC⟩ := hCcU k ph (n + 1) ρ Wp Wq Unit UD hOk A₀ hA₀U
  set a := UD.a 0 A₀ with ha_def
  set Iv : ℝ := ∫ v, (1 + ‖v‖) ^ (-a) ∂(G.muPi U.betaU (G.UT (n + 1))) with hIv
  refine ⟨ε', hε', ?_⟩
  intro f c hc F hF
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  obtain ⟨V, indexVFirst, indexVSecond, hVc, ⟨MM⟩⟩ :=
    Formalism.FourierDecayAlt.P.compactly_supported_banach_model k ρ (Unit → (Wq →L[ℂ] Wp)) (UD.a 0 A₀) mm UD.S
  obtain ⟨Φ, hΦev, hΦreg⟩ := hC f c hc V MM

  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt k (ph + (n + 1)) ρ Wp Wq z z' o κ Θ χD
    (fun x => χ (ε⁻¹ * x)) (δ * ε) hΘ hχD hχε 0 (3 * As) A₀ (by omega)
  have hStar := hC1 f c hc
  set F₁ := B.opApply Θ (U.cutDG k (ph + (n + 1)) ρ z z' χD (fun x => χ (ε⁻¹ * x)) f) with hF₁def

  have hcF : Continuous (fun t : ℂ => (U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det)) := by fun_prop
  obtain ⟨δ1, hδ1, hδ1c⟩ := Metric.continuous_iff.mp hcF t0 (‖c₀‖ / 4) (div_pos hc₀n (by norm_num))
  have ht0n : 0 < ‖t0‖ := norm_pos_iff.mpr ht0
  set δ0 : ℝ := min δ1 (‖t0‖ / 2) with hδ0def
  have hδ0 : 0 < δ0 := lt_min hδ1 (by positivity)
  have hnear : ∀ t : ℂ, dist t t0 < δ0 → ‖t0‖ / 2 ≤ ‖t‖ ∧ t ≠ 0 ∧
      dist ((U.hMat σ d).det * (t ^ (n + 1) * (G.wMat (n + 1)).det)) c₀ < ‖c₀‖ / 4 := by
    intro t ht
    have h1 : dist t t0 < ‖t0‖ / 2 := lt_of_lt_of_le ht (min_le_right _ _)
    have h2 : ‖t0‖ / 2 ≤ ‖t‖ := by
      have h3 := norm_sub_norm_le t0 t
      rw [dist_eq_norm] at h1
      rw [norm_sub_rev] at h3
      linarith
    refine ⟨h2, fun h0 => ?_, hδ1c t (lt_of_lt_of_le ht (min_le_left _ _))⟩
    rw [h0, norm_zero] at h2
    linarith

  have hB : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), dist (U.DjU k (ph + (n + 1)) ρ g) c₀ < ‖c₀‖ / 4 → F g = F₁ g := by
    intro g hg hgc
    have hne : U.DjU k (ph + (n + 1)) ρ g ≠ 0 := by
      intro h0
      rw [h0, dist_zero_left] at hgc
      linarith
    rw [hF g hg hne]
    refine opApply_congr_open Θ (O := {x | dist (U.DjU k (ph + (n + 1)) ρ x) c₀ < ‖c₀‖ / 4}) ?_ ?_ g ?_
    · exact isOpen_lt ((cont_DjU k (ph + (n + 1)) ρ).dist continuous_const) continuous_const
    · intro x hx
      simp only [U.cutDG]
      rw [hχD1 _ (le_of_lt hx), one_mul, div_eq_inv_mul]
    · exact hgc
  have hZne : ∀ t : ℂ, t ≠ 0 → ∀ v : G.UT (n + 1) → ℂ, G.detM (Zv n t v) ≠ 0 := by
    intro t ht v
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]; exact mul_ne_zero (pow_ne_zero _ ht) hw
  have hOrb : ∀ t : ℂ, dist t t0 < δ0 → ∀ (ξ : U.Xi k ph (n + 1) ρ σ) (v : G.UT (n + 1) → ℂ) (γ : B.Mat k ρ),
      γ ∈ B.GV k ρ → F (U.gaXi k ρ σ d ξ (Zv n t v) γ) = F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ) := by
    intro t ht ξ v γ hγ
    obtain ⟨-, ht', hc'⟩ := hnear t ht
    apply hB _ (Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ _
      (hZne t ht' v) hγ)
    rw [Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice]
    have e : G.detM (Zv n t v) = t ^ (n + 1) * (G.wMat (n + 1)).det := detM_Zv n t v
    rw [e]
    exact hc'

  have hK : IsCompact ((fun w : ℂ => ‖w‖) '' tsupport χD) := hχD.2.1.isCompact.image continuous_norm
  have hK0 : (fun w : ℂ => ‖w‖) '' tsupport χD ⊆ Set.Ioi 0 := by
    rintro _ ⟨w, hw', rfl⟩
    exact lt_of_lt_of_le (by positivity) (hχDs w hw').1
  have hthr : 2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) * ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) <
      (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
        2 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) * ((0 + o : ℕ) : ℝ)) /
        (8 * (2 * ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1)) := by
    have hnd : ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) ≤ (As : ℝ) := by
      have h1 : 2 * (ph + (n + 1) + ρ) + k + 1 ≤ (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 :=
        Nat.le_self_pow (by norm_num) _
      exact_mod_cast h1.trans hAs
    have ha1' := ha1
    simp only [ha_def, U.UData.a, U.a1] at ha1'
    set R : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) with hR
    have hR0 : 0 ≤ R := Nat.cast_nonneg _
    have hD : 0 < 8 * (2 * R + 1) := by positivity
    set Nd : ℝ := ((2 * (ph + (n + 1) + ρ) + k + 1 : ℕ) : ℝ) with hNd
    have hNd1 : 1 ≤ Nd := by rw [hNd]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hle : (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) -
          2 * (R + 1) * (((0 * (n + 1) ^ 2 + 1 + mm) + o : ℕ) : ℝ) - 5 * R * (((0 * (n + 1) ^ 2 : ℕ) : ℝ) + 1) -
          2 * R * (mm : ℝ)) / (8 * (2 * R + 1)) ≤
        (A₀ - (κ : ℝ) - ((ph + (n + 1) : ℕ) : ℝ) * (o : ℝ) - 2 * (R + 1) * ((0 + o : ℕ) : ℝ)) /
          (8 * (2 * R + 1)) := by
      apply div_le_div_of_nonneg_right _ hD.le
      push_cast
      have hm0 : (0 : ℝ) ≤ mm := Nat.cast_nonneg _
      nlinarith
    have hlt : 2 * R * Nd < (((127 : ℕ) : ℝ) + 1) * (R + 1) ^ 3 * (As : ℝ) := by
      have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
      have h1 : 2 * R * Nd < 128 * (R + 1) * Nd := by nlinarith
      have h2 : 128 * (R + 1) * Nd ≤ 128 * (R + 1) ^ 3 * (As : ℝ) := by
        have h3 : (R + 1) ≤ (R + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
        have h4 : (R + 1) * Nd ≤ (R + 1) ^ 3 * (As : ℝ) :=
          mul_le_mul h3 hnd (by linarith) (by positivity)
        nlinarith
      norm_num
      linarith
    exact lt_of_lt_of_le hlt (le_trans ha1' hle)
  have hInt : ∀ t : ℂ, dist t t0 < δ0 → ∀ γ ∈ B.GV k ρ,
      Integrable (gInt k ph n ρ σ d t z z' F γ) (muG k ph n ρ σ) := by
    intro t ht γ hγ
    have ht' := (hnear t ht).2.1
    have h1 := hIntG k ph n ρ σ d t hd ht' _ hK hK0 0 _ hthr z z' (Wq →L[ℂ] Wp) F₁ (C1 * c) hStar γ hγ
    have e : gInt k ph n ρ σ d t z z' F γ = gInt k ph n ρ σ d t z z' F₁ γ := by
      funext y
      unfold gInt
      have e1 : U.gaXi k ρ σ d (y.1, y.2.1) (Matrix.of.symm (t • G.wMat (n + 1) * G.upper y.2.2)) γ =
          U.gaXi k ρ σ d (y.1, y.2.1) (Zv n t y.2.2) γ := rfl
      rw [e1, hOrb t ht _ _ γ hγ]
    rw [e]; exact h1
  have hcore : ∀ t : ℂ, dist t t0 < δ0 → ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ =
        ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) •
          G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t :=
    fun t ht γ hγ => Dx2.SL.core σ d t z z' F γ (hTrans k ph n ρ σ d t z z' _ F γ (hInt t ht γ hγ))

  have ha128 : 128 * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 3 * (As : ℝ) ≤ a := by
    have h := ha1
    norm_num at h ⊢
    exact h
  have ha0 : 0 ≤ a := le_trans (by positivity) ha128
  have hψc : Continuous (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v))) := by
    have h1 : Continuous fun v : G.UT (n + 1) → ℂ => G.superSum (G.upper v) := by
      unfold G.superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp Dx2.SL.cont_upper)
    unfold G.psi
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul h1))))
  have hΦc : ∀ t : ℂ, t ≠ 0 → Continuous (fun v : G.UT (n + 1) → ℂ => Φ (Zv n t v)) := by
    intro t ht
    have hZc : Continuous (fun v : G.UT (n + 1) → ℂ => Zv n t v) := by
      show Continuous (fun v : G.UT (n + 1) → ℂ =>
        (G.ptLong (n + 1) t * G.upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      exact continuous_const.matrix_mul Dx2.SL.cont_upper
    exact continuous_iff_continuousAt.2 fun v => ((hΦreg _ (hZne t ht v)).1.continuousAt).comp hZc.continuousAt
  have hCc : 0 ≤ C * c := by
    have h := (hΦreg _ (hZne t0 ht0 0)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    have hp : 0 < (1 + ‖Zv n t0 0‖) ^ (-a) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp
    linarith [norm_nonneg (Φ (Zv n t0 0))]
  have hbound : ∀ t : ℂ, t ≠ 0 → ∀ v : G.UT (n + 1) → ℂ,
      ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤ C * c * (min 1 ‖t‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro t ht v
    rw [norm_smul, Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_psi, one_mul]
    have h := (hΦreg _ (hZne t ht v)).2 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (Zv_decay n ht v ha0) hCc
    rw [← mul_assoc] at this
    exact this
  have hfin : (Module.finrank ℝ (G.UT (n + 1) → ℂ) : ℝ) < a := by
    have e : Module.finrank ℝ (G.UT (n + 1) → ℂ) = Fintype.card (G.UT (n + 1)) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have hcard : Fintype.card (G.UT (n + 1)) ≤ (n + 1) * (n + 1) := by
      have := Fintype.card_subtype_le (fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have hcardR : ((Fintype.card (G.UT (n + 1)) * 2 : ℕ) : ℝ) ≤ 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
      have : Fintype.card (G.UT (n + 1)) * 2 ≤ 2 * ((n + 1) * (n + 1)) := by omega
      exact_mod_cast this
    rw [e]
    refine lt_of_le_of_lt hcardR (lt_of_lt_of_le ?_ ha128)
    have hn : ((n : ℝ) + 1) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg ph : (0:ℝ) ≤ ph), (Nat.cast_nonneg ρ : (0:ℝ) ≤ ρ)]
    have hAs' : (1 : ℝ) ≤ As := by exact_mod_cast hAs1
    set R1 : ℝ := ((ph + (n + 1) + ρ : ℕ) : ℝ) + 1
    have hR1 : 1 ≤ R1 := by
      have : (0 : ℝ) ≤ ((ph + (n + 1) + ρ : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hn0 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have h1 : 2 * (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ 2 * (R1 * R1) := by gcongr
    have h2 : 2 * (R1 * R1) < 128 * R1 ^ 3 := by nlinarith
    have h3 : 128 * R1 ^ 3 ≤ 128 * R1 ^ 3 * (As : ℝ) := by nlinarith
    linarith
  set m0 : ℝ := min 1 (‖t0‖ / 2) with hm0
  have hm0p : 0 < m0 := lt_min one_pos (by positivity)
  have hbound' : ∀ t : ℂ, dist t t0 < δ0 → ∀ v : G.UT (n + 1) → ℂ,
      ‖G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v)‖ ≤ C * c * m0 ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro t ht v
    obtain ⟨h2, ht', -⟩ := hnear t ht
    refine (hbound t ht' v).trans ?_
    have hmle : m0 ≤ min 1 ‖t‖ := min_le_min le_rfl h2
    have h3 : (min 1 ‖t‖) ^ (-a) ≤ m0 ^ (-a) := Real.rpow_le_rpow_of_nonpos hm0p hmle (by linarith)
    have hv : 0 ≤ (1 + ‖v‖) ^ (-a) := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hCc) hv
  have hgint : Integrable (fun v : G.UT (n + 1) → ℂ => C * c * m0 ^ (-a) * (1 + ‖v‖) ^ (-a))
      (G.muPi U.betaU (G.UT (n + 1))) := by
    rw [Dx2.SL.muPi_betaU]
    apply Integrable.smul_measure_nnreal
    exact (integrable_one_add_norm hfin).const_mul _

  let Wt : ℂ → V := fun t =>
    ∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1)))
  have hWc : ContinuousAt Wt t0 := by
    have hball : ∀ᶠ t in 𝓝 t0, dist t t0 < δ0 := Metric.ball_mem_nhds t0 hδ0
    refine continuousAt_of_dominated ?_ ?_ hgint ?_
    · filter_upwards [hball] with t ht
      exact (hψc.smul (hΦc t (hnear t ht).2.1)).aestronglyMeasurable
    · filter_upwards [hball] with t ht
      exact Eventually.of_forall (hbound' t ht)
    · refine Eventually.of_forall fun v => ?_
      exact continuousAt_const.smul (ContinuousAt.comp (g := Φ) (f := fun t : ℂ => Zv n t v) (x := t0)
        ((hΦreg _ (hZne t0 ht0 v)).1.continuousAt) (continuous_unipotent_vector_scalar n v).continuousAt)

  have key : ∀ t : ℂ, dist t t0 < δ0 → ∀ γ ∈ B.GV k ρ,
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ = MM.ev (((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) • Wt t) γ () := by
    intro t ht γ hγ
    have ht' := (hnear t ht).2.1
    have hφint : Integrable (fun v : G.UT (n + 1) → ℂ => G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
        (G.muPi U.betaU (G.UT (n + 1))) :=
      hgint.mono' (hψc.smul (hΦc t ht')).aestronglyMeasurable (Eventually.of_forall (hbound' t ht))
    have hgN : 0 < B.gN γ ^ a := Real.rpow_pos_of_pos (Formalism.FourierDecayAlt.P.Ux1.gN_pos hγ) a
    let L₀ : V →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
      (LinearMap.proj (R := ℂ) (φ := fun _ : Unit => Wq →L[ℂ] Wp) ()) ∘ₗ
        (LinearMap.proj (R := ℂ) (φ := fun _ : B.Mat k ρ => Unit → (Wq →L[ℂ] Wp)) γ) ∘ₗ MM.ev
    have hL₀ : ∀ w, L₀ w = MM.ev w γ () := fun w => rfl
    have hbd : ∀ w, ‖L₀ w‖ ≤ (B.gN γ ^ a)⁻¹ * ‖w‖ := by
      intro w
      rw [hL₀]
      have h1 := (MM.mem w).2 [] [] (by simp) (by simp) (by simp) γ hγ
      rw [inv_mul_eq_div, le_div_iff₀' hgN]
      exact le_trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ ()) hgN.le) h1
    let L : V →L[ℂ] (Wq →L[ℂ] Wp) := L₀.mkContinuous _ hbd
    have hL : ∀ w, L w = MM.ev w γ () := fun w => rfl
    have hΨ : ∀ v : G.UT (n + 1) → ℂ,
        U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ = MM.ev (Φ (Zv n t v)) γ () := by
      intro v
      rw [hΦev _ (hZne t ht' v) γ hγ]
      show _ = (U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' (UD.F1 f) (Zv n t v) γ) ()
      unfold U.PhiFun
      have e := (ContinuousLinearEquiv.funUnique Unit ℂ (Wq →L[ℂ] Wp)).integral_comp_comm
        (μ := U.muXi k ph (n + 1) ρ σ)
        (fun ξ => U.psiStar k ρ σ z z' ξ • UD.F1 f (U.gaXi k ρ σ d ξ (Zv n t v) γ))
      refine Eq.trans ?_ e
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      show U.psiStar k ρ σ z z' ξ • F (U.gaXi k ρ σ d ξ (Zv n t v) γ) =
        U.psiStar k ρ σ z z' ξ • F₁ (U.gaXi k ρ σ d ξ (Zv n t v) γ)
      rw [hOrb t ht ξ v γ hγ]
    rw [hcore t ht γ hγ]
    have hOm : G.OmLong U.betaU n (fun Z => U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F Z γ) t = L (Wt t) := by
      show _ = L (∫ v, G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v) ∂(G.muPi U.betaU (G.UT (n + 1))))
      rw [← L.integral_comp_comm hφint]
      unfold G.OmLong
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      show G.psi U.betaU (G.superSum (G.upper v)) • U.PhiFun (p := ph) (s := n + 1) k ρ σ d z z' F (Zv n t v) γ =
        L (G.psi U.betaU (G.superSum (G.upper v)) • Φ (Zv n t v))
      rw [L.map_smul, hL, hΨ v]
    rw [hOm, hL, map_smul]
    rfl

  have hAa : A ≤ a := le_trans hA ha128
  have hCCv : ∀ w : V, B.CCle A mm (fun γ => MM.ev w γ ()) ‖w‖ := fun w =>
    Formalism.FourierDecayAlt.P.compactly_supported_monotone k ρ (Wq →L[ℂ] Wp) a A ‖w‖ mm _ hAa (ccle_unit (MM.mem w))
  set πc : ℂ := ((Real.pi ^ ((n + 1) * n / 2) : ℝ) : ℂ) with hπc
  have hWfc : ContinuousAt (fun t => πc • Wt t) t0 := continuousAt_const.smul hWc
  obtain ⟨δ2, hδ2, hδ2c⟩ := Metric.continuousAt_iff.mp hWfc 1 one_pos
  have hself : dist t0 t0 < δ0 := by rw [dist_self]; exact hδ0
  refine ⟨min δ0 δ2, ‖πc • Wt t0‖ + 1, fun t => ‖πc • Wt t - πc • Wt t0‖, lt_min hδ0 hδ2,
    tendsto_iff_norm_sub_tendsto_zero.mp hWfc, fun t ht => ?_⟩
  have ht0' : dist t t0 < δ0 := lt_of_lt_of_le ht (min_le_left _ _)
  have ht2 : dist t t0 < δ2 := lt_of_lt_of_le ht (min_le_right _ _)
  refine ⟨(hnear t ht0').2.1, ?_, ?_, ?_⟩
  · have h1 := Formalism.FourierDecayAlt.P.Ux1.cc_congr (fun γ hγ => (key t ht0' γ hγ).symm) (hCCv (πc • Wt t))
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c h1 ?_
    have h2 := hδ2c ht2
    simp only [dist_eq_norm] at h2
    have h3 := norm_le_insert' (πc • Wt t) (πc • Wt t0)
    linarith
  · intro γ hγ hne
    by_contra hlt
    have hnot : γ ∉ UD.S := fun h => hlt h
    apply hne
    rw [key t ht0' γ hγ, MM.off _ γ hγ hnot]
    rfl
  · have heq : ∀ γ ∈ B.GV k ρ, MM.ev (πc • Wt t - πc • Wt t0) γ () = U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t) z z' F (fun a => a.elim0) γ - U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Dx2.SL.sigP σ) (Dx2.SL.dP d t0) z z' F (fun a => a.elim0) γ := by
      intro γ hγ
      rw [key t ht0' γ hγ, key t0 hself γ hγ, map_sub]
      try rfl
    exact Formalism.FourierDecayAlt.P.Ux1.cc_congr heq (hCCv (πc • Wt t - πc • Wt t0))

end Formalism.FourierDecayAlt.P.LastBlockContinuity
