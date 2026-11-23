import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanSignatureFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalDataStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

open GlobalTheory.PackLoc

theorem realInputE_transport : RealInputE → ∃ C : ℝ, 0 < C ∧
  ∀ (m k N : ℕ) (hk : m = k) (hN : N = k + 1) (e : Option (Fin k) ≃ Fin (k + 1)) (ε : Fin N → Bool) (lam : Fin N → ℝ)
    (ε' : Fin m → Bool) (mu : Fin m → ℝ) (B : ℝ),
    GlobalTheory.SepReal.Par e (fun i => ε (Fin.cast hN.symm i)) (fun i => lam (Fin.cast hN.symm i))
      (fun i => ε' (Fin.cast hk.symm i)) (fun i => mu (Fin.cast hk.symm i)) B →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin m) (Fin m) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam π → Formalism.MainNotions.S.IsDS ε' mu σ →
      ∃ (v₀ v : H) (g₀ : Matrix (Fin N) (Fin N) ℂ) (w' : H') (c : ℝ),
        Formalism.MainNotions.S.IsLowUnit ε lam π v₀ ∧ g₀ ∈ Formalism.MainNotions.S.UJset ε ∧ v = π g₀ v₀ ∧
        GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v ∧ GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε')) σ w' ∧
        ‖w'‖ = 1 ∧ 0 < c ∧
        (ε (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) none) = true ∧ ∀ i, ε (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (some i)) = ε' i) ∧
        (∀ b : H', ∫ h, star ⟪v, π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
            ⟪b, σ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ε') = (c : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) ∧
        (∀ g ∈ Formalism.MainNotions.S.UJset ε,
          Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
            (Formalism.REAL.muG ε') ∧
          ∫ h, ‖⟪v, π (g * GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤
            c * GlobalTheory.SepReal.big C k B *
              Real.sqrt (∑ a, ‖g a (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) ∧
        (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
          Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) X) v,
            π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε') ∧
          ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) X) v,
            π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤
            c * GlobalTheory.SepReal.big C k B) ∧
        ∃ A : ℝ, ∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪v, π g v⟫_ℂ‖ ≤ A * GlobalTheory.SepReal.hsn g ^ (-(20 * ((k : ℝ) + 1) ^ 2)) := by
  rintro ⟨C, hC, hF⟩
  refine ⟨C, hC, ?_⟩
  intro m k N hk hN e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ
  subst hk
  subst hN
  have he : ((finCongr (rfl : m = m)).optionCongr.trans (e.trans (finCongr (rfl : m + 1 = m + 1).symm))) = e := by
    ext x
    cases x <;> simp
  rw [he]
  have hP' : GlobalTheory.SepReal.Par e ε lam ε' mu B := hP
  obtain ⟨v₀, v, g₀, w', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    hF m e ε lam ε' mu B hP' H H' π σ hπ hσ
  exact ⟨v₀, v, g₀, w', c, h1, h2, h3, h4, h5, h6, h7, hP'.signs, h8, h9, h10, h11⟩

theorem act_of_eigen : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w' : (GlobalTheory.ConjDS.conjModel M₀).H τ) (c₁ lam : ℝ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ u, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) = M₀.σ τ (Formalism.MainNotions.S.umat u)) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  ‖w'‖ = 1 →
  (∀ b : (GlobalTheory.ConjDS.conjModel M₀).H τ, ∫ h, star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
      ⟪b, (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) =
    (c₁ : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) →
  ∀ b : M₀.H τ, ∫ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) *
      ⟪b, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    ((lam * c₁ : ℝ) : ℂ) * ⟪b, GlobalTheory.ConjDS.cj (M₀.H τ) w'⟫_ℂ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ w' c₁ lam h1 h2 hH hw ha b
  set b' : (GlobalTheory.ConjDS.conjModel M₀).H τ := (GlobalTheory.ConjDS.cj (M₀.H τ)).symm b with hb'
  have key : ∀ x : Matrix (Fin Y.rank) (Fin Y.rank) ℂ,
      ⟪b, M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ =
        star ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ x w'⟫_ℂ := by
    intro x
    exact (inner_conj_symm (𝕜 := ℂ) b (M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w'))).symm
  let F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ := fun x => ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ *
        ⟪b, M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ
  have e1 : ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) *
      ⟪b, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ =
      F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    intro u
    simp only [F, h1, h2, GlobalTheory.ConjDS.rv_rv]
  have e2 : ∀ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), F (Formalism.MainNotions.S.umat h) =
      star (star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ) := by
    intro h; simp only [F, key, star_mul, star_star, mul_comm]
  have hww : ⟪w', w'⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have e4 : star ⟪b', w'⟫_ℂ = ⟪b, GlobalTheory.ConjDS.cj (M₀.H τ) w'⟫_ℂ :=
    inner_conj_symm (𝕜 := ℂ) b (GlobalTheory.ConjDS.cj (M₀.H τ) w')
  rw [integral_congr_ae (ae_of_all _ e1), hH F, integral_congr_ae (ae_of_all _ e2)]
  rw [show (∫ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), star (star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)))
      = star (∫ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)))
      from integral_conj]
  rw [ha b', hww, one_mul, star_mul, e4]
  simp [Complex.real_smul]
  ring

theorem locOK_of_eigen : RealInputE → ∃ C : ℝ, 0 ≤ C ∧ Ev fun {D} _ _ {sc} {G} W _ => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))) (τ : D.what₂.Tau),
  ∃ (εA : Fin (Yc D 0).rank → Bool) (A : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) ℂ) (εB : Fin (G.V (.core 0)).rank → Bool)
    (B : Matrix (Fin (G.V (.core 0)).rank) (Fin (G.V (.core 0)).rank) ℂ) (v₀ : MP.H τ)
    (g₀ : Matrix (Fin (G.V (.core 0)).rank) (Fin (G.V (.core 0)).rank) ℂ) (w : M₀.H τ) (c : ℂ),
    GlobalTheory.PackLoc.LocOK W.θ G.sp.dec0 M₀ MP τ (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log sc.b) εA A εB B v₀ g₀ w c := by
  intro hRI
  obtain ⟨C, hC, hT1⟩ := realInputE_transport hRI
  refine ⟨C, hC.le, ?_⟩
  intro ε0 CF hCF
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.branchingHypotheses_gridParameters_largeScale ε0 CF hCF
  refine ⟨x₀, fun D large₂ h1 h2 h3 T L μ0 hL G W M hM => ?_⟩
  have hP := hx₀ D large₂ h1 h2 h3 T L μ0 hL G W M hM
  intro M₀ MP τ
  have hY : (Yc D 0).rank = D.R.r := by
    have h := D.sp.Y_rank 0 (Nat.zero_le _)
    simpa [Yc, Ranks.rankY] using h
  have hN : (G.V (.core 0)).rank = D.R.r + 1 := by
    have h : (Yc D 0).rank + 1 = (G.V (.core 0)).rank := G.sp.dec0.rank
    omega
  obtain ⟨⟨e, hPar⟩, hlog, -⟩ := hP τ (fun i => MP.ε τ (Fin.cast hN.symm i)) (fun i => MP.lam τ (Fin.cast hN.symm i))
    (fun i => (GlobalTheory.ConjDS.conjModel M₀).ε τ (Fin.cast hY.symm i)) (fun i => (GlobalTheory.ConjDS.conjModel M₀).lam τ (Fin.cast hY.symm i))
    (isEnum_cast' hN.symm (MP.enum τ)) (isEnum_cast' hY.symm ((GlobalTheory.ConjDS.conjModel M₀).enum τ))
  obtain ⟨v₀, v, g₀', w', c₁, hlow, hg₀', hv, hsmv, hsmw, hw1, hc₁, ⟨hs0, hs1⟩, ha, hb, hc, A₀, hA₀⟩ :=
    hT1 (Yc D 0).rank D.R.r (G.V (.core 0)).rank hY hN e (MP.ε τ) (MP.lam τ) ((GlobalTheory.ConjDS.conjModel M₀).ε τ)
      ((GlobalTheory.ConjDS.conjModel M₀).lam τ) (large₂.sc.b ^ 2) hPar (MP.H τ) ((GlobalTheory.ConjDS.conjModel M₀).H τ) (MP.σ τ)
      ((GlobalTheory.ConjDS.conjModel M₀).σ τ) (MP.ds τ) ((GlobalTheory.ConjDS.conjModel M₀).ds τ)
  set e' : Option (Fin (Yc D 0).rank) ≃ Fin (G.V (.core 0)).rank :=
    (finCongr hY).optionCongr.trans (e.trans (finCongr hN.symm)) with he'
  obtain ⟨B, hBu, hBg, hBad, hBz, hBmem, hBemb⟩ := GlobalTheory.T.exists_signature_matrix_extension D W.θ W.θ_is (Yc D 0) (G.V (.core 0)) G.sp.dec0 τ
    ((GlobalTheory.ConjDS.conjModel M₀).ε τ) ((GlobalTheory.ConjDS.conjModel M₀).fr τ) (MP.ε τ) e'
    ((GlobalTheory.ConjDS.conjModel M₀).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M₀).fr_gram τ) hs0 hs1
  obtain ⟨lam, hlam, hH⟩ := GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple _ (M₀.ε τ)
  obtain ⟨hreal, hmco⟩ := GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame D _ _ MP τ B g₀' v₀ hBu hBg hg₀'
  obtain ⟨hpt, hlieX⟩ := GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place D W.θ W.θ_is (Yc D 0) _ M₀ τ
  have hAu := (GlobalTheory.ConjDS.conjModel M₀).fr_unit τ
  have hbig : GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2) ≤ Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) := by
    unfold GlobalTheory.SepReal.big
    apply Real.exp_le_exp.2
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * ((D.R.r : ℝ) + 1) ^ 4 by positivity)
    calc C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2)
        ≤ C * ((D.R.r : ℝ) + 1) ^ 4 * (6 * Real.log large₂.sc.b) := h
      _ = 6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b := by ring
  have hm0 : ∀ u, GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀ (GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e' (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := fun u => by
    rw [hmco _ (hBmem _ (hpt u).1), hBemb _ (hpt u).1, (hpt u).2.1, ← hv]
  have hmg : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.core 0)) τ), ∀ u,
      GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀ (g * GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e' (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := by
    intro g hg u
    rw [hmco _ (UH_mul' hg (hBmem _ (hpt u).1)), conj_mul' hBu, hBemb _ (hpt u).1, (hpt u).2.1, ← hv]
  have hm1 : ∀ X ∈ lieAt (Yc D 0) τ, ∀ (s : ℝ) u,
      GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀
        (GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (cmp W.θ τ (oneP W.θ (Yc D 0) τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e'
        (NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M₀).fr τ * X * ((GlobalTheory.ConjDS.conjModel M₀).fr τ)⁻¹)) *
          GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := by
    intro X hX s u
    have hmem := UH_mul' ((hlieX X hX).2 s).1 (hpt u).1
    rw [hmco _ (hBmem _ hmem), hBemb _ hmem, conj_mul' hAu, ((hlieX X hX).2 s).2, (hpt u).2.1, ← hv]
  have hK : lam * (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) ≤
      Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    calc lam * (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) = (lam * c₁) * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2) := by ring
      _ ≤ (lam * c₁) * Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) :=
        mul_le_mul_of_nonneg_left hbig (mul_pos hlam hc₁).le
      _ = _ := by ring
  have hL := GlobalTheory.T.smooth_vector_matrixCoeff_integrable (Yc D 0).rank (G.V (.core 0)).rank e' (MP.ε τ) ((GlobalTheory.ConjDS.conjModel M₀).ε τ)
    (MP.H τ) (MP.σ τ) v (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) (MP.ds τ).2.2.1 hs0 hs1 hsmv
    (fun g hg => (hb g hg).1) hc
  obtain ⟨Cd, hCd⟩ := GlobalTheory.T.matrix_coefficient_decay_in_frame_of_translate_decay D.R.r (G.V (.core 0)).rank hN (MP.ε τ) (MP.H τ) (MP.σ τ) v₀ g₀' (MP.fr τ)
    (gramAt D (G.V (.core 0)) τ) A₀ (MP.ds τ).2.2.1 hg₀' (MP.fr_unit τ) (MP.fr_gram τ)
    (fun g hg => by rw [← hv]; exact hA₀ g hg)
  refine ⟨(GlobalTheory.ConjDS.conjModel M₀).ε τ, (GlobalTheory.ConjDS.conjModel M₀).fr τ, MP.ε τ, B, v₀, B⁻¹ * g₀' * MP.fr τ,
    GlobalTheory.ConjDS.cj (M₀.H τ) w', ((lam * c₁ : ℝ) : ℂ), ?_⟩
  exact
    { unitA := hAu
      gramA := (GlobalTheory.ConjDS.conjModel M₀).fr_gram τ
      unitB := hBu
      gramB := hBg
      adapted := hBad
      real := hreal
      kfin := GlobalTheory.isKFin_of_mem_lowKSub _ _ _ _ _ _ hlow.2
      dec := ⟨Cd, hCd⟩
      sm := GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth D _ _ M₀ τ w' hsmw
      ne := by
        intro h
        have h' : ‖GlobalTheory.ConjDS.cj (M₀.H τ) w'‖ = 1 := (GlobalTheory.ConjDS.cj (M₀.H τ)).norm_map w' ▸ hw1
        rw [h, norm_zero] at h'
        exact zero_ne_one h'
      cne := Complex.ofReal_ne_zero.2 (mul_pos hlam hc₁).ne'
      act := act_of_eigen D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ) w' c₁ lam
        hm0 (fun u => (hpt u).2.2) (fun F => (hH ℂ F).2) hw1 ha
      far := GlobalTheory.T.transversal_coefficient_decay_at_real_place D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ) B c₁ lam
        _ _ D.R.r hBu hBg hBz hN hmg (fun F => (hH ℂ F).1) (fun F => (hH ℝ F).2) hc₁ hlam hbig hb
      lip := GlobalTheory.T.matrix_coefficient_lipschitz_at_real_place D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ)
        ((GlobalTheory.ConjDS.conjModel M₀).fr τ) _ lam _ _ hm0 hm1 (fun X hX => (hlieX X hX).1) hL (fun F => hH ℝ F) hlam hK }

theorem packEx_of_eigen : RealInputE → PackEx := by
  intro hRI
  obtain ⟨C, hC, hloc⟩ := locOK_of_eigen hRI
  refine ⟨6 * C, by positivity, ?_⟩
  intro ε CF hCF
  obtain ⟨x₀, hx⟩ := hloc ε CF hCF
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx0 hS T L μ0 hL G W M hM M₀ MP
  have h := hx D large₂ hε hx0 hS T L μ0 hL G W M hM M₀ MP
  choose εA A εB B v₀ g₀ w c hOK using h
  obtain ⟨p, hp⟩ := GlobalTheory.T.realVectors_allPlaces_of_localData W.θ W.θ_is G.sp.dec0 M₀ MP _ εA A εB B v₀ g₀ w c hOK
  refine ⟨p, ?_⟩
  have e : loss D (6 * C) large₂.sc.b = Fintype.card D.what₂.Tau * (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) := by
    unfold loss; ring
  rw [e]
  exact hp

end UpperTheory.Lit.Branch

end
