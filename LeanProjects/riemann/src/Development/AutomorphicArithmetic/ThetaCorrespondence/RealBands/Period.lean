import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCuspFormPeriodNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsMultTEqPoin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

set_option maxHeartbeats 1000000 in
open GlobalTheory.SepPer.PerNe in

theorem exists_cusp_form_theta_period_ne_zero : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → PackEx → DepthPays →
    Ev fun {D} _ {L} {sc} {G} W M => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
      (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∀ t ∈ Rows L W.θ M₀, t ≠ 0 →
        ∃ y ∈ CoreForms G W.θ 0 MP, ∃ v w, per0 G M (y v) (t w) ≠ 0 := by
  intro hHC hCW hCRD hPE hDP
  obtain ⟨C, hC, hPack⟩ := hPE
  intro ε CF hCF
  obtain ⟨x₁, hx₁⟩ := hPack ε CF hCF
  obtain ⟨x₂, hx₂⟩ := hDP C hC ε CF hCF
  refine ⟨max x₁ x₂, ?_⟩
  intro D large₂ hε hx hSz T L μ0 hL G W M hM M₀ MP t ht ht0
  obtain ⟨p, hp⟩ := hx₁ D large₂ hε (le_trans (le_max_left _ _) hx) hSz T L μ0 hL G W M hM M₀ MP
  obtain ⟨s, hs0, hs1, hsLip, hsN1, hsN2⟩ := hx₂ D large₂ hε (le_trans (le_max_right _ _) hx) hSz T L μ0 hL G W M hM
  obtain ⟨hsdY, hsdV, hlam, hz0, hJ, hrY, hrV, hmY⟩ :=
    GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices D (offQ_of_sizeRows hSz) T L μ0 hL _ G W M hM

  have hθ : IsInfFam W.θ := W.θ_is
  have hmod : G.modul ≠ ⊥ := G.pl.modul_ne_bot _
  have hRow := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨v, hvμ, hv𝓕⟩ : ∃ v : GlobalTheory.Unf.Vol (Yc D 0), v.μ = M.ν (.grid 0 0) ∧ v.𝓕 = M.fd (.grid 0 0) :=
    ⟨⟨_, _, hRow.1, hRow.2⟩, rfl, rfl⟩
  obtain ⟨b, x, hb, hbx⟩ := GlobalTheory.T.exists_bound_multiplicity_value_exceeds_half hCRD D W.θ hθ (Yc D 0) (parB (Ptw D) 0) M₀ (levRow L : Set (GA D (Yc D 0))) v t ht ht0 p.w hp.1.ne
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb x)
  obtain ⟨hAutSm, hCusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCRD D (Yc D 0) _ M₀ W.θ hθ _ 1 t ht
    (PiTensorProduct.tprod ℂ p.w)
  have hLip := GlobalTheory.T.unipotentPeriod_value_lipschitz_realOneParameter hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp (levRow L : Set (GA D (Yc D 0))) 1 t ht b hb
  have hInv : ∀ k ∈ Lev.levA (Yc D 0) (congLev D.sp.cm (Yc D 0).gram (L.ΛY 0)
      (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)})), ∀ y, t (PiTensorProduct.tprod ℂ p.w) (y * k) = t (PiTensorProduct.tprod ℂ p.w) y := by
    intro k hk y
    rw [multT_apply_mul_lev ht _ k hk y, Pi.one_apply, one_mul]
  have hLong : Long W.θ p.A (L.ΛY 0) x s := by
    by_contra hn
    have hg1 : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hr1 : 1 ≤ (Yc D 0).rank := by rw [hrY]; exact (odd_r D).pos
    have hmin : ∀ τ, min (Finset.univ.filter fun a => p.A.ε τ a = true).card
        (Finset.univ.filter fun a => p.A.ε τ a = false).card ≤ D.R.m := fun τ => min_le_of_right_le (hmY p.A τ)
    have h := GlobalTheory.T.norm_cuspForm_le_of_shortLine D W.θ hθ (Yc D 0) p.A (L.ΛY 0) hsdY (D.host.g 0 * D.host.g 1) D.R.m hg1 hm1 hr1 hmin (t (PiTensorProduct.tprod ℂ p.w))
      hAutSm.toIsAutFun hCusp hInv (Real.exp (loss D C large₂.sc.b) * b) (by positivity) hLip x s hs0 hs1 hn
    rw [hrY] at h
    have : ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b / 2 := by
      refine h.trans ?_
      have := mul_le_mul_of_nonneg_left hsLip hb0
      nlinarith
    linarith
  rw [hlam] at hsdV hz0
  have hJ' : ∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈
      congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul → k ∈ (levRow L : Set (GA D (Yc D 0))) := by
    rw [← hlam]; exact hJ
  obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentPeriod_adelic_clauses_of_real hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp
    (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul hsdV hmod hz0 (levRow L : Set (GA D (Yc D 0))) hJ' t ht v.μ v.haar
  have hN1 : 2 * Real.exp (loss D C large₂.sc.b + (6 * ((G.V (.core 0)).rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤
      s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm G.modul) := by
    rw [hrV]; push_cast; exact hsN1
  have hne := GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp.1 (L.ΛY 0) G.modul hsdY hmod v (t (PiTensorProduct.tprod ℂ p.w)) c b s
    x (GlobalTheory.Core.Mi.BotPin.isContAut_multT ht _) hb hbx hs0.le (by linarith) hLong hc hN1 hsN2
  have hKD : KDecay MP p.v₀ := fun τ => ⟨(hp.1.dec τ).1, fun a ha =>
    GlobalTheory.T.coefficientDecay_kFinite_second_vector hHC D _ _ MP τ (p.v₀ τ) _ (hp.1.dec τ).1 (hp.1.dec τ).2 a ha⟩
  obtain ⟨y, hy, hyv⟩ := exists_multT_eq_poin hHC hCW hCRD D W.θ hθ (G.V (.core 0)) _ MP (G.sp.dec0.lat (L.ΛY 0) fun _ => 1)
    G.modul hsdV hmod p.v₀ hKD (p.g₀⁻¹ * stabilizerEmbedding G.sp.dec0 x⁻¹) ⟨D.eTau.symm 1⟩
  obtain ⟨v₀', hv₀'⟩ : ∃ v₀' : MP.Vec, ∀ τ, (v₀' τ : MP.H τ) = p.v₀ τ :=
    ⟨fun τ => ⟨p.v₀ τ, GlobalTheory.Core.Mi.kFin_le_sm hHC MP τ (hp.1.dec τ).1⟩, fun _ => rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : MP.Vec, ∀ τ, (a' τ : MP.H τ) = MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ) :=
    ⟨fun τ => ⟨MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ),
      GlobalTheory.UnifEvery.rep_mem_sm MP τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) (v₀' τ).2⟩, fun _ => rfl⟩
  have hv₀f : (fun τ => (v₀' τ : MP.H τ)) = p.v₀ := funext hv₀'
  have hU := (mem_multT W.θ MP _ 1 y).1 hy
  have key := GlobalTheory.RealEquiv.mult_realElt D (G.V (.core 0)) _ W.θ MP _ 1 _ hU (fun τ => cmp W.θ τ p.g₀)
    (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) v₀' a' ha'
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hp.1.real] at key
  have hyg : ∀ g, y (PiTensorProduct.tprod ℂ a') g =
      poin W.θ MP (congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul) (p.v W.θ)
        (stabilizerEmbedding G.sp.dec0 x⁻¹) (p.v W.θ) g := by
    intro g
    rw [apply_tprod_eq, key]
    show PiTensorProduct.lift.symm y v₀' (g * p.g₀) = _
    rw [← apply_tprod_eq, hyv v₀' (fun τ => (hv₀' τ).symm ▸ (hp.1.dec τ).1), hv₀f]
    exact GlobalTheory.T.coefficientPoincareSeries_move_real_point D W.θ hθ (G.V (.core 0)) _ MP _ p.v₀ p.g₀ hp.1.real _ g
  have hmem : y ∈ CoreForms G W.θ 0 MP := by
    show y ∈ MultT W.θ MP (Lev.levA (G.V (.core 0)) (G.levCong (.core 0)) : Set (GA D (G.V (.core 0)))) 1
    unfold GridData.levCong
    rw [hlam]
    exact hy
  have hper : per0 G M (y (PiTensorProduct.tprod ℂ a')) (t (PiTensorProduct.tprod ℂ p.w)) ≠ 0 := by
    unfold per0
    simp_rw [hyg]
    rw [hvμ, hv𝓕] at hne
    exact hne
  exact ⟨y, hmem, _, _, hper⟩

end UpperTheory.Lit.Cusp

end
