import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AbsAZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.ExistsCtxOkOfPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisationDictionaryCharacterLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.abelian₂.LevelModel

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.Member Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = xiR D := by
  unfold xiR
  have hs : ∀ σ : D.host.E →+* ℂ, ‖σ D.host.sqrtMinusD‖ ^ 2 = ‖(D.host.d : ℂ)‖ := fun σ => by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg]
  have hn : ‖τ D.host.sqrtMinusD‖ = ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ((hs τ).trans (hs _).symm)
  rw [show D.host.xi0 = -1 / ((Ideal.absNorm D.host.ccK : D.host.E) * D.host.sqrtMinusD) from rfl]
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul, hn]

theorem exists_levelLaws (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (hH : H.d = D.host.d) (Dw : Datum H)
    (V : HSp D) (hV : V.SigOK) (hr : V.rank = D.R.r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : IotaOK Dw V ι) (hpq : 1 ≤ Dw.p + Dw.q)
    (l : Level H) (hA : l.A = 1) (Xo : Moduli Dw l) (c : Coeff l) :
    ∃ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r), LevelLaws U V dict := by
  obtain ⟨Kf, hK, -⟩ := GlobalTheory.RecDict.exists_isLevelK D V l.M
  have hgood : ∀ σ, GoodEmb c σ → ∃ (U : Unf Xo c σ D.R.r) (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r)
      (mu : GA D V → ℂ) (x₀ : _) (ι' : _) (χ : _), PkgLaws V hr ι' Kf χ U dict mu x₀ := fun σ hσ => by
    obtain ⟨⟨C, hC, -⟩, -⟩ := GlobalTheory.Member.exists_ctx D H Dw l Xo c σ V D.R.r hr ι hι hpq hA hσ
    obtain ⟨un, dict, mu, -, -, h2⟩ := GlobalTheory.Member.exists_pkgLaws D _ _ l Xo c σ _ _ C hC Kf hK 1
      ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
    exact ⟨C.unf un, dict, mu, C.x₀, C.ι, _, h2⟩
  have hall : ∀ σ : c.F →+* ℂ, ∃ (U : Unf Xo c σ D.R.r) (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r),
      GoodEmb c σ → ∃ (mu : GA D V → ℂ) (x₀ : _) (ι' : _) (χ : _), PkgLaws V hr ι' Kf χ U dict mu x₀ := fun σ => by
    by_cases hσ : GoodEmb c σ
    · obtain ⟨U, dict, h⟩ := hgood σ hσ
      exact ⟨U, dict, fun _ => h⟩
    · obtain ⟨U, dict, -⟩ := hgood c.F.val.toRingHom rfl
      obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws GlobalTheory.firstFiveLaws.2.1.secTwist
        _ _ Dw _ Xo c hpq σ
      exact ⟨{ Comp := Unit, X := fun _ => U.X (dict 1).1, un := fun _ _ => y }, fun _ => ⟨(), fun _ => 0⟩,
        fun h => absurd h hσ⟩
  choose U dict h using hall
  refine ⟨U, dict, hH, hA, hV, fun σ hσ => ?_, fun σ hσ a n _ k γ _ => ?_, fun σ hσ => ?_, fun σ hσ k τ => ?_⟩
  · obtain ⟨_, _, _, _, h⟩ := h σ hσ
    exact h.unf
  · obtain ⟨_, _, _, _, h⟩ := h σ hσ
    exact h.chi1 _ _ _
  · obtain ⟨_, _, _, _, h⟩ := h σ hσ
    obtain ⟨_, _, _, _, _, th, h1, h2, -⟩ := h.dictLaws
    exact ⟨Kf, th, hr, hK, h1, h2, h.muUnit.2.2.2⟩
  · obtain ⟨_, _, _, _, h⟩ := h σ hσ
    rw [(h.modelW k).2, map_neg, norm_neg]
    exact norm_embedding_hostFormConstant_eq D τ

theorem exists_levelLaws_at_lift (D : D7) (j : ℕ) (hj : 1 ≤ j ∧ j ≤ D.R.m) (l : Level (hostOfRecord D)) (hA : l.A = 1) :
    3 ≤ D.R.r ∧ ∃ (Xo : Moduli (datumW D j hj) l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
      (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r),
      LevelLaws U (D.sp.W j) dict := by
  have hm := D.R.m_add_three_le_k
  have hpq : 1 ≤ (datumW D j hj).p + (datumW D j hj).q := by
    show 1 ≤ (D.R.sigW j).1 + (D.R.sigW j).2
    simp only [Ranks.sigW]
    omega
  obtain ⟨Xo⟩ := GlobalTheory.Moduli.moduli_scheme_exists D.host.E (hostOfRecord D) (datumW D j hj) l hpq
  obtain ⟨c, -⟩ := GlobalTheory.exists_coeff_containing D.host.E (hostOfRecord D) l ∅ (by simp)
  refine ⟨by unfold Ranks.r; omega, Xo, c, exists_levelLaws D _ rfl _ _ (D.sp.W_sig j) (D.sp.W_rank j hj.1 hj.2) _
    (GlobalTheory.Member.Inhab.iotaOK_at_lift D j hj) hpq l hA Xo c⟩

theorem levelLaws_of_lawsM {D : D7} (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j)
    (dict : ∀ σ : T.Q.c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((T.U j σ).X k).Ψ D.R.r)
    (hd : ∀ σ, GoodEmb T.Q.c σ → HEq (dict σ) (T.dict j σ)) : LevelLaws (T.U j) (D.sp.W j) dict := by
  refine ⟨h.pins.1.1, h.pins.2.1.2, D.sp.W_sig j, h.unf j hj, h.chiTriv j hj, fun σ hσ => ?_, h.xiAbs j hj⟩
  obtain ⟨th, hr, h1, h2⟩ := h.dictU j hj σ hσ
  have h3 := h.levelK j hj σ hσ
  have h4 := (h.muUnit j hj σ hσ).2.2.2
  have h5 := hd σ hσ
  have e := h.spaceW j hj σ hσ
  rw [← h.pins.2.1.1] at h3
  generalize dict σ = d at h5 ⊢
  generalize T.dict j σ = d' at h2 h4 h5
  generalize T.Kf j σ = Kf at h2 h3
  generalize T.V j σ = V at *
  subst e
  cases h5
  exact ⟨Kf, th, hr, h3, h1, h2, h4⟩

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l}

theorem finVol_of_levelLaws {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r} {V : HSp D}
    {dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r} (h : LevelLaws U V dict) : FinVol V :=
  (GlobalTheory.FinalJoin2.volPairEx_and_finVol D V h.sig).2

theorem petProd_smul {σ : c.F →+* ℂ} (U : Unf Xo c σ D.R.r) (V : HSp D)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r) (t : ℝ) (x y : c.F) (f g : Rul Xo c) :
    petProd U V dict t (x • f) (y • g) = starRingEnd ℂ (σ x) * σ y * petProd U V dict t f g := by
  unfold petProd
  simp only [map_smulₛₗ, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [mul_left_comm, ← integral_const_mul (starRingEnd ℂ (σ x) * σ y)]
  congr 2
  funext q
  ring

theorem petProd_conj {σ : c.F →+* ℂ} (U : Unf Xo c σ D.R.r) (V : HSp D)
    (dict : GA D V → Σ k, Frame (U.X k).Ψ D.R.r) (t : ℝ) (f g : Rul Xo c) :
    starRingEnd ℂ (petProd U V dict t f g) = petProd U V dict t g f := by
  unfold petProd
  have key : ∀ (s : ℝ) (F G : AutQ V → ℂ),
      starRingEnd ℂ ((s : ℂ) * ∫ q, starRingEnd ℂ (F q) * G q ∂(muQ1 V)) =
        (s : ℂ) * ∫ q, starRingEnd ℂ (G q) * F q ∂(muQ1 V) := fun s F G => by
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    refine congrArg _ (congrArg _ (funext fun q => ?_))
    rw [map_mul, Complex.conj_conj, mul_comm]
  exact key _ _ _

theorem gramAt_smul (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (V : HSp D)
    (dict : ∀ σ : c.F →+* ℂ, GA D V → Σ k, Frame ((U σ).X k).Ψ D.R.r) (t : ℝ) {N : ℕ} (b : Fin N → Rul Xo c)
    (x : Fin N → c.F) (b' : Fin N → Rul Xo c) (hb : ∀ k, b' k = x k • b k) (σ : c.F →+* ℂ) (i j : Fin N) :
    gramAt U V dict t b' σ i j = starRingEnd ℂ (σ (x i)) * σ (x j) * gramAt U V dict t b σ i j := by
  have key : ∀ (s : c.F →+* ℂ) (i j : Fin N), petProd (U s) V (dict s) t (b' i) (b' j) =
      starRingEnd ℂ (s (x i)) * s (x j) * petProd (U s) V (dict s) t (b i) (b j) := fun s i j => by
    rw [hb i, hb j]
    exact petProd_smul (U s) V (dict s) t (x i) (x j) (b i) (b j)
  by_cases h : GoodEmb c σ
  · simp only [gramAt, if_pos h, Matrix.of_apply]
    exact key σ i j
  · simp only [gramAt, if_neg h, Matrix.of_apply, Matrix.transpose_apply]
    rw [key, RingHom.comp_apply, RingHom.comp_apply, Complex.conj_conj, mul_comm (σ (x j))]

theorem exists_sizeRows (D : D7) (M : ℕ) (S : ℝ) (hf : 16 ≤ D.R.f) (hS : 1 ≤ S) : ∃ L : ℝ, SizeRows D M S L := by
  have hf' : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  refine ⟨2 + |Real.log D.R.r| + |Real.log D.R.f| + |Real.log (dE D.host.E)| +
    |Real.log (Ideal.absNorm D.host.ccK)| + |Real.log M| + |Real.log S|, ?_⟩
  have a1 := le_abs_self (Real.log D.R.r)
  have a2 := le_abs_self (Real.log D.R.f)
  have a3 := le_abs_self (Real.log (dE D.host.E))
  have a4 := le_abs_self (Real.log (Ideal.absNorm D.host.ccK))
  have a5 := le_abs_self (Real.log M)
  have a6 := le_abs_self (Real.log S)
  have b1 := abs_nonneg (Real.log D.R.r)
  have b2 := abs_nonneg (Real.log D.R.f)
  have b3 := abs_nonneg (Real.log (dE D.host.E))
  have b4 := abs_nonneg (Real.log (Ideal.absNorm D.host.ccK))
  have b5 := abs_nonneg (Real.log M)
  have b6 := abs_nonneg (Real.log S)
  refine ⟨hf, by linarith, hS, by linarith, by linarith, ?_, by linarith, by linarith, by linarith⟩
  nlinarith

end GlobalTheory.CompanionTheory.Ar.abelian₂.LevelModel
