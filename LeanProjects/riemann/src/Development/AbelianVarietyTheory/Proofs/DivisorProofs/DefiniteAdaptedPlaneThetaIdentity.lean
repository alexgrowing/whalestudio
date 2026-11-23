import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedAdaptedPlaneVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolDataAlmostAllPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryGroupSurjectsGeneralLinearRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactConjugateExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryIntertwinesStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.ThKLiftGoodSmall

open GlobalTheory.ThKLiftGood GlobalTheory.KSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem locOps (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (v : Pl F) (hv : X.Good v) :
    ∃ (ν₀ : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
      (∃ t : E →ₐ[F] Fv F v, ν₀ = (chrW X.ν t)⁻¹) ∧ GlobalTheory.SmGL.IsSmoothChar ν₀ ∧ GlobalTheory.SmGL.IsUnitaryChar ν₀ ∧
      Set.BijOn ι (SB (Fin a' × Fin (a + a') → Fv F v) : Set _) (SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) : Set _) ∧
      (∀ g ∈ UAt σ G.V' (evFin F v), ∃ g' : GL (Fin a') (Fv F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ →
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) ∧
      (∀ g' : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧
          ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) ∧
      ∀ h' : GL (Fin (a + a')) (Fv F v), ∃ h ∈ UAt σ G.W (evFin F v), ∃ κ : ℂ, κ ≠ 0 ∧
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = κ • fun Y => ι φ (Y * h'.1) := by
  have hp := GlobalTheory.ThKContSmall.isPair_small hT
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := GlobalTheory.T.split_place_embedding_exists F E σ hT.base.cm v hv.2
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp v t 1 1
  obtain ⟨κW, hW⟩ := GlobalTheory.T.linear_model_unitary_conjugate hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp v t 1 1 ι hι
  obtain ⟨κX, hX⟩ := GlobalTheory.T.linear_model_compact_conjugate_exists hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp v t 1 1 ι hι
  have sX := GlobalTheory.T.linear_model_unitary_intertwines hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp v t 1 1 ι hι κX hX
  obtain ⟨hs, hu⟩ := GlobalTheory.T.local_character_smooth_unitary hP F E σ B a a' G X om om' hT v hv t
  have hloc := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp v).1
  have hV : ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (g, 1)) φ φ₁ →
        ι φ₁ = GlobalTheory.SplitFlip.omA (chrW X.ν t)⁻¹ 1 (locMat t 1 g) 1 (ι φ) := by
    intro g hg φ hφ φ₁ hφ₁ hA
    rw [hX g hg φ hφ φ₁ hφ₁ hA, sX g hg]
    funext Y
    simp [GlobalTheory.SplitFlip.omA, Chars.ν]
  refine ⟨(chrW X.ν t)⁻¹, ι, ⟨t, rfl⟩, GlobalTheory.WeilLinA.isSmoothChar_inv _ hs, GlobalTheory.WeilLinA.isUnitaryChar_inv _ hu, hι.bij,
    fun g hg => ⟨_, hV g hg⟩, fun g' => ?_, fun h' => ?_⟩
  · obtain ⟨K, hK⟩ := GlobalTheory.LeviAtPlace.levi_at_place F E σ B a a' G X om om' hT v hv t
    refine ⟨K g', (hK g').1, fun φ hφ => ?_⟩
    obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc _ (hK g').1 1 (fun u _ => by simp [mat]) φ hφ
    have e1 : locMat t 1 (K g') = g' := Units.ext (by rw [locMat_val, (hK g').2.1]; simp)
    exact ⟨φ₁, hφ₁, hA, by rw [hV _ (hK g').1 φ hφ φ₁ hφ₁ hA, e1]⟩
  · obtain ⟨h, hh, hht⟩ := GlobalTheory.SkewLevi.surj_at_place hP F E σ B a a' G X om om' hT v hv t (GlobalTheory.SplitFlip.invT h')
    have e1 : locMat t 1 h = GlobalTheory.SplitFlip.invT h' := Units.ext (by rw [locMat_val, hht]; simp)
    have key : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ ∧ ι φ₁ = κW h • fun Y => ι φ (Y * h'.1) := fun φ hφ => by
      obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := hloc 1 (fun u _ => by simp [mat]) h hh φ hφ
      exact ⟨φ₁, hφ₁, hA, by rw [hW h hh φ hφ φ₁ hφ₁ hA, e1, GlobalTheory.SplitFlip.invT_invT]⟩
    refine ⟨h, hh, κW h, fun h0 => ?_, key⟩
    have hvac := hT.geo.hM'.vac v
    obtain ⟨φ₁, hφ₁, hA, e⟩ := key _ hvac.1
    rw [h0, zero_smul, ← map_zero ι] at e
    obtain rfl : φ₁ = 0 := hι.bij.injOn hφ₁ (Submodule.zero_mem _) e
    obtain ⟨Rw, hRw0, hRw⟩ := GlobalTheory.RestWitness.exists_rest (Fin a' × Fin (a + a')) v
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) Rw = 0 := funext fun _ => zero_mul _
    have e2 := congrArg (om' (1, h)⁻¹) (hA Rw (hRw _ hvac.1))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, e0, map_zero, ← e0] at e2
    exact hvac.2.1 (GlobalTheory.InertAvgDual.eq_of_tens_eq v hRw0 (hRw _ hvac.1).1 e2)

open scoped Classical in

private theorem lift_right_inv' (hK : KP) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'} (hM : IsMatched B G X om om' R Rf)
    (c : ℂ) {Φ} (hP : Φ ∈ PolData B G.M) {Φ'} (hP' : Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C)
    (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ) :
    ∃ S : Finset (Pl F), ∀ v : Pl F, X.Good v → v ∉ S → ∀ Φ₁ ∈ PolData B G.M', ∀ x ∈ UAt σ G.V' (evFin F v), ∀ g : UA σ G.V'.J,
      GlobalTheory.ThKLiftConst.lift om' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) Φ₁ μ 𝓕 (g * x) =
        GlobalTheory.ThKLiftConst.lift om' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) Φ₁ μ 𝓕 g := by
  have hT := hM.triple
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  have hPV := GlobalTheory.ThKContSmall.isPair_small hT
  have hθ := (GlobalTheory.T.theta_basic_properties hK.base F E σ B _ _ _ _ G.M' _ _ om' _ _ _ _ hPV).1
  obtain ⟨-, hlc, hsc, ht2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : Countable (ratU σ G.W.J) := (GlobalTheory.T.rational_unitary_countable_discrete F E σ _ G.W.J).1
  obtain ⟨c₀, hc₀, hJ⟩ := GlobalTheory.SkewToHerm.skew_to_hermND F E σ hT.base.cm B _ G.W _ _ hT.geo.hW
  have h𝓕fin : μ 𝓕 < ⊤ :=
    GlobalTheory.ThKContSmall.measure_fundamental_domain_lt_top hK.siegelSetUnitary hT.base.cm hJ _ (GlobalTheory.SiegelSet.ug_eq_hr hσ hc₀) μ hμ 𝓕 h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕fin.ne
  have hpres : ∀ z, ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), om' z Ψ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun z Ψ hΨ => hT.weil'.isUSplitting.pres z Ψ hΨ
  obtain ⟨l, -, hl⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin a' × Fin (a + a'))
  have hθl : ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), ∀ g h, theta om' Ψ g h = l (om' (g, h) Ψ) :=
    fun Ψ hΨ g h => (hl _ (hpres _ _ hΨ)).symm
  set f : UA σ G.W.J → ℂ := fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h with hf
  obtain ⟨hc1, hi1⟩ := GlobalTheory.T.continuous_left_invariant_theta hK F E σ B a a' G X om om' hT Φ hP
  obtain ⟨hc2, hi2⟩ := GlobalTheory.T.continuous_left_invariant_dual hK F E σ B a a' G X om om' hT Φ' hP'
  have hθinv : ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), ∀ g, ∀ γ ∈ ratU σ G.W.J, ∀ h,
      theta om' Ψ g (γ * h) = theta om' Ψ g h := fun Ψ hΨ g γ hγ h => by
    simpa using (hθ Ψ hΨ).2.1 1 (one_mem _) γ hγ g h

  have hfN : f ∈ Nice om' μ 𝓕 := by
    refine ⟨fun γ hγ h => by simp only [hf, hi1 γ hγ, hi2 γ hγ], fun Ψ hΨ g => ?_⟩
    obtain ⟨hc, -, C, k, hCk⟩ := hθ Ψ hΨ
    obtain ⟨D, hD⟩ := hdec k
    have hcf : Continuous fun h => f h * (starRingEnd ℂ) (theta om' Ψ g h) :=
      (hc1.sub (continuous_const.mul hc2)).mul
        (Complex.continuous_conj.comp (hc.comp (Continuous.prodMk_right g)))
    have hC0 : 0 ≤ max C 0 * (ht g : ℝ) ^ k := by positivity
    refine Integrable.of_bound hcf.aestronglyMeasurable (max C 0 * (ht g : ℝ) ^ k * D) (.of_forall fun h => ?_)
    have hb : ‖theta om' Ψ g h‖ ≤ max C 0 * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k := by
      refine GlobalTheory.ThKSwapV.le_mul_qht_pow h k hC0 fun γ => ?_
      rw [← hθinv Ψ hΨ g γ.1 γ.2 h, mul_assoc, ← mul_pow]
      exact (hCk g _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [norm_mul, RCLike.norm_conj]
    calc ‖f h‖ * ‖theta om' Ψ g h‖ ≤ ‖f h‖ * (max C 0 * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = max C 0 * (ht g : ℝ) ^ k * (‖f h‖ * (qht h : ℝ) ^ k) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hD h) hC0
  have hinvP : ∀ u ∈ Nice om' μ 𝓕, ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), ∀ g, ∀ γ ∈ ratU σ G.W.J, ∀ h,
      u (γ * h) * (starRingEnd ℂ) (theta om' Ψ g (γ * h)) = u h * (starRingEnd ℂ) (theta om' Ψ g h) :=
    fun u hu Ψ hΨ g γ hγ h => by rw [hu.1 γ hγ, hθinv Ψ hΨ g γ hγ]
  have htr : ∀ y : UA σ G.W.J, (fun h => f (h * y)) ∈ Nice om' μ 𝓕 := by
    intro y
    refine ⟨fun γ hγ h => by simp only [mul_assoc, hfN.1 γ hγ], fun Ψ hΨ g => ?_⟩
    obtain ⟨m, -, hm⟩ := quasi μ (ratU σ G.W.J) h𝓕 y
    have h1 := hpres (1, y⁻¹) Ψ hΨ
    have := (hm _ (hinvP f hfN _ h1 g)).1 (hfN.2 _ h1 g)
    simpa only [theta_right, mul_inv_cancel_right] using this
  obtain ⟨S, hS⟩ := GlobalTheory.ThK.TMapGood.exists_tmap hK F E σ B a a' G X om om' R Rf hM c Φ hP Φ' hP'
  refine ⟨S, fun v hv hvS Φ₁ hΦ₁ x hx g => ?_⟩
  obtain ⟨T, hT1, hT2, hT3⟩ := hS v hvS
  have hT3' : ∀ y ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, y)) φ φ₁ →
      ∀ h, T (Rf.p' v φ₁) h = T (Rf.p' v φ) (h * y) := by
    intro y hy φ' hφ' φ₁' hφ₁' ha h
    obtain ⟨φ, hφ, e⟩ : Rf.p' v φ' ∈ (SB _).map (Rf.p v) := hM.fin.onto v ▸ Submodule.mem_top
    obtain ⟨φ₁, ⟨hφ₁, ha₁⟩, -⟩ := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _
      (GlobalTheory.ThKContSmall.isPair_big hT) v).1 1 (fun u _ => by simp [mat]) y hy φ hφ
    rw [← hM.fin.equiv v y hy φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' ha₁ ha e, ← e]
    exact hT3 y hy φ hφ φ₁ hφ₁ ha₁ h
  rw [(hM.fin.sph v hv.1).1] at hT1
  have hTN : ∀ ξ, T ξ ∈ Nice om' μ 𝓕 := fun ξ =>
    (Submodule.span_le.2 (by rintro _ ⟨y, -, rfl⟩; exact htr y) : _ ≤ Nice om' μ 𝓕) (hT2 ξ)

  have hadd : ∀ u ∈ Nice om' μ 𝓕, ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), ∀ Ψ' ∈ schA F (Fin a' × Fin (a + a')), ∀ g,
      GlobalTheory.ThKLiftConst.lift om' u (Ψ + Ψ') μ 𝓕 g =
        GlobalTheory.ThKLiftConst.lift om' u Ψ μ 𝓕 g + GlobalTheory.ThKLiftConst.lift om' u Ψ' μ 𝓕 g := by
    intro u hu Ψ hΨ Ψ' hΨ' g
    simp only [GlobalTheory.ThKLiftConst.lift_apply]
    rw [← integral_add (hu.2 Ψ hΨ g) (hu.2 Ψ' hΨ' g)]
    simp only [hθl _ (add_mem hΨ hΨ'), hθl _ hΨ, hθl _ hΨ', map_add, mul_add]
  have hsmul : ∀ (u : UA σ G.W.J → ℂ) (t : ℂ), ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), ∀ g,
      GlobalTheory.ThKLiftConst.lift om' u (t • Ψ) μ 𝓕 g = (starRingEnd ℂ) t * GlobalTheory.ThKLiftConst.lift om' u Ψ μ 𝓕 g := by
    intro u t Ψ hΨ g
    simp only [GlobalTheory.ThKLiftConst.lift_apply]
    rw [← integral_const_mul]
    simp only [hθl _ (Submodule.smul_mem _ t hΨ), hθl _ hΨ, map_smul, smul_eq_mul, map_mul]
    congr 1; funext h; ring
  have hsch := GlobalTheory.ThKRatInv.polData_le_schA B G.M' hT.geo.hM'
  induction hΦ₁ using Submodule.span_induction with
  | zero => simp [GlobalTheory.ThKLiftConst.lift_apply, hθl _ (Submodule.zero_mem _)]
  | add Ψ Ψ' h1 h2 e1 e2 => rw [hadd f hfN _ (hsch h1) _ (hsch h2), hadd f hfN _ (hsch h1) _ (hsch h2), e1, e2]
  | smul t Ψ h1 e1 => rw [hsmul f t _ (hsch h1), hsmul f t _ (hsch h1), e1]
  | mem Ψ hΨ =>
  obtain ⟨f₁, -, φ, hφ1, hφ2, rfl⟩ := hΨ
  have hfam : GlobalTheory.BigNZ.Fam G.M' φ := ⟨hφ1, hφ2⟩
  obtain ⟨r, hr, er⟩ := GlobalTheory.PureFactor.exists_rest_factor v f₁ φ (hfam.std hT.geo.hM')
  have hrs : ∀ χ ∈ SB (Fin a' × Fin (a + a') → Fv F v), tens (evFin F v) χ r ∈ schA F (Fin a' × Fin (a + a')) :=
    fun χ hχ => by rw [er]; exact (hfam.update v hχ).mem hT.geo.hM' f₁
  have hact : ∀ {Op χ χ₁}, χ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Acts (evFin F v) Op χ χ₁ →
      Op (tens (evFin F v) χ r) = tens (evFin F v) χ₁ r := fun hχ ha => ha r ⟨hr, hrs _ hχ⟩

  let B0 : SB (Fin a' × Fin (a + a') → Fv F v) →ₗ[ℂ] SB (Fin a' × Fin (a + a') → Fv F v) →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun χ₁ χ₂ => GlobalTheory.ThKLiftConst.lift om' (T (Rf.p' v χ₁.1)) (tens (evFin F v) χ₂.1 r) μ 𝓕 g)
      (fun χ₁ χ₁' χ₂ => by
        simp only [GlobalTheory.ThKLiftConst.lift_apply]
        rw [← integral_add ((hTN _).2 _ (hrs _ χ₂.2) g) ((hTN _).2 _ (hrs _ χ₂.2) g)]
        simp only [Submodule.coe_add, map_add, Pi.add_apply, add_mul])
      (fun t χ₁ χ₂ => by
        simp only [GlobalTheory.ThKLiftConst.lift_apply, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
      (fun χ₁ χ₂ χ₂' => by
        rw [← hadd _ (hTN _) _ (hrs _ χ₂.2) _ (hrs _ χ₂'.2)]
        congr 1
        exact funext fun _ => add_mul _ _ _)
      (fun t χ₁ χ₂ => by
        rw [smul_eq_mul, ← hsmul _ t _ (hrs _ χ₂.2)]
        congr 1
        exact funext fun _ => mul_assoc _ _ _)
  have hB0 : ∀ χ₁ χ₂, B0 χ₁ χ₂ =
      GlobalTheory.ThKLiftConst.lift om' (T (Rf.p' v χ₁.1)) (tens (evFin F v) χ₂.1 r) μ 𝓕 g := fun _ _ => rfl
  obtain ⟨ν₀, ι, ⟨t, ht⟩, s1, u1, hbij, hg1, hg2, hh⟩ := locOps hK.base hT v hv
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hν : ∀ m : ℕ, 0 < m → ∀ s : ℝ, ((ν₀ (unifAt v) : ℂ)) ^ m ≠ (s : ℂ) := by
    intro m hm s hs
    have hn : |s| = 1 := by
      have := congrArg (fun z : ℂ => ‖z‖) hs
      simp only [norm_pow, u1 (unifAt v), one_pow, Complex.norm_real, Real.norm_eq_abs] at this
      exact this.symm
    have h2 : ν₀ (unifAt v) ^ (m * 2) = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, pow_mul, hs, ← Complex.ofReal_pow, ← sq_abs, hn]
      simp
    have h3 := GlobalTheory.NuGood.not_root_of_unity F E σ B a a' G X om om' hT v hv t ((m * 2 : ℕ) : ℤ) (by omega)
    rw [zpow_natCast] at h3
    subst ht
    exact h3 (by simpa using h2)
  let e : SB (Fin a' × Fin (a + a') → Fv F v) ≃ₗ[ℂ] SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) :=
    LinearEquiv.ofBijective (ι.restrict fun χ hχ => hbij.mapsTo hχ)
      ⟨fun χ χ' h => Subtype.ext (hbij.injOn χ.2 χ'.2 (congrArg Subtype.val h)), fun Ψ => by
        obtain ⟨χ, hχ, h⟩ := hbij.surjOn Ψ.2
        exact ⟨⟨χ, hχ⟩, Subtype.ext h⟩⟩
  have he : ∀ χ, (e χ).1 = ι χ.1 := fun _ => rfl
  have he' : ∀ Ψ, ι (e.symm Ψ).1 = Ψ.1 := fun Ψ => by rw [← he, LinearEquiv.apply_symm_apply]
  let Bf : SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) →ₗ[ℂ] SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) →ₗ⋆[ℂ] ℂ :=
    (B0.comp e.symm.toLinearMap).compl₂ e.symm.toLinearMap
  have hBf : ∀ Ψ₁ Ψ₂, Bf Ψ₁ Ψ₂ = B0 (e.symm Ψ₁) (e.symm Ψ₂) := fun _ _ => rfl
  have hlt : a' < a + a' := by have := hT.geo.lt; omega
  have key := GlobalTheory.SBFormInv.form_lact_right hK (Fv F v) a' (a + a') ν₀ (unifAt v) hlt hϖ s1 u1 hν Bf
    (fun g' Ψ₁ Ψ₁' Ψ₂ h => by
      obtain ⟨x', hx', H⟩ := hg2 (GlobalTheory.SplitFlip.invT g')
      obtain ⟨χ₁, hχ₁, ha, hι⟩ := H _ (e.symm Ψ₁).2
      rw [omA_left, GlobalTheory.SplitFlip.invT_invT, he', ← h, ← he'] at hι
      have e1 := hbij.injOn hχ₁ (e.symm Ψ₁').2 hι
      have e2 : Rf.p' v (χ₁ - (e.symm Ψ₁).1) = 0 :=
        hM.fin.inv' v (Submodule.subset_span ⟨x', hx', _, (e.symm Ψ₁).2, χ₁, hχ₁, ha, rfl⟩)
      rw [map_sub, sub_eq_zero, e1] at e2
      rw [hBf, hBf, hB0, hB0, e2])
    (fun h => by
      obtain ⟨y, hy, κ, hκ, H⟩ := hh h
      obtain ⟨m, hm0, hm⟩ := quasi μ (ratU σ G.W.J) h𝓕 y
      refine ⟨m * Complex.normSq κ, mul_pos hm0 (Complex.normSq_pos.2 hκ), fun Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2 => ?_⟩
      have loc : ∀ Ψ Ψ' : SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)), (Ψ'.1 = fun Y => Ψ.1 (Y * h.1)) →
          Acts (evFin F v) (om' (1, y)) (e.symm Ψ).1 (κ • e.symm Ψ').1 := fun Ψ Ψ' h0 => by
        obtain ⟨χ₁, hχ₁, ha, hι⟩ := H _ (e.symm Ψ).2
        rw [he', ← h0, ← he', ← map_smul] at hι
        rw [← hbij.injOn hχ₁ (κ • e.symm Ψ').2 hι]
        exact ha
      have e1 : B0 (κ • e.symm Ψ₁') (κ • e.symm Ψ₂') = Complex.normSq κ * Bf Ψ₁' Ψ₂' := by
        rw [hBf, B0.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          Complex.mul_conj]
      rw [Complex.ofReal_mul, mul_assoc, ← e1, hBf, hB0, hB0, ← hact (e.symm Ψ₂).2 (loc Ψ₂ Ψ₂' h2)]
      simp only [GlobalTheory.ThKLiftConst.lift_apply, theta_right,
        hT3' y hy _ (e.symm Ψ₁).2 _ (κ • e.symm Ψ₁').2 (loc Ψ₁ Ψ₁' h1)]
      exact (hm (fun z => T (Rf.p' v (e.symm Ψ₁).1) z * (starRingEnd ℂ) (theta om' (tens (evFin F v) (e.symm Ψ₂).1 r) g z))
        (hinvP _ (hTN _) _ (hrs _ (e.symm Ψ₂).2) g)).2)
  obtain ⟨χ₁, ⟨hχ₁, ha⟩, -⟩ := (GlobalTheory.T.theta_action_exists hK.base F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hPV v).1 x hx 1
    (fun u _ => by simp [mat]) (φ v) (hφ1 v)
  obtain ⟨g', H⟩ := hg1 x hx
  have hvac := (hT.geo.hM'.vac v).1
  have := key (GlobalTheory.SplitFlip.invT g') (e ⟨_, hvac⟩) (e ⟨_, hφ1 v⟩) (e ⟨_, hχ₁⟩)
    (by rw [he, he, ← omA_left]; exact H _ (hφ1 v) _ hχ₁ ha)
  simp only [hBf, LinearEquiv.symm_apply_apply, hB0, hT1] at this
  rw [← hact (hφ1 v) ha, er, Function.update_eq_self] at this
  simpa only [GlobalTheory.ThKLiftConst.lift_apply, theta_left] using this

end GlobalTheory.ThKLiftGoodSmall

end

theorem _root_.GlobalTheory.T.definite_adapted_plane_theta_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ c : ℂ,
      (∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ fa fb fa' fb', Split2 W₁ H' X (G.M.I om Φ) fa fb →
        Split2 W₁ H' X (G.M'.I om' Φ') fa' fb' → fa = c • fa' ∧ fb = c • fb') →
      ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' →
      IsCT H' (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) 0 →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖G.M.I om Φ h - c * G.M'.I om' Φ' h‖ * (qht h : ℝ) ^ N ≤ C) →
      ∀ Φ₁, ∀ Φ₁' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ₁ Φ₁' →
      ∀ (μ : Measure (UA σ G.W.J)) (𝓕 : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) 𝓕 μ →
        ∃ T : Finset (Pl F), ∀ v : Pl F, v ∉ T → SplitsFully E v → ∀ g, ∀ k ∈ UAt σ G.V' (evFin F v), thLift om' Φ₁' μ 𝓕 (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) (g * k) = thLift om' Φ₁' μ 𝓕 (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) g := by
  classical
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM _ _ d₁ W₁ H' i₀ i₁ _ c _ Φ Φ' hΦ' hPM _ hdec Φ₁ Φ₁' _ hPM₁ μ 𝓕 hμ h𝓕
  obtain ⟨hP, hP'⟩ := GlobalTheory.ThKSelfOrth.polData_of_polMatch hPM
  obtain ⟨S, hS⟩ := GlobalTheory.ThKLiftGoodSmall.lift_right_inv' hK hM c hP ⟨hP', hΦ'⟩ hdec μ 𝓕 hμ h𝓕
  refine ⟨S ∪ X.T, fun v hv hsp g k hk => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  exact hS v ⟨hv.2, hsp⟩ hv.1 Φ₁' (GlobalTheory.ThKSelfOrth.polData_of_polMatch hPM₁).2 k hk g
