import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfIsIntegralMulOfSmall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFrameWeightRatioBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicFrameBlockZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteAdelicDenominatorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameBlockZeroStabilizesFlagStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdeleSplitSndDiagonal

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.FlagKey

variable {r : ℕ}

theorem exists_embOver (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : E →+* ℂ) : ∃ (w : InfinitePlace F) (τ : EmbOver E w), τ.1 = φ := by
  haveI := h.1
  let ψ : F →+* ℂ := φ.comp (algebraMap F E)
  let w : InfinitePlace F := InfinitePlace.mk ψ
  have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal w)
  have e : ψ = w.embedding := by
    rcases InfinitePlace.embedding_mk_eq ψ with e | e
    · exact e.symm
    · have h2 : ComplexEmbedding.conjugate w.embedding = w.embedding := ComplexEmbedding.isReal_iff.1 hr
      rw [← h2]
      change ψ = ComplexEmbedding.conjugate (InfinitePlace.mk ψ).embedding
      rw [e]
      exact RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
  exact ⟨w, ⟨φ, e⟩, rfl⟩

theorem archMat_ratEmb {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F} (τ : EmbOver E w) (γ : GRat σ J) :
    archMat σ J τ (projArch σ J w (ratEmb σ J γ)) = γ.1.1.map τ.1 := by
  rw [projArch_ratEmb]
  ext i j
  change infEmb τ ((1 : w.Completion) ⊗ₜ[F] (γ.1.1 i j)) = _
  simp

theorem gram_YX {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E} (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (hW : IsWittFrame σ J X Y) : cT (σ : E →+* E) Y * J * X = 1 :=
  PFr.yx (s := (σ : E →+* E)) ⟨fun x => sigma_sigma h x, Matrix.ext fun i j => hJ.1 i j, hW.xx, hW.yy, hW.xy⟩

theorem exists_denom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ι : Type) [Finite ι] (P : ι → Matrix (Fin n) (Fin n) E) (Ω C : Set (GAd σ J)), IsCompact Ω → IsCompact C → ∃ d : ℕ, 0 < d ∧ ∀ p ∈ Ω, ∀ a ∈ infPts σ J, ∀ m ∈ C, ∀ γ : GRat σ J, ratEmb σ J γ = p * a * m * a⁻¹ * p⁻¹ → ∀ (α β : ι) (u v : Fin n), IsIntegral ℤ ((d : E) * (P α * γ.1.1 * P β) u v) := by
  intro F E _ _ _ _ _ σ n J ι _ P Ω C hΩ hC
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := Af F)
  let Cf : Set (GFin σ J) := (fun q : GAd σ J × GAd σ J => projFin σ J (q.1 * q.2 * q.1⁻¹)) '' (Ω ×ˢ C)
  have hCf : IsCompact Cf := (hΩ.prod hC).image
    ((continuous_projFin σ J).comp ((continuous_fst.mul continuous_snd).mul continuous_fst.inv))
  let f : ι × ι × Fin n × Fin n → GFin σ J → Af F ⊗[F] E := fun q g =>
    ((P q.1).map (inclR (F := F) (Af F)) * (matHom (Af F) σ J g).1 * (P q.2.1).map (inclR (F := F) (Af F))) q.2.2.1 q.2.2.2
  have hcont : Continuous fun g : GFin σ J => (matHom (Af F) σ J g).1 :=
    Units.continuous_val.comp (isEmbedding_matHom (Af F) σ J).continuous
  have hf : ∀ q, Continuous (f q) := fun q =>
    ((continuous_const.matrix_mul hcont).matrix_mul continuous_const).matrix_elem _ _
  obtain ⟨d, hd, h⟩ := GlobalTheory.T.compact_finite_adelic_denominator F E (⋃ q, f q '' Cf) (isCompact_iUnion fun q => hCf.image (hf q))
  refine ⟨d, hd, fun p hp a ha m hm γ hγ α β u v => h _ (Set.mem_iUnion.2 ⟨(α, β, u, v), projFin σ J (ratEmb σ J γ), ⟨(p, m), ⟨hp, hm⟩, ?_⟩, ?_⟩)⟩
  · have ha' : projFin σ J a = 1 := mem_infPts.1 ha
    simp only [hγ, map_mul, map_inv, ha', mul_one, one_mul, inv_one]
  · have e : (matHom (Af F) σ J (projFin σ J (ratEmb σ J γ))).1 = γ.1.1.map (inclR (F := F) (Af F)) :=
      congrArg Units.val (GlobalTheory.CompanionTheory.ClassFin.projFin_ratEmb_val σ J γ)
    simp only [f, e]
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    rfl

theorem frameLev_le (s : Fin r) (α : FrameIx r) : frameLev s α ≤ 2 := by
  rcases α with _ | i | i
  · simp [frameLev]
  · simp only [frameLev]; split_ifs <;> omega
  · simp only [frameLev]; split_ifs <;> omega

theorem block_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∀ c : ℝ, 0 < c → ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ m ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r) (α β : FrameIx r), frameLev s α < 2 → frameLev s β = 2 → ∀ u v : Fin n, ‖((frameIdem (σ : E →+* E) J X Y α).map τ.1 * archMat σ J τ (projArch σ J w (p * a * m * a⁻¹ * p⁻¹)) * (frameIdem (σ : E →+* E) J X Y β).map τ.1) u v‖ ≤ B / ratio t s := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW Ω C hΩ hΩP hC c hc
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.cone_frame_weight_ratio_bound r c hc
  have hb : ∀ q : (Σ w : InfinitePlace F, EmbOver E w) × FrameIx r × FrameIx r × FrameIx r × FrameIx r × Fin n × Fin n,
      ∃ B : ℝ, ∀ x ∈ Ω ×ˢ C,
      ‖((frameIdem (σ : E →+* E) J X Y q.2.1).map q.1.2.1 * archMat σ J q.1.2 (projArch σ J q.1.1 x.1) *
        (frameIdem (σ : E →+* E) J X Y q.2.2.1).map q.1.2.1 * archMat σ J q.1.2 (projArch σ J q.1.1 x.2) *
        (frameIdem (σ : E →+* E) J X Y q.2.2.2.1).map q.1.2.1 * archMat σ J q.1.2 (projArch σ J q.1.1 x.1⁻¹) *
        (frameIdem (σ : E →+* E) J X Y q.2.2.2.2.1).map q.1.2.1) q.2.2.2.2.2.1 q.2.2.2.2.2.2‖ ≤ B := fun q => by
    have hcont : Continuous fun g : GAd σ J => archMat σ J q.1.2 (projArch σ J q.1.1 g) :=
      (GlobalTheory.Orb.continuous_archMat σ J q.1.2).comp (continuous_projArch σ J q.1.1)
    refine (hΩ.prod hC).exists_bound_of_continuousOn (Continuous.continuousOn ?_)
    exact (((((((continuous_const.matrix_mul (hcont.comp continuous_fst)).matrix_mul continuous_const).matrix_mul
      (hcont.comp continuous_snd)).matrix_mul continuous_const).matrix_mul
      (hcont.comp continuous_fst.inv)).matrix_mul continuous_const)).matrix_elem _ _
  choose B hB using hb
  set Bt : ℝ := ∑ q, |B q| with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(Fintype.card (FrameIx r) : ℝ) * ((Fintype.card (FrameIx r) : ℝ) * (K * Bt)), by positivity, ?_⟩
  intro p hp t ht a ha m hm w τ s α β hα hβ u v
  have hr : 0 < ratio t s := ratio_pos ht s
  have hd : ∀ α, 0 < frameWt t α := frameWt_pos ht.1
  set A := archMat σ J τ (projArch σ J w a) with hAdef
  set A' := archMat σ J τ (projArch σ J w a⁻¹) with hA'def
  set G := archMat σ J τ (projArch σ J w p) with hGdef
  set G' := archMat σ J τ (projArch σ J w p⁻¹) with hG'def
  set M₁ := archMat σ J τ (projArch σ J w m) with hM₁
  set P : FrameIx r → Matrix (Fin n) (Fin n) ℂ := fun α => (frameIdem (σ : E →+* E) J X Y α).map τ.1 with hPdef
  have hAA : A' * A = 1 := by
    rw [hAdef, hA'def, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have e2 : archMat σ J τ (projArch σ J w (p * a * m * a⁻¹ * p⁻¹)) = G * A * M₁ * A' * G' := by
    simp only [map_mul, hAdef, hA'def, hGdef, hG'def, hM₁]
  have hP : ∑ α, P α = 1 := by
    have : ∑ α, P α = (τ.1.mapMatrix) (∑ α, frameIdem (σ : E →+* E) J X Y α) := by
      rw [map_sum]; rfl
    rw [this, sum_frameIdem, map_one]
  have hTor : ∀ β, A * P β = ((frameWt t β : ℝ) : ℂ) • P β := fun β =>
    GlobalTheory.T.torus_archimedean_frame_action F E σ h n J hJ r X Y hW t a ha ht.1 w τ β
  have hA : A = ∑ β, ((frameWt t β : ℝ) : ℂ) • P β := by
    calc A = A * ∑ β, P β := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun β _ => hTor β
  have hTor' : ∀ α, A' * P α = ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := fun α => by
    have hne : ((frameWt t α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hd α).ne'
    rw [eq_inv_smul_iff₀ hne, ← Matrix.mul_smul, ← hTor α, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have hA' : A' = ∑ α, ((frameWt t α : ℝ) : ℂ)⁻¹ • P α := by
    calc A' = A' * ∑ α, P α := by rw [hP, Matrix.mul_one]
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => hTor' α
  have e3 : P α * (G * A * M₁ * A' * G') * P β =
      ∑ α', ∑ β', (((frameWt t α' : ℝ) : ℂ) * ((frameWt t β' : ℝ) : ℂ)⁻¹) •
        (P α * G * P α' * M₁ * P β' * G' * P β) := by
    conv_lhs => rw [hA', hA]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun β' _ => ?_
    rw [mul_comm]
  have hp' : p ∈ minPar σ J X := minParOne_sub (hΩP hp)
  have hp'' : p⁻¹ ∈ minPar σ J X := inv_mem_minPar h hJ hW hp'
  have term : ∀ α' β', ‖((((frameWt t α' : ℝ) : ℂ) * ((frameWt t β' : ℝ) : ℂ)⁻¹) •
      (P α * G * P α' * M₁ * P β' * G' * P β)) u v‖ ≤ K * Bt / ratio t s := fun α' β' => by
    have hnn : 0 ≤ K * Bt / ratio t s := div_nonneg (mul_nonneg hK0 hBt0) hr.le
    by_cases h1 : frameLev s α' = 2
    · have h0 : P α * G * P α' = 0 := GlobalTheory.T.minimal_parabolic_frame_block_zero F E σ h n J hJ r X Y hW p hp' w τ s α α' hα h1
      simpa [h0] using hnn
    by_cases h2 : frameLev s β' = 2
    · have h3 : frameLev s α' < frameLev s β' := by
        have := frameLev_le s α'
        omega
      have h4 := hK s t ht β' α' h3
      have h5 : ‖(P α * G * P α' * M₁ * P β' * G' * P β) u v‖ ≤ Bt :=
        ((hB (⟨w, τ⟩, α, α', β', β, u, v) (p, m) ⟨hp, hm⟩).trans (le_abs_self _)).trans
          (Finset.single_le_sum (f := fun q => |B q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))
      have h6 : ‖((frameWt t α' : ℝ) : ℂ) * ((frameWt t β' : ℝ) : ℂ)⁻¹‖ = frameWt t α' / frameWt t β' := by
        rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hd α').le,
          Real.norm_of_nonneg (hd β').le, div_eq_mul_inv]
      rw [Matrix.smul_apply, norm_smul, h6]
      calc _ ≤ K / ratio t s * Bt := mul_le_mul h4 h5 (norm_nonneg _) (div_nonneg hK0 hr.le)
        _ = _ := by ring
    · have h3 : frameLev s β' < 2 := lt_of_le_of_ne (frameLev_le s β') h2
      have h0 : P β' * G' * P β = 0 := GlobalTheory.T.minimal_parabolic_frame_block_zero F E σ h n J hJ r X Y hW p⁻¹ hp'' w τ s β' β h3 hβ
      have h7 : P α * G * P α' * M₁ * P β' * G' * P β = 0 := by
        simp only [Matrix.mul_assoc] at h0 ⊢
        simp [h0]
      simpa [h7] using hnn
  rw [e2]
  change ‖(P α * (G * A * M₁ * A' * G') * P β) u v‖ ≤ _
  rw [e3, Matrix.sum_apply]
  calc _ ≤ ∑ α' : FrameIx r, ‖(∑ β', (((frameWt t α' : ℝ) : ℂ) * ((frameWt t β' : ℝ) : ℂ)⁻¹) •
        (P α * G * P α' * M₁ * P β' * G' * P β)) u v‖ := norm_sum_le _ _
    _ ≤ ∑ α' : FrameIx r, ∑ β' : FrameIx r, K * Bt / ratio t s := Finset.sum_le_sum fun α' _ => by
        rw [Matrix.sum_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun β' _ => term α' β')
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem flag_key : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → ∀ (K : Subgroup (GAd σ J)), IsCompact (K : Set (GAd σ J)) → ∀ c : ℝ, 0 < c → ∀ (C : Set (GAd σ J)), IsCompact C → ∃ t1 : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, ∀ γ : GRat σ J, (p * a * k)⁻¹ * ratEmb σ J γ * (p * a * k) ∈ C → ∀ j : Fin r, t1 < t j → (∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j) → (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y hW Ω hΩ hΩP K hK c hc C hC
  haveI := hcm.1
  let C' : Set (GAd σ J) := (fun q : GAd σ J × GAd σ J × GAd σ J => q.1 * q.2.1 * q.2.2) '' ((K : Set (GAd σ J)) ×ˢ C ×ˢ (K : Set (GAd σ J)))
  have hC' : IsCompact C' := (hK.prod (hC.prod hK)).image (by fun_prop)
  obtain ⟨B, hB0, hB⟩ := block_bound F E σ hcm n J hJ r X Y hW Ω C' hΩ hΩP hC' c hc
  obtain ⟨d, hd, hint⟩ := exists_denom F E σ n J (FrameIx r) (frameIdem (σ : E →+* E) J X Y) Ω C' hΩ hC'
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨2 * d * B + 1, fun p hp t ht a ha k hk γ hγ j hj1 hj2 l hl => ?_⟩
  have hT : 0 < 2 * (d : ℝ) * B + 1 := by positivity
  have hrat : 2 * (d : ℝ) * B + 1 < ratio t j := by
    unfold ratio
    split_ifs with h
    · rw [lt_div_iff₀ (ht.1 _)]
      exact hj2 _ rfl
    · exact hj1
  have hr0 : 0 < ratio t j := hT.trans hrat
  have hzero : ∀ α β : FrameIx r, frameLev j α < 2 → frameLev j β = 2 →
      frameIdem (σ : E →+* E) J X Y α * γ.1.1 * frameIdem (σ : E →+* E) J X Y β = 0 := fun α β hα hβ => by
    ext u v
    let m : GAd σ J := k * ((p * a * k)⁻¹ * ratEmb σ J γ * (p * a * k)) * k⁻¹
    have hm : m ∈ C' := ⟨(k, _, k⁻¹), ⟨hk, hγ, K.inv_mem hk⟩, rfl⟩
    have hgm : ratEmb σ J γ = p * a * m * a⁻¹ * p⁻¹ := by
      simp only [m]; group
    refine GlobalTheory.CompanionTheory.SmallIntegral.eq_zero_of_isIntegral_mul_of_small E d _ hd
      (hint p hp a ha.1 m hm γ hgm α β u v) (B / ratio t j) (fun φ => ?_) ?_
    · obtain ⟨w, τ, rfl⟩ := exists_embOver F E σ hcm φ
      have h1 := hB p hp t ht a ha m hm w τ j α β hα hβ u v
      rw [← hgm, archMat_ratEmb] at h1
      have e : τ.1 ((frameIdem (σ : E →+* E) J X Y α * γ.1.1 * frameIdem (σ : E →+* E) J X Y β) u v) =
          ((frameIdem (σ : E →+* E) J X Y α).map τ.1 * γ.1.1.map τ.1 * (frameIdem (σ : E →+* E) J X Y β).map τ.1) u v := by
        rw [← Matrix.map_mul, ← Matrix.map_mul]; rfl
      rw [e]; exact h1
    · have h2 : (d : ℝ) * (B / ratio t j) < 1 := by
        rw [← mul_div_assoc, div_lt_one hr0]
        nlinarith
      exact pow_lt_one₀ (by positivity) h2 Module.finrank_pos.ne'
  exact GlobalTheory.T.frame_block_zero_stabilizes_flag E (σ : E →+* E) n r J X Y (gram_YX hcm hJ hW) γ.1.1 j hzero l hl

end GlobalTheory.CompanionTheory.FlagKey

end
