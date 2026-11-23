import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfIsSkew
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeightConvReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleNormProductIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountIntegrableBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCountLatticeStabilizersStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblHeightInt

open scoped ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem integrable_left (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}
    (ha : IsMajorantFrame σ J a) (hI : HasIwasawa σ Q (KAd σ Q L a)) :
    ∃ R : ℝ, ∀ μ : Measure (GAd σ J), μ.IsHaarMeasure → ∀ t : ℝ, R < t →
      Integrable (fun g => (hgtAd σ Q L a (ioH (AF F) σ hQ (g, 1)) : ℝ) ^ t) μ := by
  classical
  subst hQ
  obtain ⟨c, hc⟩ := GlobalTheory.T.bounded_count_lattice_stabilizers F E σ n J L
  choose! T hT hTx using hc
  refine ⟨max ((c : ℝ) + 1) n, fun μ hμ t ht => ?_⟩
  have ht1 : (c : ℝ) + 1 < t := (le_max_left _ _).trans_lt ht
  have ht2 : (n : ℝ) < t := (le_max_right _ _).trans_lt ht
  have ht0 : 0 ≤ t := (Nat.cast_nonneg n).trans ht2.le
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := t2Space_adeleRing' (F := F)
  set Q := dblGram finSumFinEquiv J with hQ
  let fa : ∀ w, GArch σ J w → ℝ := fun w y =>
    (hgtArch σ Q w (Formalism.UG.bc (compInf F E w) a) (ioH w.Completion σ rfl (y, 1)) : ℝ) ^ t
  have hfa : ∀ w (m : Measure (GArch σ J w)), m.IsHaarMeasure → Integrable (fa w) m := fun w m hm => by
    have := GlobalTheory.RealHeight.heightConv_real F E σ hcm n J hJ w _ (ha w) m hm (t - n / 2) (by linarith)
    simpa only [GlobalTheory.IndefiniteRowSideFullHecke.LocalMajorantConvergence.HeightConv, sub_add_cancel] using this
  have hfc : ∀ w, Continuous (fa w) := fun w =>
    (NNReal.continuous_coe.comp (((hI.arch w).continuous_hgtH (continuous_absEw w) (isCompact_KArch hcm w _)).comp
      ((continuous_ioH _).comp (continuous_id.prodMk continuous_const)))).rpow_const fun _ => Or.inr ht0
  have hfa0 : ∀ w y, 0 ≤ fa w y := fun w y => Real.rpow_nonneg (NNReal.coe_nonneg _) _
  let U : Set (GAd σ J) := {g | ∀ v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 F))), proj σ J v g ∈ stabLoc σ J L v}
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have hU : MeasurableSet U := by
    have : U = ⋂ v, proj σ J v ⁻¹' (stabLoc σ J L v) := by ext g; simp [U]
    rw [this]
    exact MeasurableSet.iInter fun v => (continuous_proj σ J v).measurable (isOpen_stabLoc σ J L v).measurableSet
  let ψ : GAd σ J → ℝ≥0∞ := fun g => ∏ w, ENNReal.ofReal (fa w (projArch σ J w g))
  have hψ : Measurable ψ := Finset.measurable_prod _ fun w _ =>
    ((hfc w).comp (continuous_projArch σ J w)).measurable.ennreal_ofReal
  have hφ : ∫⁻ g, U.indicator ψ g ∂μ ≠ ⊤ := by
    obtain ⟨μa, hμa⟩ := exists_isRestrictedProd_of_haar σ J L μ
    have := ((hμa.euler_product ∅ (fun v _ => haarLoc_stabLoc σ J L v)).2
      (fun w y => ENNReal.ofReal (fa w y)) (fun _ _ => 1)
      (fun w => (hfc w).measurable.ennreal_ofReal.aemeasurable)).1 (fun _ _ _ _ => rfl) ∅ le_rfl (by simp)
    rw [lintegral_indicator hU]
    simp only [finprod_one, mul_one, Finset.prod_empty] at this
    rw [this]
    exact ENNReal.prod_ne_top fun w _ => (hfa w _ (hμa.haar_arch w)).lintegral_lt_top.ne
  let T' : ℕ → Finset (GAd σ J) := fun m => (T m).image fun x => ofFin σ J (projFin σ J x)
  have hcont : Continuous fun g : GAd σ J => (hgtAd σ Q L a (ioH (AF F) σ rfl (g, 1)) : ℝ) ^ t :=
    (NNReal.continuous_coe.comp ((hI.continuous_hgtH continuous_absE (isCompact_KAd hcm)).comp
      ((continuous_ioH _).comp (continuous_id.prodMk continuous_const)))).rpow_const fun _ => Or.inr ht0
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  refine lt_top_iff_ne_top.2 (GlobalTheory.T.lattice_count_integrable_bound (GAd σ J) μ (U.indicator ψ) _ (hψ.indicator hU) hφ T' c t
    (fun m hm => Finset.card_image_le.trans (hT m hm)) ht1 fun g => ?_)
  choose d hd0 hd1 hd2 hd3 using fun v => GlobalTheory.T.iwasawa_decomposition_local F E σ hcm n J hJ.2 Q rfl L v (hI.fin v) (proj σ J v g)
  have hp : ∀ v, proj σ Q v (ioH (AF F) σ rfl (g, 1)) = ioH _ σ rfl (proj σ J v g, 1) := fun v => by
    rw [proj_ioH, map_one]
  have hpa : ∀ w, projArch σ Q w (ioH (AF F) σ rfl (g, 1)) = ioH _ σ rfl (projArch σ J w g, 1) := fun v => by
    rw [projArch_ioH, map_one]
  have hfin := finite_mulSupport_hgtFin (L := L) (ioH (AF F) σ (rfl : Q = _) (g, 1))
  simp only [hp, hd2] at hfin
  obtain ⟨m, hm, hm1, hm2⟩ := GlobalTheory.T.finite_adele_norm_product_integer F d hd0 hd1 hfin
  obtain ⟨x, hx, hxg⟩ := hTx m hm g fun v => hd3 v m (hm2 v)
  refine ⟨m, hm, ofFin σ J (projFin σ J x), Finset.mem_image_of_mem _ hx, ?_⟩
  have hmem : (ofFin σ J (projFin σ J x))⁻¹ * g ∈ U := fun v _ => by
    simpa only [map_mul, map_inv, proj_ofFin, projFinLoc_projFin] using hxg v
  rw [Set.indicator_of_mem hmem, hI.hgtAd_eq hcm]
  simp only [hp, hpa, hd2, hm1, ψ, map_mul, map_inv, projArch_ofFin, inv_one, one_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => hfa0 w _, NNReal.coe_mul,
    Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _), NNReal.coe_prod,
    ← Real.finset_prod_rpow _ _ (fun _ _ => NNReal.coe_nonneg _), mul_comm,
    ENNReal.ofReal_mul (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
  refine le_of_eq ?_
  congr 1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [NNReal.coe_inv, NNReal.coe_natCast, Real.inv_rpow hm'.le, ← Real.rpow_neg hm'.le,
    ← ENNReal.ofReal_rpow_of_pos hm', ENNReal.ofReal_natCast]

theorem integrable_right (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}
    (ha : IsMajorantFrame σ J a) (hI : HasIwasawa σ Q (KAd σ Q L a)) (μ : Measure (GAd σ J)) (hμ : μ.IsHaarMeasure) :
    ∃ R : ℝ, ∀ t : ℝ, R < t → Integrable (fun g => (hgtAd σ Q L a (ioH (AF F) σ hQ (1, g)) : ℝ) ^ t) μ := by
  obtain ⟨R, hR⟩ := integrable_left hcm hJ hQ L ha hI
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HermUnimod.exists_anti hcm
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := t2Space_adeleRing' (F := F)
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ (GlobalTheory.SiegelSet.sigma_sigma hcm) hδ hσδ hJ μ
  have hH : μ.inv.IsHaarMeasure := {}
  refine ⟨R, fun t ht => ?_⟩
  have := (integrable_map_equiv (μ := μ) (MeasurableEquiv.inv (GAd σ J)) _).1 (hR μ.inv hH t ht)
  refine this.congr (Eventually.of_forall fun g => ?_)
  have e : ioH (AF F) σ hQ (1, g) = (ioDiag hQ g : GAd σ Q) * ioH (AF F) σ hQ (g⁻¹, 1) := by
    rw [coe_ioDiag, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
  have e2 := hI.hgtH_left continuous_absE (isCompact_KAd hcm) (ioDiag hQ g) (ioH (AF F) σ hQ (g⁻¹, 1))
  rw [aH_ioDiag, abs_detH (absE_conjUnit σ) hJ.2, one_mul, ← e] at e2
  exact congrArg (fun x : ℝ≥0 => (x : ℝ) ^ t) e2.symm

def Conv {A : Type} [CommRing A] [TopologicalSpace A] {n : ℕ} (H : Subgroup (GL (Fin n) A))
    (G : Subgroup (GL (Fin (n + n)) A)) (ν : Aˣ →* ℝ≥0) (S : Set (GL (Fin (n + n)) A)) : Prop :=
  ∀ i : H × H →* G, (∀ h h', (i (h, h')).1.1 = blkMat finSumFinEquiv h.1.1 h'.1.1) →
    ∀ K : Subgroup G, (∀ g, g ∈ K ↔ g.1 ∈ S) → IwasawaOf finSumFinEquiv G.subtype ν K →
    ∀ μ : @Measure H (borel H), @Measure.IsHaarMeasure H _ _ (borel H) μ → ∃ R : ℝ, ∀ t : ℝ, R < t →
      @Integrable _ _ _ _ (borel H) (fun g => ((hgtOf finSumFinEquiv G.subtype ν K (i (1, g)) : ℝ≥0) : ℝ) ^ t) μ

theorem conv_adelic (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] {a : GL (Fin n) (AF F ⊗[F] E)}
    (ha : IsMajorantFrame σ J a) :
    Conv (HR (AF F) σ J) (HR (AF F) σ Q) (absE F E) ((KAd σ Q L a).map (matHom (AF F) σ Q)) := by
  intro i hi K hK hI μ hμ
  obtain rfl : K = KAd σ Q L a := Subgroup.ext fun g =>
    (hK g).trans (Subgroup.mem_map_iff_mem (matHom_injective (AF F) σ Q))
  obtain rfl : i = ioH (AF F) σ hQ := MonoidHom.ext fun x => Subtype.ext (Units.ext (hi x.1 x.2))
  exact integrable_right hcm hJ hQ L ha hI.1 μ hμ

omit [NumberField E] in

theorem UG_smul {n : ℕ} {ξ : E} (hξ : ξ ≠ 0) (J : Matrix (Fin n) (Fin n) E) :
    UG (cA σ) (incM F (ξ • J)) = UG (cA σ) (incM F J) := by
  have e : incM F (ξ • J) = inclR (F := F) (AF F) ξ • incM F J := by ext i j; simp [incM]
  have hu : IsUnit (inclR (F := F) (AF F) ξ) := (IsUnit.mk0 _ hξ).map _
  ext g
  change _ * incM F (ξ • J) * _ = incM F (ξ • J) ↔ _ * incM F J * _ = incM F J
  rw [e, Matrix.mul_smul, Matrix.smul_mul, hu.smul_left_cancel]

omit [NumberField E] in
theorem isStab_iff {n : ℕ} {B : Base F E} {X : Spc F E n} {K : Subgroup (UA σ X.J)} (hK : IsStab B K)
    (g : GL (Fin n) (AE F E)) (hg : g ∈ UG (cA σ) (incM F X.J)) : (⟨g, hg⟩ : UA σ X.J) ∈ K ↔
      (∀ w, Commute (g.1.map (piInf (B.emb w))) (X.θ w)) ∧
      (∀ z ∈ latHat X, g.1 *ᵥ z ∈ latHat X) ∧ ∀ z ∈ latHat X, (g⁻¹).1 *ᵥ z ∈ latHat X := by
  have e1 : mat (⟨g, hg⟩ : UA σ X.J) = g.1 := rfl
  have e2 : mat (⟨g, hg⟩⁻¹ : UA σ X.J) = (g⁻¹).1 := congrArg Units.val (Subgroup.coe_inv _ _)
  rw [hK, e1, e2, forall₂_and]

theorem isCartan_smul {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) {c ε : ℝ} (h1 : ε * ε = 1)
    (h2 : 0 < ε * c) : IsCartan ((c : ℂ) • M) ((ε : ℂ) • θ) := by
  have h1' : (ε : ℂ) * ε = 1 := by exact_mod_cast h1
  have hm : ((ε : ℂ) • θ).map star = (ε : ℂ) • θ.map star := by ext i j; simp
  refine ⟨by rw [Matrix.smul_mul, Matrix.mul_smul, h.1, smul_smul, h1', one_smul], ?_, fun x hx => ?_⟩
  · rw [hm]; simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.2.1]
    congr 1; linear_combination (c : ℂ) * h1'
  · have := h.2.2 x hx
    simp only [Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    exact mul_pos (by linarith [mul_comm c ε]) this

theorem blkMat_smul {A : Type} [CommRing A] {n : ℕ} (t : A) (x : Matrix (Fin n) (Fin n) A) :
    blkMat finSumFinEquiv (t • x) (-(t • x)) = t • blkMat finSumFinEquiv x (-x) := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.smul_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, smul_neg]

theorem integrable_hgt_rpow : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∃ R : ℝ, ∀ t : ℝ, R < t →
      Integrable (fun g => ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K (i (1, g)) : ℝ≥0) : ℝ) ^ t) μ := by
  intro _ F E _ _ _ _ _ σ B hB n r s W hW W₂ hJ₂ hL₂ hθ₂ i hi K hK
  have hcm := hB.cm
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HermUnimod.exists_anti hcm
  have hc : ∀ w : InfinitePlace F, ∃ c ε : ℝ, (B.emb w).1 δ = c * Complex.I ∧ ε * ε = 1 ∧ 0 < ε * c := fun w => by
    have h1 := congrArg Complex.re (hcm.2.2.2 (B.emb w).1 δ)
    rw [hσδ, map_neg, Complex.neg_re, Complex.star_def, Complex.conj_re] at h1
    have h2 : ((B.emb w).1 δ).re = 0 := by linarith
    have h3 : ((B.emb w).1 δ).im ≠ 0 := fun e => hδ ((map_eq_zero _).1 (Complex.ext h2 e))
    have h4 : (B.emb w).1 δ = (((B.emb w).1 δ).im : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [h2]
    rcases h3.lt_or_gt with e | e
    · exact ⟨_, -1, h4, by simp, by linarith⟩
    · exact ⟨_, 1, h4, by simp, by linarith⟩
  choose c ε hc h1 h2 using hc
  haveI : Submodule.IsLattice E W.L := hW.lat
  have hherm : ∀ i j, σ ((δ • W.J) j i) = (δ • W.J) i j := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hσδ, hW.skew, neg_mul_neg]
  have hJt : IsHermND σ (δ • W.J)ᵀ := ⟨fun i j => hherm j i, by
    rw [Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hδ) (GlobalTheory.SkewUnimod.det_ne_zero_of_isSkew hW)⟩
  have hθ : ∀ w, IsCartan ((δ • W.J).map (B.emb w).1) ((ε w : ℂ) • W.θ w) := fun w => by
    have : (δ • W.J).map (B.emb w).1 = (c w : ℂ) • (Complex.I • W.J.map (B.emb w).1) := by
      ext i j; simp [hc w, mul_assoc]
    rw [this]
    exact isCartan_smul (hW.cartan w) (h1 w) (h2 w)
  let X₂ : Spc F E (n + n) := { W₂ with J := δ • W₂.J }
  have hQ : X₂.Jᵀ = dblGram finSumFinEquiv (δ • W.J)ᵀ := by
    rw [← GlobalTheory.DblIwasawa.transpose_dblGram, dblGram, blkMat_smul, ← dblGram, ← hJ₂]
  obtain ⟨a, hmaj, harch⟩ := GlobalTheory.DblIwasawa.arch hcm B (δ • W.J) (fun w => (ε w : ℂ) • W.θ w) hherm hθ hQ
  have hε : ∀ w, (ε w : ℂ) ≠ 0 := fun w => by exact_mod_cast left_ne_zero_of_mul_eq_one (h1 w)
  have harch' : ∀ (w : InfinitePlace F) (k : GArch σ X₂.Jᵀ w), k ∈ KArch σ X₂.Jᵀ w (Formalism.UG.bc (compInf F E w) a) ↔
      Commute ((matHom w.Completion σ X₂.Jᵀ k).1.map (infEmb (B.emb w))) (X₂.θ w) := fun w k => by
    rw [harch, blkMat_smul, Commute.smul_right_iff₀ (hε w), ← hθ₂]
  have hL₂' : X₂.L.IsLattice E := by change W₂.L.IsLattice E; rw [hL₂]; infer_instance
  have hL₃ : X₂.L = sumLat finSumFinEquiv W.L W.L := hL₂
  have key : ∀ g : GAd σ X₂.Jᵀ, GlobalTheory.IwLine.ofGAd σ X₂.J g ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X₂ ↔
      g ∈ KAd σ X₂.Jᵀ W.L a := by
    intro g
    rw [mem_KAd]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B (n + n) X₂ hL₂' g h
      refine ⟨fun v => ?_, fun w => (harch' w _).2 (h1 w)⟩
      have := h2 v; rwa [hL₃] at this
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B (n + n) X₂ hL₂' g (fun w => (harch' w _).1 (h1 w)) (fun v => ?_)
      rw [hL₃]; exact h2 v
  have hH : HR (AF F) σ (δ • W.J)ᵀ = UG (cA σ) (incM F W.J) :=
    (GlobalTheory.IwLine.UG_eq_HR σ _).symm.trans (UG_smul hδ _)
  have hG : HR (AF F) σ X₂.Jᵀ = UG (cA σ) (incM F W₂.J) :=
    (GlobalTheory.IwLine.UG_eq_HR σ _).symm.trans (UG_smul hδ _)
  have hC := conv_adelic hcm hJt hQ W.L hmaj
  generalize hS : SetLike.coe ((KAd σ X₂.Jᵀ W.L a).map (matHom (AF F) σ X₂.Jᵀ)) = S at hC
  rw [hH, hG] at hC
  refine hC i hi K fun g => ?_
  have hg : g.1 ∈ HR (AF F) σ X₂.Jᵀ := hG.ge g.2
  have hg' : g.1 ∈ UG (cA σ) (incM F X₂.J) := (GlobalTheory.IwLine.UG_eq_HR σ X₂.J).ge hg
  rw [← hS]
  refine ((isStab_iff hK g.1 g.2).trans (isStab_iff (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X₂) g.1 hg').symm).trans ?_
  exact (key ⟨g.1, hg⟩).trans (Subgroup.mem_map_iff_mem (matHom_injective (AF F) σ X₂.Jᵀ)).symm

end GlobalTheory.DblHeightInt

end
