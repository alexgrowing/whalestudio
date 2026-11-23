import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationGoodModelsIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantUnderIntegralLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSupportBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLevelConductorCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelsDifferBySymplecticMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairEvaluationSelfLinearStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
open GlobalTheory.ThetaDenom

namespace GlobalTheory.ThKTorusBound

open scoped Classical

theorem exists_clm_eval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F),
      ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), e (om (κ, h) (pureA F f φ)) z = T f := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev φ hφ κ h z
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hPair.weil
  have hl : (LinearMap.proj z : Fn F n d →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d) := GlobalTheory.RealLift.eval_mem_adm z
  have hl2 := GlobalTheory.DoublingEv.IsTame.comp_adm
    (GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e hPair.good hM₁ hev) hl
  have hl3 := hS.adm (κ, h) _ hl2
  obtain ⟨T, hT⟩ := hl3 φ hφ
  exact ⟨T, fun f => by simpa using (hT f)⟩

theorem exists_transfer : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∃ (om₁ : Rep σ X W) (e₀ : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), IsPair B M₁ χX χW om₁ r s r' s' ∧ IsEv B M M₁ 1 1 ∅ e₀ ∧
      ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = c • om₁ x (e₀ Φ) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev
  obtain ⟨a, ha, hco⟩ := GlobalTheory.goodModel_coords_rat_symplectic F E σ B.ψ n d X W M M₁ hP.good hM₁
  obtain ⟨e₀, -, -, he₀, hbij, -⟩ := GlobalTheory.RatWeilOp.exists_intertwiner hK.base F E σ B n d X W M M₁ r s r' s'
    hP.base hP.herm hP.skew hP.good hM₁ a ha hco
  obtain ⟨om₁, hW, hint⟩ := GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e₀ he₀ hbij
  have h1n : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by simp [incM]
  have h1d : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  obtain ⟨c, hc⟩ := GlobalTheory.T.pair_evaluation_self_linear hK F E σ B n d X W M χX χW om r s r' s' hP M₁ e₀ hM₁ he₀ e (fun z Φ hΦ => by
    have := hev.Heisenberg₂ z Φ hΦ
    rwa [h1n, h1d, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this)
  refine ⟨om₁, e₀, c, ⟨hP.base, hP.herm, hP.skew, hM₁, hP.hX, hP.hW, hP.resX, hP.resW, hW⟩, he₀, fun x Φ hΦ => ?_⟩
  rw [hc _ (hP.weil.isUSplitting.pres x Φ hΦ), hint x Φ hΦ]

theorem adelic_char_denom {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∃ D : ℕ, 0 < D ∧ ∀ x : AF F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (x * t) = 1) →
      ∀ v : Pl F, evFin F v ((D : AF F) * x) ∈ v.adicCompletionIntegers F := by
  obtain ⟨D, hD, hcond⟩ := std_char_denom ψ hψ
  obtain ⟨m, hm, htriv⟩ := GlobalTheory.PsiTriv.exists_nat_trivial ψ hψ.1
  refine ⟨D, hD, fun x hx v => ?_⟩
  obtain ⟨ξ, a, ha, hxa⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F m hm).1 x.2
  set A : AF F := ((0 : InfiniteAdeleRing F), a) with hA
  have hAv : ∀ v : Pl F, evFin F v A ∈ v.adicCompletionIntegers F := fun v => ha v
  have hev : ∀ v : Pl F, evFin F v x = algebraMap F (Fv F v) ξ + (m : Fv F v) * evFin F v A := fun v => by
    have e1 : evFin F v x = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v x.2 := rfl
    have e2 : evFin F v A = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a := rfl
    rw [e1, e2, hxa, map_add, map_nsmul, AlgHom.commutes, nsmul_eq_mul]
  have hsplit : ∀ t : AF F, t.1 = 0 → x * t = algebraMap F (AF F) ξ * t + (m : AF F) * A * t := fun t ht => by
    refine Prod.ext ?_ ?_
    · change x.1 * t.1 = (algebraMap F (AF F) ξ).1 * t.1 + ((m : AF F) * A).1 * t.1
      rw [ht, mul_zero, mul_zero, mul_zero, add_zero]
    · change x.2 * t.2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ * t.2 + (m : FiniteAdeleRing (𝓞 F) F) * a * t.2
      rw [hxa, nsmul_eq_mul, add_mul]
  obtain ⟨o, ho⟩ := hcond ξ fun t ht0 ht1 => by
    have h1 := hx t ht0 ht1
    have h2 : ψ ((m : AF F) * A * t) = 1 := by
      refine htriv _ ?_ fun v => ?_
      · change ((m : AF F) * A).1 * t.1 = 0
        rw [ht0, mul_zero]
      · rw [map_mul, map_mul, map_natCast, norm_mul, norm_mul, mul_assoc]
        exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀
          (Valued.toNormedField.norm_le_one_iff.2 (hAv v)) (norm_nonneg _) (ht1 v))
    rwa [hsplit t ht0, AddChar.map_add_eq_mul, h2, mul_one] at h1
  have ho' : (D : Fv F v) * algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F := by
    rw [← map_natCast (algebraMap F (Fv F v)) D, ← map_mul, ho]
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v o
  rw [map_mul, map_natCast, hev, mul_add]
  exact add_mem ho' (mul_mem (natCast_mem _ D) (mul_mem (natCast_mem _ m) (hAv v)))

theorem tame_fixed {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ)
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)} (hT : GlobalTheory.DoublingEv.IsTame F T)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (f : SInf F κ) (a b : κ → AF F), IsMulInt F m₀ a → IsMulInt F m₀ b →
      schr ψ (a, b) (T (pureA F f g)) = T (pureA F f g) := by
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  obtain ⟨m₃, hm₃, h3⟩ := GlobalTheory.PsiTriv.exists_nat_trivial ψ hψ
  choose m₁ hm₁ h1 using fun j => GlobalTheory.SBTransl.transInv (g' j) (hg' j)
  choose M hM h2 using fun j => GlobalTheory.SuppDen.support_bounded_denominators (g' j) (hg' j)
  refine ⟨∏ j, 2 * m₁ j * M j * m₃, Finset.prod_pos fun j _ => by have := hm₁ j; have := hM j; positivity,
    fun f a b ha hb => ?_⟩
  have hj : ∀ j, schr ψ (a, b) (pureA F (P j f) (g' j)) = pureA F (P j f) (g' j) := fun j => by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at ha hb
    exact GlobalTheory.PureFix.pureA_fixed ψ (g' j) (m₁ j) (M j) m₃ (hm₁ j) (hM j) hm₃ (h1 j) (h2 j) h3 _ a b ha.mono hb.mono
  rw [hP]
  funext z
  have hz := fun j => congrFun (hj j) z
  simp only [schr, Finset.sum_apply, Finset.mul_sum] at hz ⊢
  exact Finset.sum_congr rfl fun j _ => hz j

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {Cc : Set (UA σ J)} (hCc : IsCompact Cc) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ κ ∈ Cc, (ht κ : ℝ) ≤ H := by
  have hc : Continuous fun κ : UA σ J => (ht κ : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  obtain ⟨H, hH⟩ := hCc.bddAbove_image hc.continuousOn
  exact ⟨max H 0, le_max_right _ _, fun κ hκ => (hH ⟨κ, hκ, rfl⟩).trans (le_max_left _ _)⟩

theorem support_unif : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ (C : ℝ) (k : ℕ), ∀ (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ (f : SInf F (Fin n × Fin d)) (z : Fin n × Fin d → AF F),
        e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev Cc hCc φ hφ
  obtain ⟨om₁, e₀, c, hP₁, he₀, hint⟩ := exists_transfer hK F E σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev
  have hsp := hP₁.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨m₀, hm₀, hinv⟩ := tame_fixed B.ψ hstd.1
    (GlobalTheory.EvTame.isTame_of_isEv F E σ B n d n d X W X W M M₁ 1 1 ∅ e₀ hP.good hM₁ he₀) φ hφ
  obtain ⟨D, hD, hcond⟩ := adelic_char_denom B.ψ hstd
  obtain ⟨C, hC⟩ := transport_denom M₁.co.e
  obtain ⟨H, hH0, hH⟩ := ht_bdd hCc
  refine ⟨D * m₀ * (max C 0 * H), 1, fun g h hg => ?_⟩
  obtain ⟨N, hN, hNle, hT⟩ := hC ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹) ((h : GL (Fin d) (AF F ⊗[F] E))⁻¹)
  rw [heightGL_inv, heightGL_inv] at hNle
  refine ⟨D * (m₀ * N), Nat.one_le_iff_ne_zero.2 (by positivity), ?_, ?_⟩
  · rw [pow_one]
    have : ((D * (m₀ * N) : ℕ) : ℝ) = D * m₀ * N := by push_cast; ring
    rw [this, mul_assoc (D * m₀ : ℝ)]
    refine mul_le_mul_of_nonneg_left (hNle.trans ?_) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_right (hH g hg) (NNReal.coe_nonneg _))
      (by positivity) (le_max_right _ _)
  intro f z hz j v
  have hΦ₀ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hΦ : e₀ (pureA F f φ) ∈ schA F (Fin n × Fin d) := he₀.maps _ hΦ₀
  have hz' : om₁ (g, h) (e₀ (pureA F f φ)) z ≠ 0 := by
    intro h0
    apply hz
    rw [hint _ _ hΦ₀, Pi.smul_apply, h0, smul_zero]
  have hfix : ∀ y : Fin n × Fin d → AF F, IsMulInt F (m₀ * N) y →
      schr B.ψ (0, y) (om₁ (g, h) (e₀ (pureA F f φ))) = om₁ (g, h) (e₀ (pureA F f φ)) := by
    clear hz hz' hcond hNle hC
    intro y hy
    set w' := M₁.co.e.symm (0, y) with hw'
    set w := ((g : GL (Fin n) (AF F ⊗[F] E))⁻¹ : GL (Fin n) (AF F ⊗[F] E)).1 * w' *
      (((h : GL (Fin d) (AF F ⊗[F] E))⁻¹ : GL (Fin d) (AF F ⊗[F] E)).1)ᵀ with hw
    obtain ⟨h1, h2⟩ := hT m₀ y hy
    have hΦw : M₁.co.rho B.ψ w (e₀ (pureA F f φ)) = e₀ (pureA F f φ) := hinv f _ _ h1 h2
    have hact : actAB (cA σ) (g, h) w = w' := by
      simp only [actAB, hw]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
        Matrix.mul_one]
    have himpl := hsp.impl (g, h) w _ hΦ
    rw [hΦw, hact] at himpl
    rw [Darboux.rho, hw', LinearEquiv.apply_symm_apply] at himpl
    exact himpl.symm
  have key := hcond (((m₀ * N : ℕ) : AF F) * z j) (fun t ht0 ht1 => by
    have e1 := congrFun (hfix _ (isMulInt_single (m₀ * N) j t ht0 ht1)) z
    simp only [schr, dotProduct_single, zero_dotProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero] at e1
    have e2 := (mul_eq_right₀ hz').1 e1
    rw [← e2]
    congr 1
    ring) v
  rwa [← mul_assoc, ← Nat.cast_mul] at key

theorem size_le {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z : κ → AF F, 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) ≤
      A * (1 + ‖fun i => evI F (z i)‖) := by
  refine ⟨1 + Fintype.card κ * Fintype.card (InfinitePlace F), by positivity, fun z => ?_⟩
  have h1 : ∀ j (w : InfinitePlace F), mixedEmbedding.normAtPlace w (evI F (z j)) ≤ ‖fun i => evI F (z i)‖ := fun j w => by
    refine le_trans ?_ (norm_le_pi_norm (fun i => evI F (z i)) j)
    by_cases hw : w.IsReal
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
      exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
      exact (norm_le_pi_norm _ _).trans (norm_snd_le _)
  have h2 : ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) ≤
      Fintype.card κ * Fintype.card (InfinitePlace F) * ‖fun i => evI F (z i)‖ := by
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun w _ => h1 j w).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h3 : (0 : ℝ) ≤ Fintype.card κ * Fintype.card (InfinitePlace F) := by positivity
  nlinarith [norm_nonneg fun i => evI F (z i)]

theorem decay_one : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ (N : ℕ) (f : SInf F (Fin n × Fin d)), ∃ (k : ℕ) (C : ℝ), ∀ (κ : UA σ X.J) (h : UA σ W.J) (z : Fin n × Fin d → AF F), κ ∈ Cc →
      ‖e (om (κ, h) (pureA F f φ)) z‖ * (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N ≤
        C * (ht h : ℝ) ^ k := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev Cc hCc φ hφ N f
  obtain ⟨om₁, e₀, c, hP₁, he₀, hint⟩ := exists_transfer hK F E σ B n d X W M χX χW om r s r' s' hP M₁ e hM₁ hev
  have hΦ₀ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨C, k, hC⟩ := GlobalTheory.ArchDecay.om_bound_arch F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ _ (he₀.maps _ hΦ₀) N
  obtain ⟨H, hH0, hH⟩ := ht_bdd hCc
  obtain ⟨A, hA0, hA⟩ := size_le (F := F) (κ := Fin n × Fin d)
  refine ⟨k, ‖c‖ * A ^ N * (max C 0 * H ^ k), fun κ h z hκ => ?_⟩
  have hS0 : (0 : ℝ) ≤ 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) :=
    add_nonneg zero_le_one
      (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg w _)
  have h1 := pow_le_pow_left₀ hS0 (hA z) N
  have h2 : C * ((ht κ : ℝ) * ht h) ^ k ≤ max C 0 * H ^ k * (ht h : ℝ) ^ k := by
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (hH κ hκ) (NNReal.coe_nonneg _)) k) (by positivity) (le_max_right _ _)
  rw [hint _ _ hΦ₀, Pi.smul_apply, smul_eq_mul, norm_mul]
  calc ‖c‖ * ‖om₁ (κ, h) (e₀ (pureA F f φ)) z‖ *
        (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N
      ≤ ‖c‖ * ‖om₁ (κ, h) (e₀ (pureA F f φ)) z‖ * (A * (1 + ‖fun i => evI F (z i)‖)) ^ N :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖c‖ * A ^ N * (‖om₁ (κ, h) (e₀ (pureA F f φ)) z‖ * (1 + ‖fun i => evI F (z i)‖) ^ N) := by
        rw [mul_pow]; ring
    _ ≤ ‖c‖ * A ^ N * (max C 0 * H ^ k * (ht h : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left ((hC κ h z).trans h2) (by positivity)
    _ = _ := by ring

theorem family_bound (F : Type) [Field F] [NumberField F] (κ ι : Type) [Fintype κ] (T : ι → SInf F κ →L[ℂ] ℂ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hT : ∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖T i f‖ ≤ C * w i ^ N) :
    ∃ (N : ℕ) (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ i f, ‖T i f‖ ≤ C * semK κ k f * w i ^ N := by
  obtain ⟨N, C, s, hs⟩ := GlobalTheory.schwartz_family_uniform_bound (κ → mixedEmbedding.mixedSpace F) ι T w hw hT
  set k := s.sup (fun x : ℕ × ℕ => max x.1 x.2)
  have hsub : s ⊆ Finset.Iic (k, k) := fun x hx => Finset.mem_Iic.2
    ⟨le_trans (le_max_left _ _) (Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx),
     le_trans (le_max_right _ _) (Finset.le_sup (f := fun x : ℕ × ℕ => max x.1 x.2) hx)⟩
  refine ⟨N, max C 0, k, le_max_right _ _, fun i f => (hs i f).trans ?_⟩
  have h3 : (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f ≤ semK κ k f :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) f
  exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) h3 (apply_nonneg _ _) (le_max_right _ _))
    (pow_nonneg (hw i) _)

theorem major_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (M₁ : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d), M₁.IsGood B.ψ → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (κ : UA σ X.J) (h : UA σ W.J), κ ∈ Cc →
      ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧ ∀ z : Fin n × Fin d → AF F,
        ‖e (om (κ, h) (pureA F f φ)) z‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j))) ^ N)⁻¹ ∧
        (e (om (κ, h) (pureA F f φ)) z ≠ 0 → ∀ j (v : Pl F), evFin F v ((m : AF F) * z j) ∈ v.adicCompletionIntegers F) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev Cc hCc φ hφ N
  obtain ⟨C₁, k₁, hsupp⟩ := support_unif hKP F E σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev Cc hCc φ hφ
  have hdec := decay_one hKP F E σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev Cc hCc φ hφ N
  choose T hT using exists_clm_eval F E σ B n d X W M χX χW om r s r' s' hPair M₁ e hM₁ hev φ hφ
  set S : (Fin n × Fin d → AF F) → ℝ := fun z =>
    1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (z j)) with hSdef
  have hS1 : ∀ z, 1 ≤ S z := fun z => le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg w _)
  have hSp : ∀ z, 0 < S z ^ N := fun z => pow_pos (lt_of_lt_of_le one_pos (hS1 _)) _
  have hht : ∀ h : UA σ W.J, (1 : ℝ) ≤ (ht h : ℝ) := fun h => by
    have := GlobalTheory.AdelicU.one_le_heightGL F h.1
    exact_mod_cast this
  let ι := {p : UA σ X.J × UA σ W.J × (Fin n × Fin d → AF F) // p.1 ∈ Cc}
  let T' : ι → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun i => ((S i.1.2.2 ^ N : ℝ) : ℂ) • T i.1.1 i.1.2.1 i.1.2.2
  have hT' : ∀ i f, ‖T' i f‖ = ‖e (om (i.1.1, i.1.2.1) (pureA F f φ)) i.1.2.2‖ * S i.1.2.2 ^ N := fun i f => by
    simp only [T', ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hSp _), hT]
    ring
  obtain ⟨k₂, C₃, k₃, hC₃, hBS⟩ := family_bound F (Fin n × Fin d) ι T' (fun i => (ht i.1.2.1 : ℝ))
    (fun i => NNReal.coe_nonneg _) fun f => by
      obtain ⟨k, C, hC⟩ := hdec f
      exact ⟨k, C, fun i => by rw [hT']; exact hC i.1.1 i.1.2.1 i.1.2.2 i.2⟩
  set K := max k₁ (max k₂ k₃)
  refine ⟨max C₁ 0 + C₃, K, fun f κ h hκ => ?_⟩
  obtain ⟨m, hm1, hmC, hmz⟩ := hsupp κ h hκ
  have hhtK : ∀ k, k ≤ K → (ht h : ℝ) ^ k ≤ (ht h : ℝ) ^ K := fun k hk => pow_le_pow_right₀ (hht h) hk
  have hsemK : semK (Fin n × Fin d) k₃ f ≤ semK (Fin n × Fin d) K f := by
    have hsub : Finset.Iic (k₃, k₃) ⊆ Finset.Iic (K, K) := fun x hx => by
      simp only [Finset.mem_Iic] at hx ⊢
      exact le_trans hx (by simp [K, Prod.le_def])
    exact Seminorm.le_def.mp (Finset.sup_mono hsub) f
  have hsem0 : 0 ≤ semK (Fin n × Fin d) k₃ f := apply_nonneg _ _
  have hpos : ∀ k, 0 ≤ (ht h : ℝ) ^ k := fun k => pow_nonneg (NNReal.coe_nonneg _) _
  have hC0 : 0 ≤ max C₁ 0 + C₃ := add_nonneg (le_max_right _ _) hC₃
  refine ⟨m, hm1, ?_, fun z => ⟨?_, fun hz j v => hmz f z hz j v⟩⟩
  · calc (m : ℝ) ≤ C₁ * (ht h : ℝ) ^ k₁ := hmC
      _ ≤ max C₁ 0 * (ht h : ℝ) ^ k₁ := mul_le_mul_of_nonneg_right (le_max_left _ _) (hpos _)
      _ ≤ (max C₁ 0 + C₃) * (ht h : ℝ) ^ K :=
          mul_le_mul (le_add_of_nonneg_right hC₃) (hhtK _ (le_max_left _ _)) (hpos _) hC0
  · have h1 := hBS ⟨(κ, h, z), hκ⟩ f
    rw [hT'] at h1
    refine (le_mul_inv_iff₀ (hSp z)).2 (le_trans h1 ?_)
    refine mul_le_mul ?_ (hhtK _ (le_trans (le_max_left _ _) (le_max_right _ _))) (hpos _)
      (mul_nonneg hC0 (apply_nonneg _ _))
    exact mul_le_mul (le_add_of_nonneg_left (le_max_right _ _)) hsemK hsem0 hC0

end GlobalTheory.ThKTorusBound
