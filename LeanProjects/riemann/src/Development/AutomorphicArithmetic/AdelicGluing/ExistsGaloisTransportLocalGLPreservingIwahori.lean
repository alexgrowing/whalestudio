import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import Development.AutomorphicArithmetic.AdelicQuotients.FinAtMapGLGalAdMemIwahori
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate

section SlopeTestRemainingChoices

open GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct ValuativeRel

private theorem galAd_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : galAd σ a = σ • a := by
  have h1 : (MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ) = Formalism.L2.Host.CT.adMap σ.toRingEquiv :=
    UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv _ (continuous_const_smul σ) fun x => GroundTheory.Global.AdeleBaseChange.smul_algebraMap σ x
  rw [UpperTheory.ConvolutionTheory.K.galAdEq, ← h1]
  rfl

variable {E : Type} [Field E] [NumberField E]

private theorem v_lt (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

private theorem v_le (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one,
    Valued.toNormedField.norm_le_one_iff]

private theorem v_eq (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ ‖y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, v_le, ← not_lt (b := 1) (a := ‖y‖), ← v_lt, not_lt]

private theorem unif_lt (w : HeightOneSpectrum (𝓞 E)) : ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)‖ < 1 := by
  rw [← v_lt]
  have h := GLnLocal.irreducible_uniformizer (w.adicCompletion E)
  refine lt_of_le_of_ne (GLnLocal.uniformizer (w.adicCompletion E)).2 fun e => h.not_isUnit ?_
  exact (Valuation.integer.integers (ValuativeRel.valuation (w.adicCompletion E))).isUnit_of_one' e

private theorem unif_max (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) (hy : ‖y‖ < 1) :
    ‖y‖ ≤ ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E)‖ := by
  have h := GLnLocal.irreducible_uniformizer (w.adicCompletion E)
  let z : 𝒪[w.adicCompletion E] := ⟨y, ((v_lt w y).2 hy).le⟩
  have hz : z ∈ IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := fun hu =>
    ((v_lt w y).2 hy).ne ((Valuation.integer.integers (ValuativeRel.valuation (w.adicCompletion E))).one_of_isUnit hu)
  rw [h.maximalIdeal_eq, Ideal.mem_span_singleton'] at hz
  obtain ⟨a, ha⟩ := hz
  have e : y = a.1 * (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) := (congrArg Subtype.val ha).symm
  rw [e, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) ((v_le w _).1 a.2)

end SlopeTestRemainingChoices

theorem UpperTheory.exists_galois_transport_localGL_preserving_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E) (n : ℕ), 0 < n → ∀ w : Pl E,
          ∃ s : GL (Fin n) (w.adicCompletion E) ≃* GL (Fin n) ((σ • w).adicCompletion E),
            (∀ g, (mapGL n (galAd σ) (finEmb E n (AdelicGLn.localEmbedding w g)) : AdelicGLn.AdelicGL E n) = finEmb E n (AdelicGLn.localEmbedding (σ • w) (s g))) ∧
            (∀ g, g ∈ GLnLocal.iwahori (w.adicCompletion E) n ↔ s g ∈ GLnLocal.iwahori ((σ • w).adicCompletion E) n) ∧
            ∀ ν : Fin n → ℤ, s (Cartan.diagPow (w.adicCompletion E) n ν) ∈ iwCoset (σ • w) ν := by
  intro F E _ _ _ _ _ _ σ n _ w
  have h' : w = σ⁻¹ • (σ • w) := (inv_smul_smul σ w).symm
  let t : w.adicCompletion E ≃+* (σ • w).adicCompletion E :=
    RingEquiv.ofRingHom (galHom σ w (σ • w) rfl) (galHom σ⁻¹ (σ • w) w h')
      (galHom_comp_galHom σ⁻¹ σ (mul_inv_cancel σ) _ _ h' rfl) (galHom_comp_galHom σ σ⁻¹ (inv_mul_cancel σ) _ _ rfl h')
  have hc : ∀ a (u : Pl E), (galAd σ a).2 (σ • u) = galHom σ u (σ • u) rfl (a.2 u) := fun a u => by
    rw [galAd_smul]; exact AdeleBaseChange.smul_snd_eq_galHom σ a u _ rfl
  have hn : ∀ y, ‖t y‖ = ‖y‖ := fun y => by
    refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun y => ‖t y‖ = ‖y‖) y
      (isClosed_eq (continuous_norm.comp (continuous_galHom σ w _ rfl)) continuous_norm) fun l => ?_
    have h1 := (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ (algebraMap E _ l)).1 w
    rw [hc] at h1
    exact h1
  let s : GL (Fin n) (w.adicCompletion E) ≃* GL (Fin n) ((σ • w).adicCompletion E) :=
    Units.mapEquiv t.mapMatrix.toMulEquiv
  have hs : ∀ g i j, s g i j = t (g i j) := fun _ _ _ => rfl
  refine ⟨s, fun g => ?_, fun g => ?_, fun ν => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
    · have e1 : ∀ (y : AdelicGLn.FiniteAdelicGL E n), (finEmb E n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E)) i j :=
        fun y => congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
      refine Eq.trans ?_ (e1 _).symm
      funext v
      change (galAd σ (finEmb E n (AdelicGLn.localEmbedding w g) i j)).1 v = _
      rw [galAd_smul, AdeleBaseChange.smul_fst, e1]
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.one_apply_eq]
        exact map_one _
      · simp only [Matrix.one_apply_ne hij]
        exact map_zero _
    · refine FiniteAdeleRing.ext _ fun v => ?_
      obtain ⟨u, rfl⟩ : ∃ u, v = σ • u := ⟨σ⁻¹ • v, (smul_inv_smul σ v).symm⟩
      refine (hc (finEmb E n (AdelicGLn.localEmbedding w g) i j) u).trans ?_
      change galHom σ u (σ • u) rfl (finAt u (finEmb E n (AdelicGLn.localEmbedding w g)) i j) =
        finAt (σ • u) (finEmb E n (AdelicGLn.localEmbedding (σ • w) (s g))) i j
      by_cases hu : u = w
      · subst hu
        rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n u).2.1, (UpperTheory.ConvolutionTheory.Tf.locEmb E n (σ • u)).2.1]
        rfl
      · rw [(UpperTheory.ConvolutionTheory.Tf.locEmb E n w).2.2.1 u hu, (UpperTheory.ConvolutionTheory.Tf.locEmb E n (σ • w)).2.2.1 _ fun e => hu (MulAction.injective σ e)]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.one_apply_ne hij]
  · simp only [GLnLocal.mem_iwahori_iff, v_lt, v_eq, hs, hn]
    refine and_congr (forall₂_congr fun i j => ?_) Iff.rfl
    exact ((v_le w _).trans (by rw [hn])).trans (v_le (σ • w) (t (g i j))).symm
  · set p := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) with hp
    set p' := (GLnLocal.uniformizer ((σ • w).adicCompletion E) : (σ • w).adicCompletion E) with hp'
    have h0 : p' ≠ 0 := Cartan.uniformizer_ne_zero _
    have h1 : ‖t p‖ = ‖p'‖ := le_antisymm (unif_max _ _ (by rw [hn]; exact unif_lt w)) (by
      rw [hn, ← t.apply_symm_apply p', hn]
      exact unif_max _ _ (by rw [← hn, t.apply_symm_apply]; exact unif_lt _))
    refine ⟨s (Cartan.diagPow _ n ν) * (Cartan.diagPow _ n ν)⁻¹, ?_, 1, one_mem _, by simp⟩
    have e : ((s (Cartan.diagPow _ n ν) * (Cartan.diagPow _ n ν)⁻¹ : GL (Fin n) ((σ • w).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((σ • w).adicCompletion E)) = Matrix.diagonal fun i => t p ^ ν i * p' ^ (-ν i) := by
      rw [← Matrix.diagonal_mul_diagonal, Units.val_mul]
      congr 1
      ext i j
      rw [hs, Cartan.coe_diagPow]
      by_cases hij : i = j
      · subst hij
        simp [hp]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have h2 : ∀ i, ‖t p ^ ν i * p' ^ (-ν i)‖ = 1 := fun i => by
      rw [norm_mul, norm_zpow, norm_zpow, h1, ← zpow_add₀ (norm_ne_zero_iff.2 h0), add_neg_cancel, zpow_zero]
    refine (GLnLocal.mem_iwahori_iff _ n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
    · refine (v_le _ _).2 ?_
      rw [e]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, h2]
      · simp [Matrix.diagonal_apply_ne _ hij]
    · rw [v_lt, e, Matrix.diagonal_apply_ne _ (by rintro rfl; exact lt_irrefl _ hij)]
      simp
    · rw [v_eq, e, Matrix.diagonal_apply_eq, h2]
