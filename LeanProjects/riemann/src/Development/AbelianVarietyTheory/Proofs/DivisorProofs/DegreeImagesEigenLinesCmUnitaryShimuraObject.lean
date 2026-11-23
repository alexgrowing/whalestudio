import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermitianMetricDifferentialEqOfPairingRelation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CubeLBPairingIsoIffWeilPairingCompatibleOverRingStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLatticesStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignatureStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LinearIndependentOfIsLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilPairingEqOfIsomorphicCubePairings
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegOfLatRankEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormEmbeddingsRingHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegISupMapRankOneLatticeOfGramStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section
namespace GlobalTheory.FlatCM.ImageDeg

open GlobalTheory.HermHom in

theorem form_diff_eq_pair : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
  (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K))
  (f₁ f₂ : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M₁ M₂ : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K))
  (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f₁ → IsMonHom f₂ →
  IsMonHom g → LamEq P'.L f₁ f₂ P.L g (𝟙 P.A) → F.IsDiffOf F' f₁ M₁ → F.IsDiffOf F' f₂ M₂ → F.IsDiffOf F g N →
  ∀ s c c', h'.form s (M₂ c) (M₁ c') = h.form s c (N c') := by
  intro hU hL K _ _ P F P' F' h h' f₁ f₂ g M₁ M₂ N hh hh' hf₁ hf₂ hg hlam hM₁ hM₂ hN s c c'
  obtain ⟨Q, φ, t, u, Hm, χ, W, hφ, hA, hW, hform⟩ := hh s
  obtain ⟨Q', φ', t', u', Hm', χ', W', hφ', hA', hW', hform'⟩ := hh' s
  obtain ⟨-, a₀, ha₀, ea₀, da⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₁ hf₁
  obtain ⟨-, b₀, hb₀, eb₀, db⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₂ hf₂
  obtain ⟨-, g₀, hg₀, eg₀, dg⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have hlam₀ : LamEq F'.P₀.L a₀ b₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    lamEq_baseChange _ _ (spMap (algebraMap (𝓞 K) K)) P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A
      F.φ F.φ F'.φ F.φ F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1
      P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB F.P₀.isLB F'.fib.2.2 F.fib.2.2 f₁ f₂ g (𝟙 _) a₀ b₀ g₀ (𝟙 _)
      ea₀ eb₀ eg₀ (by simp) hlam
  obtain ⟨a₁, ha₁, ea⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 a₀
  obtain ⟨b₁, hb₁, eb⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 b₀
  obtain ⟨g₁, hg₁, eg⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ.2.1 g₀
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨Φ₁, hΦ₁, -, hΦd₁, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' a₁ ha₁
  obtain ⟨Φ₂, hΦ₂, -, hΦd₂, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' b₁ hb₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have hlam₁ : LamEq Q'.L a₁ b₁ Q.L g₁ (𝟙 Q.A) :=
    lamEq_baseChange _ _ (spMap s) F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A φ φ φ' φ
      hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 a₀ b₀ g₀ (𝟙 _) a₁ b₁ g₁ (𝟙 _)
      ea eb eg (by simp) hlam₀
  have hweil := weilEq_of_lamEq hL ℂ Q Q Q' Q a₁ b₁ g₁ (𝟙 _) ha₁ hb₁ hg₁ inferInstance hlam₁
  have hherm := (weilEq_iff_hermForm_eq hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA a₁ b₁ g₁ (𝟙 _) Φ₁ Φ₂ G
    LinearMap.id hΦ₁ hΦ₂ hG (fun z => by simp)).1 hweil
  have e₁ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' ea hΦd₁ (da M₁ hM₁ c')
  have e₂ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' eb hΦd₂ (db M₂ hM₂ c)
  have e₃ := map_comb s hφ.2.1 hφ.2.1 u u F.basis.1 F.basis.1 hW hW t₁ eg hGd (dg N hN c')
  rw [form_eq h' s Hm' W' _ hform', form_eq h s Hm W _ hform, ← e₁, ← e₂, ← e₃, hherm, LinearMap.id_apply]

theorem gram_images : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
  [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol) (FB : GenFib B.pol)
  (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) (f₁ f₂ : A.t.G ⟶ B.t.G)
  (M₁ M₂ : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) (g : 𝓞 E), FA.IsHerm hA → FB.IsHerm hB →
  IsMonHom f₁ → IsMonHom f₂ →
  WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
  FA.IsDiffOf FB f₁ M₁ → FA.IsDiffOf FB f₂ M₂ → ∀ (τ : 𝓞 E →+* 𝓞 K) (s : K →+* ℂ),
  ∀ c ∈ FA.eigLat A.t.act τ, hB.form s (M₂ c) (M₁ c) = s (τ g : K) * hA.form s c c := by
  intro hU hL E _ _ _ H K _ _ σ₁ A B FA FB hA hB f₁ f₂ M₁ M₂ g hhA hhB hf₁ hf₂ hw hM₁ hM₂ τ s c hc
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K A.pol FA (𝓞 E) A.t.act
  have hg : IsMonHom (A.t.act.act g) := A.t.act.hom _
  have hinj : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hlam := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol f₁ f₂ (A.t.act.act g) (𝟙 _) hf₁ hf₂ hg inferInstance ℂ
    (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hinj hw
  have hf := form_diff_eq_pair hU hL K A.pol FA B.pol FB hA hB f₁ f₂ (A.t.act.act g) M₁ M₂ (r g) hhA hhB hf₁ hf₂ hg
    hlam hM₁ hM₂ (hr _) s c c
  have hev : r g c = (τ g : K) • c := ((he τ c).1.1 hc).2 _
  rw [hf]
  erw [hev]
  rw [HermFam.smul_right]

theorem side (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {K : Type} [Field K] [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol)
    (FB : GenFib B.pol) (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) {n : ℕ}
    (f : Fin n → (A.t.G ⟶ B.t.G)) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
    (g : Matrix (Fin n) (Fin n) (𝓞 E)) (τ : 𝓞 E →+* 𝓞 K) (Ω : ℝ) (hhA : FA.IsHerm hA) (hhB : FB.IsHerm hB)
    (hf : ∀ a, IsMonHom (f a))
    (hw : ∀ a b, WeilEq B.t.PP.L (f a) (f b) A.t.PP.L (A.t.act.act (g a b)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    (hM : ∀ a, FA.IsDiffOf FB (f a) (M a)) (hr : latRank K (FA.eigLat A.t.act τ) = 1)
    (hi : ∀ a, Function.Injective (M a))
    (hind : iSupIndep (fun a => Submodule.span K
      (((FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set (Fin FB.P₀.g → K))))
    (hΩ : 2 * deg hA (FA.eigLat A.t.act τ) = Ω) :
    g.det ≠ 0 ∧ deg hB (⨆ a, (FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K))) =
      n * (Ω / 2) - Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  set y : Matrix (Fin n) (Fin n) K := g.map fun x => (τ x : K) with hy
  have hgr : ∀ (s : K →+* ℂ) a b, ∀ c ∈ FA.eigLat A.t.act τ,
      hB.form s (M b c) (M a c) = s (y a b) * hA.form s c c := fun s a b c hc =>
    gram_images hU hL E H K σ₁ A B FA FB hA hB (f a) (f b) (M a) (M b) (g a b) hhA hhB (hf a) (hf b) (hw a b)
      (hM a) (hM b) τ s c hc
  obtain ⟨hne, hdeg⟩ := GlobalTheory.T.deg_iSup_map_rankOne_lattice_of_gram K _ _ hA hB n M _ y (GlobalTheory.CM.DegBound.eigLat_fg FA A.t.act τ) hr hi hind hgr
  have hdet : y.det = ((τ g.det : 𝓞 K) : K) := by
    rw [hy, show (fun x : 𝓞 E => (τ x : K)) = ⇑((algebraMap (𝓞 K) K).comp τ) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    rfl
  refine ⟨fun h0 => hne (by rw [hdet, h0, map_zero]; rfl), ?_⟩
  have hn := GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq E K τ g.det
  rw [hdeg, ← hΩ, hdet]
  have e : (∑ s : K →+* ℂ, Real.log ‖s ((τ g.det : 𝓞 K) : K)‖) / (2 * (Module.finrank ℚ K : ℝ)) =
      Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * (Module.finrank ℚ E : ℝ)) := by
    rw [mul_comm (2 : ℝ), ← div_div, hn, div_div, mul_comm]
  rw [e]
  ring

theorem deg_images : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  intro hC hU hL hE E _ _ _ H K _ _ ρ σ₁ p q X _ χ hχ gP gQ hG FP FQ FB MP MQ hDf h hh τ hτ
  have hD : DegSt := PureDeg.degSt hC hU hL hE
  obtain ⟨hP, hhP⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FP).1
  obtain ⟨hQ, hhQ⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FQ).1
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτ' : (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) H.rt = -ρ := by
    have e : (H.bar : 𝓞 E →+* 𝓞 E) H.rt = -H.rt := by simp
    rw [RingHom.comp_apply, e, map_neg, hτ]
  have hne : -ρ ≠ ρ := fun e => hρ (by
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero)
  let FA : ∀ b, GenFib (X.A b).pol := fun b => Bool.rec (motive := fun b => GenFib (X.A b).pol) FQ FP b
  let M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun j =>
    Sum.rec (motive := fun j => (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) MP MQ j
  have hM : ∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j) := by
    rintro (a | a)
    exacts [hDf.1 a, hDf.2 a]
  obtain ⟨-, -, hinj, hind, -⟩ := Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  have hrP := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ
  have hrQ := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) FQ 0 1 X.split X.typeM X.ρ_sq).1 (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))
  rw [if_pos hτ] at hrP
  rw [if_neg (by rw [hτ']; exact hne)] at hrQ
  have hΩP : 2 * deg hP (FP.eigLat (X.A true).t.act τ) = (logOm E χ).re := by
    have := hD E H χ hχ K ρ (X.A true) X.split X.ρ_sq X.typeP FP hP hhP τ hτ
    rw [← this, Complex.ofReal_re]
  have hΩQ := NumInh.deg_conjugate_type hD hχ X FQ hhQ hτ'
  have hindP := iSupIndep.comp (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin q), τ)) hind
    (fun a b e => Sum.inl_injective (congrArg Prod.fst e))
  have hindQ := iSupIndep.comp (f := fun a : Fin q => ((Sum.inr a : Fin p ⊕ Fin q), τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) hind
    (fun a b e => Sum.inr_injective (congrArg Prod.fst e))
  obtain ⟨h1, h2⟩ := side hU hL σ₁ (X.A true) X.B FP FB hP h (fun a => phiP X a) MP gP τ _ hhP hh
    (fun a => (X.lin (Sum.inl a)).1) hG.1 hDf.1 hrP (fun a => hinj (Sum.inl a)) hindP hΩP
  obtain ⟨h3, h4⟩ := side hU hL σ₁ (X.A false) X.B FQ FB hQ h (fun a => phiQ X a) MQ gQ
    (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) _ hhQ hh (fun a => (X.lin (Sum.inr a)).1) hG.2 hDf.2 hrQ
    (fun a => hinj (Sum.inr a)) hindQ hΩQ
  exact ⟨h1, h3, h2, h4⟩

end GlobalTheory.FlatCM.ImageDeg

end
