import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import Development.AutomorphicArithmetic.AdelicQuotients.OneLeEntryBoundOfBorelDiagonalDecomp
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsLowerEntryNeZeroOfNormCharpolyIrreducible
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing TensorProduct

private theorem real_fix {A : Type*} [NormedField A] [CharZero A] (e ψ : A →+* ℂ) (he : Isometry e) (hψ : Continuous ψ)
    (x : A) (s : ℝ) (hx : e x = (s : ℂ)) : ψ x = (s : ℂ) := by
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.1 (Rat.denseRange_cast (𝕜 := ℝ) s)
  choose u hu using hq
  have h1 : Filter.Tendsto (fun k => ((u k : ℚ) : ℂ)) Filter.atTop (nhds (s : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto s).comp hlim
    refine this.congr fun k => ?_
    simp [← hu k]
  have h2 : Filter.Tendsto (fun k => ((u k : ℚ) : A)) Filter.atTop (nhds x) := by
    rw [he.isEmbedding.isInducing.tendsto_nhds_iff, hx]
    refine h1.congr fun k => ?_
    simp
  have h3 := (hψ.tendsto x).comp h2
  refine tendsto_nhds_unique h3 (h1.congr fun k => ?_)
  simp

private theorem ext_pos {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    InfinitePlace.Completion.extensionEmbedding w (((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 w) = (ρ : ℂ) := by
  rw [← IdeleGroup.coe_infiniteProj, infiniteProj_posIdele]
  show InfinitePlace.Completion.extensionEmbedding w (posRealElem w (ρ ^ w.mult)) = _
  unfold posRealElem
  split_ifs with hw
  · have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hm, pow_one,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply]
  · have hm : w.mult = 2 := by simp [InfinitePlace.mult, hw]
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply
      (InfinitePlace.not_isReal_iff_isComplex.1 hw), RingEquiv.apply_symm_apply, hm,
      Real.sqrt_sq hρ.le]

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem map_pos' (s : ℝ) (hs : 0 < s) :
    adeleMap F E ((posIdele (K := F) s hs : IdeleGroup F) : 𝔸[F]) = ((posIdele (K := E) s hs : IdeleGroup E) : 𝔸[E]) := by
  refine Prod.ext (funext fun w => ?_) ?_
  · apply (InfinitePlace.Completion.extensionEmbedding w).injective
    rw [ext_pos]
    change InfinitePlace.Completion.extensionEmbedding w
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) ((posIdele (K := F) s hs : IdeleGroup F) : 𝔸[F]).1 w) = _
    rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply]
    have := GroundTheory.Global.InfinitePlace.liesOver_comap (K := F) w
    have : CharZero (w.comap (algebraMap F E)).Completion := algebraRat.charZero _
    exact real_fix (InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)))
      ((InfinitePlace.Completion.extensionEmbedding w).comp NumberField.LiesOver.completionMap)
      (InfinitePlace.Completion.isometry_extensionEmbedding _)
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        NumberField.LiesOver.continuous_completionMap) _ s (ext_pos s hs _)
  · have h1 : ((posIdele (K := F) s hs : IdeleGroup F) : 𝔸[F]).2 = 1 := by
      refine DFunLike.ext _ _ fun v => ?_
      exact posIdele_finite s hs v
    have h2 : ((posIdele (K := E) s hs : IdeleGroup E) : 𝔸[E]).2 = 1 := by
      refine DFunLike.ext _ _ fun v => ?_
      exact posIdele_finite s hs v
    rw [h2]
    change finiteAdeleMap F E ((posIdele (K := F) s hs : IdeleGroup F) : 𝔸[F]).2 = 1
    rw [h1, map_one]

private theorem galAd_apply (σ : E ≃ₐ[F] E) (y : 𝔸[E]) : galAd σ y = σ • y := by
  have h : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
    refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
      rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
      rfl
    · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
        ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
      rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
        smul_adeleMap, map_one, map_one, one_mul]
      rfl
  rw [h]
  rfl

private theorem cont_gal (σ : E ≃ₐ[F] E) (n : ℕ) :
    Continuous (mapGL n (galAd σ) : AdelicGLn.AdelicGL E n → AdelicGLn.AdelicGL E n) := by
  have h : Continuous (galAd σ) := by
    rw [show (galAd σ : 𝔸[E] → 𝔸[E]) = fun y => σ • y from funext (galAd_apply σ)]
    exact continuous_const_smul σ
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map h
  · exact Units.continuous_coe_inv.matrix_map h

private theorem gal_diag (σ : E ≃ₐ[F] E) (n : ℕ) (h : GL (Fin n) E) :
    mapGL n (galAd σ) (AdelicGLn.diagonal E n h) = AdelicGLn.diagonal E n (sigmaGL σ h) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change galAd σ (algebraMap E 𝔸[E] (h.1 i j)) = algebraMap E 𝔸[E] (σ (h.1 i j))
  rw [galAd_apply, AdeleBaseChange.smul_algebraMap]

private theorem gal_torus (σ : E ≃ₐ[F] E) (n : ℕ) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
    mapGL n (galAd σ) (diagUnits n (fun i => posIdele (K := E) (ρ i) (hρ i))) =
      diagUnits n (fun i => posIdele (K := E) (ρ i) (hρ i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change galAd σ (Matrix.diagonal (fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j) =
    Matrix.diagonal (fun i => ((posIdele (K := E) (ρ i) (hρ i) : IdeleGroup E) : 𝔸[E])) i j
  rw [Matrix.diagonal_apply]
  split_ifs
  · rw [← map_pos' (F := F), galAd_apply, smul_adeleMap]
  · exact map_zero _

private theorem gal_borel (σ : E ≃ₐ[F] E) (n : ℕ) (b : AdelicGLn.AdelicGL E n)
    (hb : b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL E n))) :
    mapGL n (galAd σ) b ∈ (adelicBorel : Subgroup (AdelicGLn.AdelicGL E n)) := by
  rw [mem_adelicBorel] at hb ⊢
  intro i j hij
  change galAd σ (b.1 i j) = 0
  rw [hb hij, map_zero]
end

private theorem ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {L : ℝ} (hL : 1 ≤ L)
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → ρ j ≤ L * ρ i ∧ ρ i ≤ L * ρ j) (i j : Fin n) : ρ i / ρ j ≤ L ^ n := by
  have hL0 : 0 < L := by linarith
  have hm : max 1 (L⁻¹)⁻¹ = L := by rw [inv_inv, max_eq_right hL]
  rw [div_le_iff₀ (hρ j)]
  rcases le_total (j : ℕ) i with hij | hij
  · have := CuspidalSpectrum.le_pow_mul_of_siegel (ρ := ρ) (t := L⁻¹) (inv_pos.2 hL0) hρ
      (fun a b hab => by rw [inv_mul_le_iff₀ hL0]; exact (h a b hab).1) (i - j) j i (by omega)
    rw [hm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) (hρ j).le)
  · have := CuspidalSpectrum.le_pow_mul_of_siegel (ρ := fun a => (ρ a)⁻¹) (t := L⁻¹) (inv_pos.2 hL0)
      (fun a => inv_pos.2 (hρ a))
      (fun a b hab => by
        rw [← mul_inv]; exact inv_anti₀ (hρ a) (h a b hab).2) (j - i) i j (by omega)
    rw [hm, inv_le_iff_one_le_mul₀' (hρ j), ← mul_assoc, ← div_eq_mul_inv, one_le_div (hρ i), mul_comm] at this
    exact this.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL (by omega)) (hρ j).le)

private theorem one_le_of_pow {x Q : ℝ} {d : ℕ} (hd : d ≠ 0) (hx : 0 ≤ x) (hQ : 1 ≤ Q) (h : 1 ≤ x ^ d * Q) : 1 ≤ x * Q := by
  rcases le_total x 1 with h1 | h1
  · exact h.trans (mul_le_mul_of_nonneg_right (pow_le_of_le_one hx h1 hd) (by linarith))
  · exact one_le_mul_of_one_le_of_one_le h1 hQ

private theorem numeric_product_inequality {c u v w M₁ M₂ M₃ Y : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (hv : 1 ≤ v) (hw : 1 ≤ w)
    (h1 : u ≤ M₁) (h2 : v ≤ c * c * M₃ * Y) (h3 : w ≤ M₂) :
    1 ≤ (c * (u * v * w)) ^ 2 ∧ (c * (u * v * w)) ^ 2 ≤ (c * (M₁ * (c * c * M₃) * M₂)) ^ 2 * Y ^ 2 := by
  refine ⟨one_le_pow₀ (one_le_mul_of_one_le_of_one_le hc (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hu hv) hw)), ?_⟩
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  calc c * (u * v * w) ≤ c * (M₁ * (c * c * M₃ * Y) * M₂) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul h1 h2 (by linarith) (by linarith)) h3 (by linarith)
          (mul_nonneg (by linarith) (by linarith))) (by linarith)
    _ = _ := by ring

private theorem numeric_degree_inequality {N T Q D Y H a b : ℝ} {d : ℕ} (hd : d ≠ 0) (hT : 0 < T) (ha : 0 < a) (hb : 0 < b) (hH : 1 ≤ H)
    (hHQ : H ≤ Q * Y ^ 2) (hD : N ^ 2 * T * Q ≤ D) (h : 1 ≤ (N ^ 2 * (T * (b / a))) ^ d * H) : a ≤ D * Y ^ 2 * b := by
  have h2 := one_le_of_pow hd (by positivity) hH h
  have h3 : 1 ≤ D * Y ^ 2 * b / a := by
    refine h2.trans ?_
    calc N ^ 2 * (T * (b / a)) * H ≤ N ^ 2 * (T * (b / a)) * (Q * Y ^ 2) :=
          mul_le_mul_of_nonneg_left hHQ (by positivity)
      _ = (N ^ 2 * T * Q) * (Y ^ 2 * b / a) := by ring
      _ ≤ D * (Y ^ 2 * b / a) := mul_le_mul_of_nonneg_right hD (by positivity)
      _ = _ := by ring
  rwa [one_le_div ha] at h3

open AutomorphicForm in
theorem UpperTheory.ConvolutionTheory.G.galois_twist_preserves_siegel_bound :
    G2 := by
  intro F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := E) n
  obtain ⟨M₁, hM₁⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hω
  obtain ⟨M₂, hM₂⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hω.image (cont_gal σ n))
  obtain ⟨M₃, hM₃⟩ := CuspidalSpectrum.exists_height_le_of_isCompact
    ((isCompact_maxCompact (K := E) (n := n)).image (cont_gal σ n))
  obtain ⟨C, hC0, hC⟩ := CuspidalSpectrum.exists_height_le_normOne hω
  set c := heightConst E n with hc
  have hc1 : 1 ≤ c := one_le_heightConst
  set T := max 1 t⁻¹ ^ (2 * n) with hT
  have hT0 : 0 < T := pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _
  set Q := (c * (M₁ * (c * c * M₃) * M₂)) ^ 2 with hQ
  set D := max (max 1 t⁻¹) ((n : ℝ) ^ 2 * T * Q) with hD
  have hD1 : 1 ≤ D := (le_max_left _ _).trans (le_max_left _ _)
  set e := 2 * Fintype.card (InfinitePlace E) with he
  refine ⟨C * D ^ (n * e), 2 * (n * e), ?_⟩
  intro μ _ θ hθ f Y hY hf hEll x hx
  obtain ⟨γ, hγ⟩ : ∃ γ : Gam E n, f (x⁻¹ * (γ : G1 E n) * θ.e x) ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hx (finsum_eq_zero_of_forall_eq_zero hne)
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : GL (Fin n) E, AdelicGLn.diagonal E n δ₀ = ((γ : G1 E n) : AdelicGLn.AdelicGL E n) := γ.2
  obtain ⟨g, b, hb, _, ⟨ρ, hρ, hρt, rfl⟩, k, hk, hg⟩ := hsieg (x : AdelicGLn.AdelicGL E n)
  set a := diagUnits n (fun i => posIdele (K := E) (ρ i) (hρ i)) with ha
  set y : G1 E n := x⁻¹ * (γ : G1 E n) * θ.e x with hy
  let g₁ : Gam E n := ⟨⟨AdelicGLn.diagonal E n g, rationalGL_le_normOneGL ⟨g, rfl⟩⟩, ⟨g, rfl⟩⟩
  set x' : G1 E n := (g₁ : G1 E n) * x with hx'
  have hx'v : (x' : AdelicGLn.AdelicGL E n) = AdelicGLn.diagonal E n g * x := rfl
  set δ : GL (Fin n) E := g * δ₀ * (sigmaGL σ g)⁻¹ with hδ
  have hyv : (y : AdelicGLn.AdelicGL E n) = (x' : AdelicGLn.AdelicGL E n)⁻¹ * AdelicGLn.diagonal E n δ *
      mapGL n (galAd σ) (x' : AdelicGLn.AdelicGL E n) := by
    rw [hx'v, hδ, map_mul, map_mul, map_mul, map_inv, gal_diag, hδ₀, ← hθ x, hy]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  obtain ⟨p, hp, hpc⟩ := hEll δ x' y hyv hγ
  have hyY := hf y hγ
  set m := k * (y : AdelicGLn.AdelicGL E n) * (mapGL n (galAd σ) k)⁻¹ with hm
  have hdec : AdelicGLn.diagonal E n δ = b * a * m * a⁻¹ * (mapGL n (galAd σ) b)⁻¹ := by
    rw [hm, hyv, hx'v, hg, map_mul (mapGL n (galAd σ)), map_mul (mapGL n (galAd σ)), ha, gal_torus]
    group
  have hb1 := hM₁ b hb
  have hb2 : AutomorphicForm.height (mapGL n (galAd σ) b)⁻¹ ≤ M₂ := by rw [height_inv]; exact hM₂ _ ⟨b, hb, rfl⟩
  have hk3 : AutomorphicForm.height (mapGL n (galAd σ) k)⁻¹ ≤ M₃ := by rw [height_inv]; exact hM₃ _ ⟨k, hk, rfl⟩
  have hM1 : 1 ≤ M₁ := (one_le_height _).trans hb1
  have hM3 : 1 ≤ M₃ := (one_le_height _).trans hk3
  have hm1 : AutomorphicForm.height m ≤ c * c * M₃ * Y := by
    have h1 : AutomorphicForm.height (k * (y : AdelicGLn.AdelicGL E n)) ≤ c * Y := by
      refine (height_mul_le _ _).trans ?_
      rw [height_eq_one_of_mem_maxCompact hk, mul_one]
      exact mul_le_mul_of_nonneg_left hyY (by linarith)
    refine (height_mul_le _ _).trans ?_
    calc c * AutomorphicForm.height (k * (y : AdelicGLn.AdelicGL E n)) * AutomorphicForm.height (mapGL n (galAd σ) k)⁻¹
        ≤ c * (c * Y) * M₃ := mul_le_mul (mul_le_mul_of_nonneg_left h1 (by linarith)) hk3 (height_pos _).le
          (mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith)))
      _ = _ := by ring
  obtain ⟨hH1, hHQ⟩ := numeric_product_inequality hc1 (one_le_height _) (one_le_height _) (one_le_height _) hb1 hm1 hb2
  have hY2 : 1 ≤ Y ^ 2 := one_le_pow₀ hY
  have hL : 1 ≤ D * Y ^ 2 := one_le_mul_of_one_le_of_one_le hD1 hY2
  have hrat := ratio_le hρ hL fun i j hij => by
    have hi := hρ i
    have hj := hρ j
    constructor
    · have h1 : ρ j ≤ t⁻¹ * ρ i := by rw [le_inv_mul_iff₀ ht]; exact hρt i j hij
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hi.le)
      exact ((le_max_right _ _).trans (le_max_left _ _)).trans (le_mul_of_one_le_right (by linarith) hY2)
    · have hr : 0 < (j : ℕ) := by omega
      have hi' : (⟨(j : ℕ) - 1, by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
      obtain ⟨i', j', hi'r, hj'r, hne⟩ := UpperTheory.exists_lower_entry_ne_zero_of_norm_charpoly_irreducible F E σ hσ n δ p hp hpc j hr j.2
      have h1 := UpperTheory.one_le_entry_bound_of_borel_diagonal_decomp E n δ b (mapGL n (galAd σ) b)⁻¹ m (hωB hb) (inv_mem (gal_borel σ n b (hωB hb))) ρ hρ j
        (T * (ρ j / ρ i)) (mul_pos hT0 (div_pos hj hi)) (fun u v hu hv => by
          have := CuspidalSpectrum.div_le_of_siegel ht hρ hρt hr j.2 (i := u) (j := v) ⟨hu, hv⟩
          rwa [hi'] at this) hdec i' j' hi'r hj'r hne
      exact numeric_degree_inequality Module.finrank_pos.ne' hT0 hi hj hH1 hHQ (le_max_right _ _) h1
  have hfin := hC b hb ρ hρ k hk x' x'.2 (hx'v.trans hg) _ (one_le_pow₀ hL) hrat
  have hq : qht x ≤ AutomorphicForm.height (x' : AdelicGLn.AdelicGL E n) :=
    ciInf_le (f := fun γ : Gam E n => AutomorphicForm.height (((γ : G1 E n) * x : G1 E n) : AdelicGLn.AdelicGL E n))
      ⟨1, by rintro _ ⟨γ, rfl⟩; exact one_le_height _⟩ g₁
  refine (hq.trans hfin).trans (le_of_eq ?_)
  rw [← pow_mul, mul_pow, ← pow_mul, mul_assoc]
