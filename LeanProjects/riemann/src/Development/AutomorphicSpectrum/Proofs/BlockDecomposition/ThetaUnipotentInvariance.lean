import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.GENSL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalWhittakerUnipotentCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetFinAtMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedThetaValueIndicator
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaUnipotent

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rW_shift (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (a b c d x : F)
    (hc0 : c = 0 → a * d = 1) (Φ : E → ℂ) (z : E) :
    GL2LocalData.rW χ σ μE lam (a + x * c) (b + x * d) c d Φ z =
      (χ (x * Algebra.norm F z) : ℂ) * GL2LocalData.rW χ σ μE lam a b c d Φ z := by
  by_cases hc : c = 0
  · have had := hc0 hc
    subst hc
    have h1 : a * (b + x * d) * Algebra.norm F z = x * Algebra.norm F z + a * b * Algebra.norm F z := by
      linear_combination (x * Algebra.norm F z) * had
    simp only [GL2LocalData.rW, if_true, mul_zero, add_zero]
    rw [h1, AddChar.map_add_eq_mul]
    push_cast
    ring
  · have hk : ∀ u : E,
        ((χ (((a + x * c) * Algebra.norm F z + d * Algebra.norm F u -
            Algebra.trace F E (σ z * u)) / c) : Circle) : ℂ) * Φ u =
          (χ (x * Algebra.norm F z) : ℂ) * (((χ ((a * Algebra.norm F z + d * Algebra.norm F u -
            Algebra.trace F E (σ z * u)) / c) : Circle) : ℂ) * Φ u) := by
      intro u
      have h2 : ((a + x * c) * Algebra.norm F z + d * Algebra.norm F u -
            Algebra.trace F E (σ z * u)) / c =
          x * Algebra.norm F z + (a * Algebra.norm F z + d * Algebra.norm F u -
            Algebra.trace F E (σ z * u)) / c := by
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul]
      push_cast
      ring
    simp only [GL2LocalData.rW, if_neg hc, hk]
    rw [integral_const_mul]
    ring

theorem entries (x : F) (g : GL (Fin 2) F) :
    (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 ∧ (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 ∧
      (uni2 x * g).val 1 0 = g.val 1 0 ∧ (uni2 x * g).val 1 1 = g.val 1 1 := by
  rw [GlobalTheory.CompanionTheory.WeilPsi.unipotent_mul_val_real]
  simp

theorem corner (g : GL (Fin 2) F) :
    g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
  have hΔ : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g.val).1 g.isUnit).ne_zero
  intro h0
  have hC : g.val 1 0 = 0 := by
    rcases div_eq_zero_iff.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 hΔ
  have hD : (g.val).det = g.val 0 0 * g.val 1 1 := by
    rw [Matrix.det_fin_two g.val, hC]
    ring
  rw [div_mul_eq_mul_div, ← hD]
  exact div_self hΔ

theorem field_weil_action_unipotent (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μE : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ)
    (x : F) (g : GL (Fin 2) F) (Φ : E → ℂ) (z : E) :
    GL2LocalData.piG χ σ μE lam c (uni2 x * g) Φ z =
      (χ (x * Algebra.norm F z) : ℂ) * GL2LocalData.piG χ σ μE lam c g Φ z := by
  have hdet := GlobalTheory.CompanionTheory.WeilPsi.det_left_unipotent_mul x g
  obtain ⟨e00, e01, e10, e11⟩ := entries x g
  unfold GL2LocalData.piG
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have h' : ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_pos h', dif_pos h]
    have hch : h'.choose = h.choose := GlobalTheory.CompanionTheory.WeilPsi.choose_congr (by simp only [hdet]) h' h
    have hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det =
        g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
      ring
    rw [hch, hdet, e00, e01, e10, e11, hsplit, rW_shift χ σ μE lam _ _ _ _ x (corner g)]
    ring
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((uni2 x * g).val).det := by rwa [hdet]
    rw [dif_neg h', dif_neg h, mul_zero]

end Local

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem split_weil_action_unipotent (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (x : F) (g : GL (Fin 2) F) (Φ : F × F → ℂ)
    (z : F × F) :
    GL2LocalData.piS χ c₁ (uni2 x * g) Φ z =
      (χ (x * Algebra.norm F z) : ℂ) * GL2LocalData.piS χ c₁ g Φ z := by
  have hdet := GlobalTheory.CompanionTheory.WeilPsi.det_left_unipotent_mul x g
  obtain ⟨e00, e01, e10, e11⟩ := entries x g
  have hD : Matrix.GeneralLinearGroup.det (uni2 x * g) = Matrix.GeneralLinearGroup.det g := by
    apply Units.ext
    simpa using hdet
  have hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det =
      g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
    ring
  unfold GL2LocalData.piS
  rw [hD, hdet, e00, e01, e10, e11, hsplit, rW_shift χ _ _ 1 _ _ _ _ x (corner g)]
  ring

theorem norm_prod (y : F × F) : Algebra.norm F y = y.1 * y.2 := by
  rw [Algebra.norm_eq_matrix_det (Module.Basis.finTwoProd F), Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul]

end Split

section Real

theorem rWR_shift (a b c d x : ℝ) (hc0 : c = 0 → a * d = 1) (Φ : ℂ → ℂ) (z : ℂ) :
    rWR (a + x * c) (b + x * d) c d Φ z =
      GlobalTheory.CompanionTheory.GlobalWhittakerPsi.eC (x * Complex.normSq z) * rWR a b c d Φ z := by
  unfold rWR
  by_cases hc : c = 0
  · have had := hc0 hc
    subst hc
    have e : a * (b + x * d) * Complex.normSq z = a * b * Complex.normSq z + x * Complex.normSq z := by
      linear_combination (x * Complex.normSq z) * had
    simp only [if_true, mul_zero, add_zero]
    rw [e, show (2 * (Real.pi : ℂ) * Complex.I * (((a * b * Complex.normSq z + x * Complex.normSq z : ℝ)) : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((a * b * Complex.normSq z : ℝ) : ℂ) +
        2 * (Real.pi : ℂ) * Complex.I * ((x * Complex.normSq z : ℝ) : ℂ) by push_cast; ring, Complex.exp_add]
    simp only [GlobalTheory.CompanionTheory.GlobalWhittakerPsi.eC]
    ring
  · rw [if_neg hc, if_neg hc]
    have hint : ∀ u : ℂ, Complex.exp (2 * Real.pi * Complex.I *
        ((((a + x * c) * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c : ℝ) : ℂ)) * Φ u =
        GlobalTheory.CompanionTheory.GlobalWhittakerPsi.eC (x * Complex.normSq z) * (Complex.exp (2 * Real.pi * Complex.I *
        (((a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c : ℝ) : ℂ)) * Φ u) := by
      intro u
      have e : ((a + x * c) * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c =
          x * Complex.normSq z + (a * Complex.normSq z + d * Complex.normSq u - 2 * (conj z * u).re) / c := by
        field_simp
        ring
      rw [e, ← mul_assoc, GlobalTheory.CompanionTheory.GlobalWhittakerPsi.eC, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    simp only [hint]
    rw [integral_const_mul]
    ring

theorem real_weil_action_unipotent (cf : ℂˣ → ℂ) (x : ℝ) (g : GL (Fin 2) ℝ) (Φ : ℂ → ℂ) (z : ℂ) :
    piRc cf (uni2 x * g) Φ z =
      GlobalTheory.CompanionTheory.GlobalWhittakerPsi.eC (x * Complex.normSq z) * piRc cf g Φ z := by
  have hv := GlobalTheory.CompanionTheory.GlobalWhittakerPsi.unipotent_mul_val_real x g
  have hdet : ((uni2 x * g).val).det = (g.val).det := by
    rw [hv, Matrix.det_fin_two_of, Matrix.det_fin_two]
    ring
  unfold piRc
  by_cases h : 0 < (g.val).det
  · have h' : 0 < ((uni2 x * g).val).det := hdet ▸ h
    rw [dif_pos h', dif_pos h]
    simp only [hdet]
    have e00 : (uni2 x * g).val 0 0 = g.val 0 0 + x * g.val 1 0 := by rw [hv]; simp
    have e01 : (uni2 x * g).val 0 1 = g.val 0 1 + x * g.val 1 1 := by rw [hv]; simp
    have e10 : (uni2 x * g).val 1 0 = g.val 1 0 := by rw [hv]; simp
    have e11 : (uni2 x * g).val 1 1 = g.val 1 1 := by rw [hv]; simp
    have hsplit : (g.val 0 0 + x * g.val 1 0) / (g.val).det =
        g.val 0 0 / (g.val).det + x * (g.val 1 0 / (g.val).det) := by
      ring
    have hc0 : g.val 1 0 / (g.val).det = 0 → g.val 0 0 / (g.val).det * g.val 1 1 = 1 := by
      intro h0
      have hC : g.val 1 0 = 0 := by
        rcases div_eq_zero_iff.1 h0 with h1 | h1
        · exact h1
        · exact absurd h1 h.ne'
      have hD : (g.val).det = g.val 0 0 * g.val 1 1 := by
        rw [Matrix.det_fin_two g.val, hC]
        ring
      rw [div_mul_eq_mul_div, ← hD]
      exact div_self h.ne'
    rw [e00, e01, e10, e11, hsplit, rWR_shift _ _ _ _ x hc0]
    ring
  · have h' : ¬ 0 < ((uni2 x * g).val).det := hdet ▸ h
    rw [dif_neg h', dif_neg h, mul_zero]

end Real

section Places

variable {K : Type} [Field K] [NumberField K]

theorem algebraMap_rat_eq {R : Type} [Field R] [CharZero R] (inst : Algebra ℚ R) (q : ℚ) :
    @algebraMap ℚ R _ _ inst q = (q : R) :=
  eq_ratCast (@algebraMap ℚ R _ _ inst) q

theorem norm_ns (v : Pl) (w : PlK K) [i : w.asIdeal.LiesOver v.asIdeal]
    (hu : ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) (ξ : K) :
    Algebra.norm (Qv v) (algebraMap K (Kv K w) ξ) = algebraMap ℚ (Qv v) (Algebra.norm ℚ ξ) := by
  classical
  have h := SemiLocal.algebraMap_norm_eq_prod (K := ℚ) (L := K) v ξ
  haveI : Subsingleton (SemiLocal.PlacesOver K v) :=
    ⟨fun a b => Subtype.ext ((hu a.1 a.2).trans (hu b.1 b.2).symm)⟩
  rw [Fintype.prod_subsingleton _ (⟨w, i⟩ : SemiLocal.PlacesOver K v)] at h
  refine h.symm.trans ?_
  rw [algebraMap_rat_eq, algebraMap_rat_eq]

theorem norm_sp (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [i₁ : w₁.asIdeal.LiesOver v.asIdeal] [i₂ : w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) (ξ : K) :
    dg1 v w₁ ξ * dg1 v w₂ ξ = algebraMap ℚ (Qv v) (Algebra.norm ℚ ξ) := by
  classical
  obtain ⟨hall, d₁, d₂⟩ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_split h2 v w₁ w₂ hne
  have h := SemiLocal.algebraMap_norm_eq_prod (K := ℚ) (L := K) v ξ
  have hab : (⟨w₁, i₁⟩ : SemiLocal.PlacesOver K v) ≠ ⟨w₂, i₂⟩ := fun e => hne (congrArg Subtype.val e)
  have huniv : (Finset.univ : Finset (SemiLocal.PlacesOver K v)) = {⟨w₁, i₁⟩, ⟨w₂, i₂⟩} := by
    ext u
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hall u.1 u.2 with e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Subtype.ext e)
  rw [huniv, Finset.prod_pair hab] at h
  have one : ∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], Module.finrank (Qv v) (Kv K w) = 1 →
      Algebra.norm (Qv v) (algebraMap K (Kv K w) ξ) = dg1 v w ξ := by
    intro w _ d
    have e : algebraMap (Qv v) (Kv K w) (dg1 v w ξ) = algebraMap K (Kv K w) ξ :=
      Function.invFun_eq ((GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.algebraMap_bijective v w d).2 _)
    rw [← e, Algebra.norm_algebraMap, d, pow_one]
  rw [← one w₁ d₁, ← one w₂ d₂]
  refine h.symm.trans ?_
  rw [algebraMap_rat_eq, algebraMap_rat_eq]

theorem local_theta_value_unipotent (h2 : Module.finrank ℚ K = 2) {c : HeckeCharacter K} {v : Pl} (m : LM c v) (hok : m.ok)
    (x : Qv v) (g : GL (Fin 2) (Qv v)) (ξ : K) :
    m.val (uni2 x * g) ξ =
      (((GP.psiF v)⁻¹ (x * algebraMap ℚ (Qv v) (Algebra.norm ℚ ξ)) : Circle) : ℂ) * m.val g ξ := by
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ =>
    simp only [LM.val]
    rw [split_weil_action_unipotent, norm_prod]
    simp only
    rw [norm_sp h2 v w₁ w₂ hok.1]
  | @ns w i σ η Φ =>
    simp only [LM.val]
    rw [field_weil_action_unipotent, norm_ns v w hok.1]

end Places

section Global

variable {K : Type} [Field K] [NumberField K]

end Global

end GlobalTheory.CompanionTheory.ThetaUnipotent
