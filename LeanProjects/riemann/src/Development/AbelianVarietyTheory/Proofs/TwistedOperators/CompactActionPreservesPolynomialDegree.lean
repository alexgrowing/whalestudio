import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwiner
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHoldsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialIsoUnitaryPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalFockIntertwinerRealPlaceOfCoverContraStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotLocallyFiniteQuadraticMulAddDegreeNonraisingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSourceGlActionEqQuadraticAddNonRaisingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockTargetGlActionEqQuadraticAddNonRaisingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfGeneratorOneParameterGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemMaximalCompactOfMapsFockVectorToFockStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubstitutionTotalDegreeLeStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SourceOperatorLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

variable {n : ℕ}

theorem exp_add_smul (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem exp_mem_K {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Formalism.REAL.inK ε Y) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ Formalism.REAL.Kset ε := by
  have h1 : Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0 := hY.1
  have h2 : Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y := hY.2
  have h3 : Yᴴ = -Y := by
    have h4 : (Yᴴ + Y) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 0 := by
      rw [Matrix.add_mul, h2, h1, Matrix.zero_mul]
    rw [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h4
    exact eq_neg_of_add_eq_zero_left h4
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, h3, star_trivial, smul_neg, ← neg_smul, ← exp_add_smul, neg_add_cancel, zero_smul,
      NormedSpace.exp_zero]
  · exact (Commute.exp_left (Commute.smul_left (show Commute Y (Formalism.REAL.Jm ε) from h2) t)).eq

theorem conj_mem {ε : Fin n → Bool} {fr G k : Matrix (Fin n) (Fin n) ℂ} (hfr : IsUnit fr)
    (hG : frᴴ * Formalism.REAL.Jm ε * fr = G) (hk : k ∈ Formalism.REAL.Kset ε) : fr⁻¹ * k * fr ∈ Formalism.QuantumDeterminants.UH G := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have e1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have e2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e3 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff'.1 hk.1)
  have e4 : k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k := hk.2
  show (fr⁻¹ * k * fr)ᴴ * G * (fr⁻¹ * k * fr) = G
  calc (fr⁻¹ * k * fr)ᴴ * G * (fr⁻¹ * k * fr)
      = frᴴ * (kᴴ * (((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) * k)) * fr := by
        rw [← hG]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one, ← e4, ← Matrix.mul_assoc kᴴ, e3, Matrix.one_mul, hG]

theorem compact_path {ε : Fin n → Bool} {fr G k : Matrix (Fin n) (Fin n) ℂ} (hfr : IsUnit fr)
    (hG : frᴴ * Formalism.REAL.Jm ε * fr = G) (hk : k ∈ Formalism.REAL.Kset ε) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧ NormedSpace.exp ((1 : ℝ) • X) = fr⁻¹ * k * fr ∧
      ∀ t : ℝ, ∃ k' ∈ Formalism.REAL.Kset ε, NormedSpace.exp (t • X) = fr⁻¹ * k' * fr := by
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have e1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have e2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have h1 : Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y = 0 := hY.1
  have key : ∀ t : ℝ, NormedSpace.exp (t • (fr⁻¹ * Y * fr)) = fr⁻¹ * NormedSpace.exp (t • Y) * fr := by
    intro t
    rw [← Matrix.exp_conj' fr (t • Y) hfr, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fr⁻¹ * Y * fr, ?_, ?_, fun t => ⟨_, exp_mem_K hY t, key t⟩⟩
  · calc (fr⁻¹ * Y * fr)ᴴ * G + G * (fr⁻¹ * Y * fr)
        = frᴴ * (Yᴴ * (((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε) + Formalism.REAL.Jm ε * ((fr * fr⁻¹) * Y)) * fr := by
          rw [← hG]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
      _ = 0 := by rw [e1, e2, Matrix.one_mul, Matrix.one_mul, h1, Matrix.mul_zero, Matrix.zero_mul]
  · rw [key, one_smul, hexp]

theorem one_mem_K (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
  ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

end Mat

theorem not_locFin {σ : Type} [Finite σ] {A : Module.End ℂ (MvPolynomial σ ℂ)} (c : ℂ)
    (h : ∃ (Q : MvPolynomial σ ℂ) (L : Module.End ℂ (MvPolynomial σ ℂ)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧
      (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ A = LinearMap.mulLeft ℂ Q + L)
    (φ : MvPolynomial σ ℂ) (hφ : φ ≠ 0) (F : Submodule ℂ (MvPolynomial σ ℂ)) (hF : FiniteDimensional ℂ F) :
    ¬ ∀ m : ℕ, ((A + c • 1) ^ m) φ ∈ F := by
  obtain ⟨Q, L, hQ, hh, hL, rfl⟩ := h
  rw [add_assoc]
  refine GlobalTheory.T.not_locallyFinite_quadraticMul_add_degreeNonraising σ Q (L + c • 1) hQ hh (fun P => ?_) φ hφ F hF
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hL P) (MvPolynomial.totalDegree_smul_le c P))

variable {D : D7}

theorem span_bound {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (l : (⨂[ℂ] τ, M.H τ) →ₗ[ℂ] ℂ)
    (hl : l ∈ Submodule.span ℂ (Set.range (ellT M))) :
    ∃ c : ℝ, ∀ v : ∀ τ, M.H τ, ‖l (PiTensorProduct.tprod ℂ v)‖ ≤ c * ∏ τ, ‖v τ‖ := by
  induction hl using Submodule.span_induction with
  | mem l hl =>
    obtain ⟨w, rfl⟩ := hl
    refine ⟨∏ τ, ‖w τ‖, fun v => ?_⟩
    have : ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, inner ℂ (w τ) (v τ) := by simp [ellT]
    rw [this, norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ _ => norm_inner_le_norm _ _
  | zero => exact ⟨0, fun v => by simp⟩
  | add l l' _ _ h h' =>
    obtain ⟨c, hc⟩ := h
    obtain ⟨c', hc'⟩ := h'
    refine ⟨c + c', fun v => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hc v) (hc' v))
  | smul a l _ h =>
    obtain ⟨c, hc⟩ := h
    refine ⟨‖a‖ * c, fun v => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hc v) (norm_nonneg _)

theorem span_deriv {E Z : Type} [AddCommGroup E] [Module ℂ E] (e : Z → E →ₗ[ℂ] ℂ) (c : ℝ → E) (y : E)
    (h : ∀ z, HasDerivAt (fun t => e z (c t)) (e z y) 0) (l : E →ₗ[ℂ] ℂ)
    (hl : l ∈ Submodule.span ℂ (Set.range e)) : HasDerivAt (fun t => l (c t)) (l y) 0 := by
  induction hl using Submodule.span_induction with
  | mem l hl => obtain ⟨z, rfl⟩ := hl; exact h z
  | zero => exact hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add l l' _ _ h h' => exact h.fun_add h'
  | smul a l _ h => exact h.const_mul a

theorem elt_one {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel V S)
    (τ : D.what₂.Tau) : elt θ M τ 1 = 1 := by
  unfold elt
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

section Main

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {θ : InfFam D}
  {ψ : AddChar (AF D.host.F) ℂ} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
  {aS aT : D.what₂.Tau → ℚ} {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
  {I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ}

abbrev ptL (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) :
    PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) :=
  pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f

theorem srcOp_apply (τ : D.what₂.Tau) (a : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank) :
    srcOp M M' τ a X P = fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P -
      ((a : ℂ) * X.trace) • P := by
  unfold srcOp
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul, sub_eq_add_neg]

theorem hasDerivAt_lieAction_source_operator {τ : D.what₂.Tau} {a b : ℚ} (h : LieFock ψ θ M M' ω f τ a b) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (P : PolF D W.rank V.rank) (z : WO V W) :
    HasDerivAt (fun t : ℝ => ω (atTau θ V τ (NormedSpace.exp (t • X)), 1) (ptL ψ θ M M' f P) z)
      (ptL ψ θ M M' f (srcOp M M' τ b X P) z) 0 := by
  rw [srcOp_apply]
  exact h.1 X hX P z

theorem lie_tgt {τ : D.what₂.Tau} {a b : ℚ} (h : LieFock ψ θ M M' ω f τ a b) {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hY : Y ∈ lieAt W τ) (P : PolF D W.rank V.rank) (z : WO V W) :
    HasDerivAt (fun t : ℝ => ω (1, atTau θ W τ (NormedSpace.exp (t • Y))) (ptL ψ θ M M' f P) z)
      (ptL ψ θ M M' f (tgtOp M M' τ a Y P) z) 0 :=
  h.2 Y hY P z

theorem compact_action_preserves_polynomial_degree (hθ : IsInfFam θ) {τ : D.what₂.Tau} {a b : ℚ} (h : CompactFock ψ θ M M' ω f τ a b)
    (k : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : k ∈ Formalism.REAL.Kset (M.ε τ)) (P : PolF D W.rank V.rank) :
    ∃ Q : PolF D W.rank V.rank, Q.totalDegree ≤ P.totalDegree ∧
      ω (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ), 1) (ptL ψ θ M M' f P) = ptL ψ θ M M' f Q := by
  obtain ⟨x, y, -, -, h⟩ := h
  have := h k hk 1 (one_mem_K _) P
  rw [elt_one hθ M'] at this
  refine ⟨_, ?_, this.trans (map_smul (ptL ψ θ M M' f) _ _).symm⟩
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.T.substitution_total_degree_le D _ _ τ _ _ _ _ P)

theorem cpt_tgt (hθ : IsInfFam θ) {τ : D.what₂.Tau} {a b : ℚ} (h : CompactFock ψ θ M M' ω f τ a b)
    (k : Matrix (Fin W.rank) (Fin W.rank) ℂ) (hk : k ∈ Formalism.REAL.Kset (M'.ε τ)) (P : PolF D W.rank V.rank) :
    ∃ Q : PolF D W.rank V.rank, Q.totalDegree ≤ P.totalDegree ∧
      ω (1, atTau θ W τ ((M'.fr τ)⁻¹ * k * M'.fr τ)) (ptL ψ θ M M' f P) = ptL ψ θ M M' f Q := by
  obtain ⟨x, y, -, -, h⟩ := h
  have := h 1 (one_mem_K _) k hk P
  rw [elt_one hθ M] at this
  refine ⟨_, ?_, this.trans (map_smul (ptL ψ θ M M' f) _ _).symm⟩
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.T.substitution_total_degree_le D _ _ τ _ _ _ _ P)

theorem om_src_one (hθ : IsInfFam θ) (τ : D.what₂.Tau) : ω (atTau θ V τ 1, 1) = 1 := by
  rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ]; exact map_one ω

theorem om_tgt_one (hθ : IsInfFam θ) (τ : D.what₂.Tau) : ω (1, atTau θ W τ 1) = 1 := by
  rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ]; exact map_one ω

theorem om_src_mul (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (g')
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ω (atTau θ V τ (g * g'), 1) = ω (atTau θ V τ g, 1) * ω (atTau θ V τ g', 1) := by
  rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hg', ← map_mul, Prod.mk_mul_mk, mul_one]

theorem om_tgt_mul (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (g')
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) :
    ω (1, atTau θ W τ (g * g')) = ω (1, atTau θ W τ g) * ω (1, atTau θ W τ g') := by
  rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ W τ hg hg', ← map_mul, Prod.mk_mul_mk, mul_one]

theorem equiv_alt (hθ : IsInfFam θ) (h : GlobIt M M' aS aT It I) (τ : D.what₂.Tau) (hr : 0 < W.rank)
    (hinj : Function.Injective (ptL ψ θ M M' f)) (hC : CompactFock ψ θ M M' ω f τ (aS τ) (aT τ))
    (hL : LieFock ψ θ M M' ω f τ (aS τ) (aT τ)) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (φ φ' : PolF D W.rank V.rank)
    (e : ptL ψ θ M M' f φ' = ω (atTau θ V τ g, 1) (ptL ψ θ M M' f φ)) (x : ⨂[ℂ] τ, M'.H τ) :
    I φ' x = actT M τ g (I φ x) := by
  by_cases h0 : φ = 0
  · subst h0
    have : φ' = 0 := hinj (by rw [e, map_zero, map_zero])
    subst this
    simp only [map_zero, LinearMap.zero_apply]
  have T := GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct D V S M
  obtain ⟨k, hk, rfl⟩ := GlobalTheory.T.mem_maximalCompact_of_maps_fockVector_to_fock V.rank (M.ε τ) (M.fr τ) (gramAt D V τ) _ _ (ptL ψ θ M M' f)
    (fun g => ω (atTau θ V τ g, 1)) (srcOp M M' τ (aT τ)) (M.fr_unit τ) (M.fr_gram τ) hinj (om_src_one hθ τ)
    (om_src_mul hθ τ) (fun X hX => hasDerivAt_lieAction_source_operator hL hX) (compact_action_preserves_polynomial_degree hθ hC)
    (fun X _ ⟨j, k, hjk, h1, h2⟩ => not_locFin _ (GlobalTheory.T.fockSourceGlAction_eq_quadratic_add_nonRaising D _ _ τ (M.ε τ) (M'.ε τ) _ hr
      ⟨j, k, hjk, (_root_.map_ne_zero (starRingEnd ℂ)).2 h1, (_root_.map_ne_zero (starRingEnd ℂ)).2 h2⟩))
    g hg φ φ' h0 e
  obtain ⟨X, hX, h1, hK⟩ := compact_path (M.fr_unit τ) (M.fr_gram τ) hk
  have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun t => by
    obtain ⟨k', hk', e'⟩ := hK t
    rw [e']
    exact conj_mem (M.fr_unit τ) (M.fr_gram τ) hk'
  rw [← h1] at e ⊢
  refine GlobalTheory.T.equivariant_of_generator_oneParameterGroup _ _ _ (ptL ψ θ M M' f) (fun t : ℝ => ω (atTau θ V τ (NormedSpace.exp (t • X)), 1))
    (srcOp M M' τ (aT τ) X) (fun t : ℝ => actT M τ (NormedSpace.exp (t • X))) (I.flip x) (Set.range (ellT M)) hinj
    ?_ ?_ ?_ (hasDerivAt_lieAction_source_operator hL hX) ?_ ?_ ?_ ?_ ?_ φ φ' e
  · simp only [zero_smul, NormedSpace.exp_zero]
    exact om_src_one hθ τ
  · intro s t
    simp only [exp_add_smul]
    exact om_src_mul hθ τ _ (hm s) _ (hm t)
  · intro t P
    obtain ⟨k', hk', e'⟩ := hK t
    simp only [e']
    exact compact_action_preserves_polynomial_degree hθ hC k' hk' P
  · simp only [zero_smul, NormedSpace.exp_zero]
    exact T.one τ
  · intro s t
    simp only [exp_add_smul]
    exact T.mul τ _ (hm s) _ (hm t)
  · exact fun y hy => T.sep y fun w => hy _ ⟨w, rfl⟩
  · rintro _ ⟨w, rfl⟩ t
    obtain ⟨w', hw⟩ := T.adj τ _ (hm t) w
    exact ⟨w', hw.symm⟩
  · rintro _ ⟨w, rfl⟩ P
    exact h.src τ X hX P x w

theorem inv_tgt (hθ : IsInfFam θ) (h : GlobIt M M' aS aT It I) (τ : D.what₂.Tau) (hr : 0 < V.rank)
    (hinj : Function.Injective (ptL ψ θ M M' f)) (hC : CompactFock ψ θ M M' ω f τ (aS τ) (aT τ))
    (hL : LieFock ψ θ M M' ω f τ (aS τ) (aT τ)) (g : Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ)) (φ φ' : PolF D W.rank V.rank)
    (e : ptL ψ θ M M' f φ' = ω (1, atTau θ W τ g) (ptL ψ θ M M' f φ)) (x : ⨂[ℂ] τ, M'.H τ) :
    I φ' (actT M' τ g x) = I φ x := by
  by_cases h0 : φ = 0
  · subst h0
    have : φ' = 0 := hinj (by rw [e, map_zero, map_zero])
    subst this
    simp only [map_zero, LinearMap.zero_apply]
  have T := GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct D V S M
  have T' := GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct D W S' M'
  obtain ⟨k, hk, rfl⟩ := GlobalTheory.T.mem_maximalCompact_of_maps_fockVector_to_fock W.rank (M'.ε τ) (M'.fr τ) (gramAt D W τ) _ _ (ptL ψ θ M M' f)
    (fun g => ω (1, atTau θ W τ g)) (tgtOp M M' τ (aS τ)) (M'.fr_unit τ) (M'.fr_gram τ) hinj (om_tgt_one hθ τ)
    (om_tgt_mul hθ τ) (fun X hX => lie_tgt hL hX) (cpt_tgt hθ hC)
    (fun X _ hjk => not_locFin _ (GlobalTheory.T.fockTargetGlAction_eq_quadratic_add_nonRaising D _ _ τ (M.ε τ) (M'.ε τ) _ hr hjk))
    g hg φ φ' h0 e
  obtain ⟨X, hX, h1, hK⟩ := compact_path (M'.fr_unit τ) (M'.fr_gram τ) hk
  have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := fun t => by
    obtain ⟨k', hk', e'⟩ := hK t
    rw [e']
    exact conj_mem (M'.fr_unit τ) (M'.fr_gram τ) hk'
  rw [← h1] at e ⊢
  let A : ℝ → Module.End ℂ (⨂[ℂ] τ, M'.H τ) := fun t => actT M' τ (NormedSpace.exp (t • X))
  have A0 : A 0 = LinearMap.id := by
    simp only [A, zero_smul, NormedSpace.exp_zero]
    exact T'.one τ
  have Aadd : ∀ s t, A (s + t) = A s ∘ₗ A t := fun s t => by
    simp only [A, exp_add_smul]
    exact T'.mul τ _ (hm s) _ (hm t)
  let ev : (∀ τ, M.H τ) × (⨂[ℂ] τ, M'.H τ) → ((⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) →ₗ[ℂ] ℂ :=
    fun p => ellT M p.1 ∘ₗ LinearMap.applyₗ p.2
  have key : I φ' = I φ ∘ₗ A (-1) := by
    refine GlobalTheory.T.equivariant_of_generator_oneParameterGroup _ _ _ (ptL ψ θ M M' f) (fun t : ℝ => ω (1, atTau θ W τ (NormedSpace.exp (t • X))))
      (tgtOp M M' τ (aS τ) X) (fun t : ℝ => LinearMap.lcomp ℂ _ (A (-t))) I (Set.range ev) hinj
      ?_ ?_ ?_ (lie_tgt hL hX) ?_ ?_ ?_ ?_ ?_ φ φ' e
    · simp only [zero_smul, NormedSpace.exp_zero]
      exact om_tgt_one hθ τ
    · intro s t
      simp only [exp_add_smul]
      exact om_tgt_mul hθ τ _ (hm s) _ (hm t)
    · intro t P
      obtain ⟨k', hk', e'⟩ := hK t
      simp only [e']
      exact cpt_tgt hθ hC k' hk' P
    · refine LinearMap.ext fun B => ?_
      show B ∘ₗ A (-0) = B
      rw [neg_zero, A0, LinearMap.comp_id]
    · intro s t
      refine LinearMap.ext fun B => ?_
      show B ∘ₗ A (-(s + t)) = (B ∘ₗ A (-t)) ∘ₗ A (-s)
      rw [neg_add_rev, Aadd, LinearMap.comp_assoc]
    · exact fun B hB => LinearMap.ext fun y => T.sep _ fun w => hB _ ⟨(w, y), rfl⟩
    · rintro _ ⟨⟨w, y⟩, rfl⟩ t
      exact ⟨(w, A (-t) y), rfl⟩
    · rintro _ ⟨⟨w, y⟩, rfl⟩ P
      have d := HasDerivAt.scomp (0 : ℝ) (h := fun t : ℝ => -t) (by rw [neg_zero]; exact h.tgt τ X hX P y w)
        (hasDerivAt_neg (0 : ℝ))
      rw [neg_smul, one_smul, neg_neg] at d
      exact d
  show I φ' (A 1 x) = I φ x
  rw [key, LinearMap.comp_apply, ← LinearMap.comp_apply (A (-1)), ← Aadd, neg_add_cancel, A0, LinearMap.id_apply]

theorem isItW_of_globIt : ∀ {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'}
    {θ : InfFam D}, IsInfFam θ → ∀ {ψ : AddChar (AF D.host.F) ℂ}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ} {aS aT : D.what₂.Tau → ℚ}
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    {I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ},
    GlobIt M M' aS aT It I → (∀ _ : D.what₂.Tau, 0 < V.rank ∧ 0 < W.rank) →
    Function.Injective (ptOf ψ θ M M' f) → (∀ τ, CompactFock ψ θ M M' ω f τ (aS τ) (aT τ)) →
    (∀ τ, LieFock ψ θ M M' ω f τ (aS τ) (aT τ)) → IsItW θ M M' ω (ptOf ψ θ M M' f) It := by
  intro D V W S S' M M' θ hθ ψ ω f aS aT It I h hr hinj hC hL
  have T := GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct D V S M
  refine ⟨h.ne, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ w
    obtain ⟨c, hc⟩ := span_bound M' _ (h.adj φ w)
    refine ⟨c, fun v => ?_⟩
    have e : inclT M' (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun τ => (v τ : M'.H τ) :=
      PiTensorProduct.map_tprod _ _
    rw [h.incl, e]
    exact hc _
  · intro τ g hg φ φ' e v
    rw [h.incl, h.incl]
    exact equiv_alt hθ h τ (hr τ).2 hinj (hC τ) (hL τ) g hg φ φ' e _
  · intro τ X hX φ φ' e v w
    have : φ' = srcOp M M' τ (aT τ) X φ := hinj (funext fun z => (e z).unique (hasDerivAt_lieAction_source_operator (hL τ) hX φ z))
    rw [this, h.incl, h.incl]
    exact h.src τ X hX φ _ w
  · intro τ g hg φ φ' v v' e e'
    apply T.inj
    rw [h.incl, h.incl, e']
    exact inv_tgt hθ h τ (hr τ).1 hinj (hC τ) (hL τ) g hg φ φ' e _
  · intro τ X hX φ φ' v v' e e'
    have : φ' = tgtOp M M' τ (aS τ) X φ := hinj (funext fun z => (e z).unique (lie_tgt (hL τ) hX φ z))
    apply T.inj
    rw [map_add, map_zero, h.incl, h.incl, this]
    refine T.sep _ fun w => ?_
    have d := (span_deriv (ellT M') _ _ e' _ (h.adj φ w)).unique (h.tgt τ X hX φ (inclT M' v) w)
    rw [LinearMap.comp_apply] at d
    rw [map_add, d, add_neg_cancel]

end Main

end GlobalTheory.SourceOperatorLemmas

end
