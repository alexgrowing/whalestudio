import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealChartInfiniteAdelesCmTypeStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChartStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmoothStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CanonicalCommutationRelationsWeylNumberStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreationStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApplyStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompatStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanishStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormulaStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponentsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HermitianMajorantIsCartanInvolutionAndCommuteIffStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePosStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ComplexStructureOfInvolutionsPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubmoduleThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLinesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmoothStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeQuasiInvariantAndLevelStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTopStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.BddAboveOfSpanningPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariablesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SignInvolutionDiagonalIffStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FrameBasisMatrixOrthogonalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSignatureDecompositionDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedBasisOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelationStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfCreationEqZeroStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem exists_chart (hθ : IsInfFam θ) : ∃ σ, Chart θ σ := by
  obtain ⟨ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_real_chart_infiniteAdeles_cmType D θ hθ (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D)
  exact GlobalTheory.T.exists_isArchimedeanAdeleChart_of_real_chart D θ hθ ρ h1 h2 h3

theorem valTau_sympl (hθ : IsInfFam θ) (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W) :
    valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := GlobalTheory.T.symplectic_val_tau_compat D θ hθ V W τ x y

theorem valTau_sub (τ : D.what₂.Tau) (a b : AF D.host.F) : valTau θ τ (a - b) = valTau θ τ a - valTau θ τ b := by
  unfold valTau
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_sub, Complex.sub_re]

theorem valTau_neg (τ : D.what₂.Tau) (a : AF D.host.F) : valTau θ τ (-a) = -valTau θ τ a := by
  unfold valTau
  rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_neg, Complex.neg_re]

theorem Chart.wAt_iota (h : Chart θ σ) (V W : HSp D) (z : RW V W) (τ : D.what₂.Tau) :
    wAt θ V W τ (iotaW σ V W z) = z τ := congrFun (h.pi_iota V W z) τ

theorem Chart.omR_skew (h : Chart θ σ) (V W : HSp D) (u v : RW V W) : omR V W v u = -omR V W u v := by
  rw [omR_apply, omR_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← h.wAt_iota V W u τ, ← h.wAt_iota V W v τ, ← valTau_sympl h.inf, ← valTau_sympl h.inf,
    GlobalTheory.DualPairCheck.sympl_skew, valTau_neg]

theorem isRealW_neg {V W : HSp D} {x : WA V W} (hx : IsRealW V W x) : IsRealW V W (-x) := by
  ext i j
  have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show finPart D (-(x i j)) = 0
  rw [RingHom.map_neg, h1, neg_zero]

theorem Rel.cart {V : HSp D} (hV : V.SigOK) {τ : D.what₂.Tau} {A s} (h : Rel V τ A s) :
    IsCart (gramAt D V τ) (thAt V τ s) ∧ ∀ g : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∃ b : Mat (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2, IsKC b ∧ b * A = A * g) ↔ Commute g (thAt V τ s) := by
  refine GlobalTheory.T.hermitianMajorant_isCartanInvolution_and_commute_iff _ _ _ ?_ A _ _ ?_ h.1 h.2
  · have := (Formalism.UG.P.sig_data _ _ _ (hV (tauE D τ))).1
    rw [Fintype.card_fin] at this
    exact this.symm
  · have : (gramAt D V τ).det = tauE D τ V.gram.det := ((tauE D τ).map_det V.gram).symm
    rw [this]
    exact (map_ne_zero _).2 (gram_det_ne V)

theorem isKinf_iff {V : HSp D} (hV : V.SigOK) {A} {s : InvFam V} (h : ∀ τ, Rel V τ (A τ) (s τ)) (g : GA D V) :
    IsKinf θ V A g ↔ g ∈ Kinf θ V s :=
  and_congr Iff.rfl (forall_congr' fun τ => ((h τ).cart hV).2 _)

theorem eq_neg_of_commute {R : Type} [AddCommGroup R] (J j : R →+ R) (hJ : ∀ z, J (J z) = -z) (hj : ∀ z, j (j z) = -z)
    (hc : ∀ z, J (j z) = j (J z)) (h0 : ∀ y, J y = j y → y = 0) (z : R) : J z = -j z := by
  rw [eq_neg_iff_add_eq_zero]
  apply h0
  rw [map_add, map_add, hJ, hj, hc, add_comm]

section Cx

variable {V W : HSp D} {s : InvFam V} {s' : InvFam W}
  (hs : ∀ τ, IsCart (gramAt D V τ) (thAt V τ (s τ))) (hs' : ∀ τ, IsCart (gramAt D W τ) (thAt W τ (s' τ)))
include hs hs'

theorem jR_jR (z : RW V W) : jR V W s s' (jR V W s s' z) = -z :=
  funext fun τ => (GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)).1 (z τ)

theorem omR_jR (u v : RW V W) : omR V W (jR V W s s' u) (jR V W s s' v) = omR V W u v :=
  Finset.sum_congr rfl fun τ _ => (GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)).2.1 (u τ) (v τ)

theorem symplC_jAt_le (τ : D.what₂.Tau) (x : WC V W) : symplC V W τ (jAt V W τ (s τ) (s' τ) x) x ≤ 0 := by
  by_cases hx : x = 0
  · have := symplC_smul_right V W τ 0 (jAt V W τ (s τ) (s' τ) x) x
    rw [zero_smul, zero_mul] at this
    rw [hx] at this ⊢
    exact this.le
  · have := GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) x hx
    linarith

theorem Chart.omR_pos (h : Chart θ σ) (u : RW V W) (hu : u ≠ 0) : 0 < omR V W u (jR V W s s' u) := by
  rw [h.omR_skew, omR_apply, ← Finset.sum_neg_distrib]
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hu
  exact Finset.sum_pos' (fun τ _ => neg_nonneg.2 (symplC_jAt_le hs hs' τ _))
    ⟨τ, Finset.mem_univ _, GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) (u τ) hτ⟩

end Cx

theorem isFockCx_sign (h : Chart θ σ) {V W : HSp D} (hV : V.SigOK) (hW : W.SigOK) {A B} {s : InvFam V} {s' : InvFam W}
    (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ)) {J : WA V W →+ WA V W}
    (hJ : IsFockCx θ V W A B J) :
    (∀ x, IsRealW V W x → piW θ V W (J x) = jR V W s s' (piW θ V W x)) ∨
      ∀ x, IsRealW V W x → piW θ V W (J x) = (-jR V W s s') (piW θ V W x) := by
  have hs := fun τ => ((hA τ).cart hV).1
  have hs' := fun τ => ((hB τ).cart hW).1
  choose g hg g' hg' hgj using fun τ => (GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)).2.2.2
  obtain ⟨k, hk, hkg⟩ := GlobalTheory.T.exists_real_point_unitary_with_components D θ σ h V g fun τ => (hg τ).1
  obtain ⟨k', hk', hkg'⟩ := GlobalTheory.T.exists_real_point_unitary_with_components D θ σ h W g' fun τ => (hg' τ).1
  have hK : IsKinf θ V A k := (isKinf_iff hV hA k).2 ⟨hk, fun τ => by rw [hkg]; exact (hg τ).2⟩
  have hK' : IsKinf θ W B k' := (isKinf_iff hW hB k').2 ⟨hk', fun τ => by rw [hkg']; exact (hg' τ).2⟩
  have hact := (GlobalTheory.T.adelicUnitary_action_at_real_place D θ h.inf).2 V W k k'
  have hT : ∀ x, piW θ V W (actHom V W k k' x) = jR V W s s' (piW θ V W x) := fun x => funext fun τ => by
    rw [piW_apply, (hact x).1, hkg, hkg']
    exact (hgj τ _).symm
  let J' : RW V W →+ RW V W := (piW θ V W).comp (J.comp (iotaW σ V W))
  have hJ' : ∀ z, J' z = piW θ V W (J (iotaW σ V W z)) := fun _ => rfl
  have h1 : ∀ z, J' (J' z) = -z := fun z => by
    rw [hJ', hJ', h.iota_pi (hJ.real _ (h.real_iota V W z)), hJ.sq _ (h.real_iota V W z), map_neg, h.pi_iota]
  have h2 : ∀ z, J' (jR V W s s' z) = jR V W s s' (J' z) := fun z => by
    have e : iotaW σ V W (jR V W s s' z) = actHom V W k k' (iotaW σ V W z) :=
      h.real_ext (h.real_iota V W _) ((hact _).2 (h.real_iota V W z)) (by rw [hT, h.pi_iota, h.pi_iota])
    rw [hJ', hJ', e, hJ.kcomm k k' hK hK' _ (h.real_iota V W z), hT]
  have h3 : ∀ z τ, valTau θ τ (sympl V W (J (iotaW σ V W z)) (iotaW σ V W z)) = symplC V W τ (J' z τ) (z τ) :=
    fun z τ => by rw [valTau_sympl h.inf, h.wAt_iota]; rfl
  have h4 : ∀ y : RW V W, (∀ τ, 0 ≤ symplC V W τ (jR V W s s' y τ) (y τ)) → y = 0 := fun y hy => funext fun τ => by
    by_contra hne
    have := GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) (y τ) hne
    have h5 := hy τ
    rw [jR_apply] at h5
    linarith
  obtain ⟨ε, hε | hε, hd⟩ := hJ.defin
  · refine Or.inr fun x hx => ?_
    have := eq_neg_of_commute J' (jR V W s s').toAddMonoidHom h1 (jR_jR hs hs') h2 (fun y hy => h4 y fun τ => by
      have h5 := (hd _ (h.real_iota V W y)).1 τ
      rw [hε, one_mul, h3, hy] at h5
      exact h5) (piW θ V W x)
    rw [hJ', h.iota_pi hx] at this
    exact this
  · refine Or.inl fun x hx => ?_
    have := eq_neg_of_commute J' (-jR V W s s').toAddMonoidHom h1 (fun z => by
        show -jR V W s s' (-jR V W s s' z) = -z
        rw [map_neg, neg_neg, jR_jR hs hs']) (fun z => by
        show J' (-jR V W s s' z) = -jR V W s s' (J' z)
        rw [map_neg, h2]) (fun y hy => h4 y fun τ => by
      have h5 := (hd _ (h.real_iota V W y)).1 τ
      have h6 : J' y τ = (-1 : ℝ) • jR V W s s' y τ := by rw [hy, neg_one_smul]; rfl
      have h7 := symplC_smul_left V W τ (-1) (jR V W s s' y τ) (y τ)
      rw [hε, h3, h6] at h5
      have h8 := h5.trans_eq (congrArg (fun r : ℝ => -1 * r) h7)
      linarith) (piW θ V W x)
    rw [hJ', h.iota_pi hx] at this
    rw [this]
    exact neg_neg _

theorem actC_smul (V W : HSp D) (g h) (c : ℝ) (x : WC V W) : actC V W g h (c • x) = c • actC V W g h x := by
  unfold actC
  split_ifs <;> simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem isFockCx_of_sign (h : Chart θ σ) {V W : HSp D} (hV : V.SigOK) (hW : W.SigOK) {A B} {s : InvFam V} {s' : InvFam W}
    (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ)) {J : WA V W →+ WA V W} (hc : Continuous J)
    (hr : ∀ x, IsRealW V W x → IsRealW V W (J x)) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hJ : ∀ x, IsRealW V W x → ∀ τ, wAt θ V W τ (J x) = ε • jAt V W τ (s τ) (s' τ) (wAt θ V W τ x)) :
    IsFockCx θ V W A B J := by
  have hs := fun τ => ((hA τ).cart hV).1
  have hs' := fun τ => ((hB τ).cart hW).1
  have hal := fun τ => GlobalTheory.T.complexStructureOfInvolutions_properties D V W τ _ _ (hs τ) (hs' τ)
  have hεε : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  refine ⟨hc, hr, fun x hx => ?_, fun x y hx hy => ?_, fun k k' hk hk' x hx => ?_, -ε, ?_, fun x hx => ⟨fun τ => ?_, fun h0 => ?_⟩⟩
  · refine h.real_ext (hr _ (hr _ hx)) (isRealW_neg hx) (funext fun τ => ?_)
    rw [map_neg, piW_apply, hJ _ (hr _ hx), hJ _ hx, jAt_smul, smul_smul, hεε, one_smul, (hal τ).1]
    rfl
  · rw [← sub_eq_zero]
    refine (GlobalTheory.T.realAdele_ext_and_standardCharacter_formula D θ σ h _ ?_).1 fun τ => ?_
    · rw [map_sub, (GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inl (hr _ hx)), (GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inl hx), sub_zero]
    · rw [valTau_sub, valTau_sympl h.inf, valTau_sympl h.inf, hJ _ hx, hJ _ hy, symplC_smul_left, symplC_smul_right,
        ← mul_assoc, hεε, one_mul, (hal τ).2.1, sub_self]
  · have hact := (GlobalTheory.T.adelicUnitary_action_at_real_place D θ h.inf).2 V W k k'
    refine h.real_ext (hr _ ((hact x).2 hx)) ((hact _).2 (hr _ hx)) (funext fun τ => ?_)
    rw [piW_apply, piW_apply, hJ _ ((hact x).2 hx), (hact _).1, (hact _).1, hJ _ hx,
      (hal τ).2.2.1 _ _ (((isKinf_iff hV hA k).1 hk).2 τ) (((isKinf_iff hW hB k').1 hk').2 τ)]
    exact (actC_smul V W _ _ ε _).symm
  · rcases hε with h | h <;> rw [h] <;> norm_num
  · rw [valTau_sympl h.inf, hJ _ hx, symplC_smul_left, ← mul_assoc, neg_mul, hεε]
    have := symplC_jAt_le hs hs' τ (wAt θ V W τ x)
    linarith
  · rw [← h.iota_pi hx, ← (iotaW σ V W).map_zero]
    congr 1
    funext τ
    by_contra hne
    have h1 := GlobalTheory.T.neg_traceSymplecticForm_complexStructure_pos D V W τ _ _ (hs τ) (hs' τ) (wAt θ V W τ x) hne
    have h2 := h0 τ
    rw [valTau_sympl h.inf, hJ _ hx, symplC_smul_left] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rw [h3] at hεε; norm_num at hεε
    · rw [h3] at h1; norm_num at h1

theorem isFockCx_iff (hθ : IsInfFam θ) {V W : HSp D} (hV : V.SigOK) (hW : W.SigOK) {A B} {s : InvFam V} {s' : InvFam W}
    (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ)) (J : WA V W →+ WA V W) :
    IsFockCx θ V W A B J ↔ Continuous J ∧ (∀ x, IsRealW V W x → IsRealW V W (J x)) ∧
      ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ x, IsRealW V W x → ∀ τ, wAt θ V W τ (J x) = ε • jAt V W τ (s τ) (s' τ) (wAt θ V W τ x) := by
  obtain ⟨σ, h⟩ := exists_chart hθ
  refine ⟨fun hJ => ⟨hJ.cont, hJ.real, ?_⟩, fun ⟨hc, hr, ε, hε, hJ⟩ => isFockCx_of_sign h hV hW hA hB hc hr hε hJ⟩
  rcases isFockCx_sign h hV hW hA hB hJ with h1 | h1
  · exact ⟨1, Or.inl rfl, fun x hx τ => by rw [one_smul]; exact congrFun (h1 x hx) τ⟩
  · exact ⟨-1, Or.inr rfl, fun x hx τ => by rw [neg_one_smul]; exact congrFun (h1 x hx) τ⟩

section Killed

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

theorem foldr_lin (a : I → Module.End ℂ M) (l : List I) (m : M) :
    l.foldr (fun i x => a i x) m = (l.map a).prod m := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem Killed.succ {N : ℕ} {m : M} (h : Killed a N m) : Killed a (N + 1) m := by
  intro l hl
  obtain _ | ⟨i, l⟩ := l
  · simp at hl
  · rw [List.foldr_cons, h l (by simpa using hl), map_zero]

theorem Killed.mono {N N' : ℕ} {m : M} (h : Killed a N m) (hN : N ≤ N') : Killed a N' m := by
  induction hN with
  | refl => exact h
  | step _ ih => exact ih.succ

def nilSub (a : I → Module.End ℂ M) : Submodule ℂ M where
  carrier := {m | ∃ N, Killed a N m}
  zero_mem' := ⟨0, fun l _ => by rw [foldr_lin, map_zero]⟩
  add_mem' := fun {x y} ⟨N, hN⟩ ⟨N', hN'⟩ => ⟨max N N', fun l hl => by
    have h1 := hN.mono (le_max_left N N') l hl
    have h2 := hN'.mono (le_max_right N N') l hl
    rw [foldr_lin] at h1 h2 ⊢
    rw [map_add, h1, h2, add_zero]⟩
  smul_mem' := fun c x ⟨N, hN⟩ => ⟨N, fun l hl => by
    have h1 := hN l hl
    rw [foldr_lin] at h1 ⊢
    rw [map_smul, h1, smul_zero]⟩

end Killed

section Fock

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}

theorem Chart.psi_symplH (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (w : WA V W) (x : RW V W) :
    ψ (symplH V W w (iotaW σ V W x)) =
      Complex.exp (-(Real.pi * Complex.I) * (omR V W (piW θ V W w) x : ℝ)) := by
  unfold symplH
  rw [(GlobalTheory.T.realAdele_ext_and_standardCharacter_formula D θ σ h _ ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inr (h.real_iota V W x)))).2 ψ hψ, omR_apply]
  congr 3
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [valTau_sympl h.inf, h.wAt_iota]
  rfl

theorem Chart.dRho_eq_hD (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WA V W} (hL : IsRealDir V W L)
    (f : WA V W → ℂ) : dRho ψ V W L f = hD (iotaW σ V W) (piW θ V W) (omR V W) (piW θ V W (L 1)) f := by
  funext w
  unfold dRho hD Heisenberg₂
  congr 1
  funext t
  rw [(GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).2.1 L hL t, h.psi_symplH hψ]

theorem Chart.exists_line (h : Chart θ σ) (u : RW V W) : ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ piW θ V W (L 1) = u := by
  obtain ⟨L, hL, e⟩ := (GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).2.2 u
  exact ⟨L, hL, by rw [e, one_smul, h.pi_iota]⟩

theorem Chart.pi_line (h : Chart θ σ) {L : ℝ →+ WA V W} (hL : IsRealDir V W L) (t : ℝ) :
    piW θ V W (L t) = t • piW θ V W (L 1) := by
  rw [(GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).2.1 L hL t, h.pi_iota]

theorem Chart.isJPair_iff (h : Chart θ σ) (s : InvFam V) (s' : InvFam W) (L L' : ℝ →+ WA V W) :
    IsJPair θ V W s s' L L' ↔ IsRealDir V W L ∧ IsRealDir V W L' ∧ piW θ V W (L' 1) = jR V W s s' (piW θ V W (L 1)) := by
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, funext fun τ => h3 1 τ⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun t τ => ?_⟩⟩
  have : piW θ V W (L' t) = jR V W s s' (piW θ V W (L t)) := by
    rw [h.pi_line h1, h.pi_line h2, map_smul, h3]
  exact congrFun this τ

theorem Chart.sm (h : Chart θ σ) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) : Sm (iotaW σ V W) f :=
  ((GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).1 f).1 hf.smooth

theorem Chart.theta_hD (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f)
    (u : RW V W) : IsThetaFun ψ V W (hD (iotaW σ V W) (piW θ V W) (omR V W) u f) := by
  have hsm := (GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) f (h.sm hf) u).2
  obtain ⟨L, hL, rfl⟩ := h.exists_line u
  rw [← h.dRho_eq_hD hψ hL] at hsm ⊢
  have hd := GlobalTheory.T.heisenbergDerivative_quasiInvariant_and_level D ψ V W L f
  have hlev : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u (dRho ψ V W L f) = dRho ψ V W L f := by
    obtain ⟨U, hU, hl⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => hd.2 u (fun t => ?_) (hl u hu h0)⟩
    have h1 : sympl V W u (L t) = 0 :=
      Prod.ext ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).2 (Or.inl h0)) ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inr (hL.2 t)))
    have h2 : sympl V W (L t) u = 0 :=
      Prod.ext ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).2 (Or.inr h0)) ((GlobalTheory.T.symplectic_real_part_vanish D V W _ _).1 (Or.inl (hL.2 t)))
    unfold symplH
    rw [h1, h2, mul_zero]
    exact ⟨rfl, rfl⟩
  exact ⟨hd.1 hf.quasi, hlev, GlobalTheory.T.continuous_of_heisenberg_level_and_smooth D θ σ h ψ hψ.1.1 V W _ hlev hsm,
    ((GlobalTheory.T.smooth_iff_realCoordinates_and_real_lines D θ σ h V W).1 _).2 hsm⟩

theorem Chart.bounded (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f)
    (w : WA V W) : ∃ C : ℝ, ∀ x, ‖f (w + iotaW σ V W x)‖ ≤ C := by
  refine GlobalTheory.T.exists_le_of_continuous_of_spanning_periods _ (fun x => ‖f (w + iotaW σ V W x)‖) (h.sm hf w).continuous.norm _
    (GlobalTheory.T.span_realProjection_rationalPoints_eq_top D θ σ h V W) ?_
  rintro _ ⟨γ, rfl⟩
  obtain ⟨N, hN, e⟩ := GlobalTheory.T.norm_thetaFunction_periodic_real_variables D θ σ h ψ hψ.1.2.1 (GlobalTheory.T.exists_pos_nat_mem_open_adele_subgroup D.host.F) V W f hf γ
  exact ⟨N, hN, fun x => by rw [map_add, ← add_assoc, e]⟩

theorem Chart.killed_iff (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : Submodule ℂ (WA V W → ℂ)}
    {Dop : RW V W → Module.End ℂ M}
    (hD1 : ∀ u (f : M), ((Dop u f : M) : WA V W → ℂ) = hD (iotaW σ V W) (piW θ V W) (omR V W) u f)
    {J : WA V W →+ WA V W} (hc : Continuous J) (hr : ∀ x, IsRealW V W x → IsRealW V W (J x))
    (j : RW V W →ₗ[ℝ] RW V W) (hj : ∀ x, IsRealW V W x → piW θ V W (J x) = j (piW θ V W x)) (N : ℕ) (m : M) :
    (∀ Ls : Fin N → (ℝ →+ WA V W), (∀ i, IsRealDir V W (Ls i)) →
      (List.ofFn Ls).foldr (fun L g => annOp ψ V W J L g) m = 0) ↔
      Killed (fun u => Dop u + Complex.I • Dop (j u)) N m := by
  have key : ∀ l : List (ℝ →+ WA V W), (∀ L ∈ l, IsRealDir V W L) →
      l.foldr (fun L g => annOp ψ V W J L g) m =
        ((l.map fun L => piW θ V W (L 1)).foldr (fun u x => (Dop u + Complex.I • Dop (j u)) x) m : M) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons L l ih =>
      have hL := hl L List.mem_cons_self
      have hL' : IsRealDir V W (J.comp L) := ⟨hc.comp hL.1, fun t => hr _ (hL.2 t)⟩
      rw [List.foldr_cons, ih fun L' h' => hl L' (List.mem_cons_of_mem _ h'), List.map_cons, List.foldr_cons,
        LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD1, hD1, ← hj _ (hL.2 1),
        ← h.dRho_eq_hD hψ hL]
      erw [← h.dRho_eq_hD hψ hL']
      rfl
  constructor
  · intro H l hl
    choose Lf hLf e using fun u : RW V W => h.exists_line u
    subst hl
    have h1 := H (fun i => Lf (l.get i)) fun i => hLf _
    have h2 : (List.ofFn fun i => Lf (l.get i)) = l.map Lf := by
      rw [show (fun i => Lf (l.get i)) = Lf ∘ l.get from rfl, ← List.map_ofFn, List.ofFn_get]
    rw [h2, key _ (by
      intro L hL
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hL
      exact hLf u), List.map_map] at h1
    have h3 : ((fun L : ℝ →+ WA V W => piW θ V W (L 1)) ∘ Lf) = id := funext e
    rw [h3, List.map_id] at h1
    exact Subtype.ext h1
  · intro H Ls hLs
    rw [key _ (by
      intro L hL
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hL
      exact hLs i), H _ (by simp)]
    rfl

theorem isPolFock_iff (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (hV : V.SigOK) (hW : W.SigOK) {A B}
    {s : InvFam V} {s' : InvFam W} (hA : ∀ τ, Rel V τ (A τ) (s τ)) (hB : ∀ τ, Rel W τ (B τ) (s' τ))
    {f : WA V W → ℂ} (hf : IsThetaFun ψ V W f) : IsPolFock ψ θ V W A B f ↔ f ∈ polFun ψ θ V W s s' := by
  obtain ⟨σ, h⟩ := exists_chart hθ
  have hs := fun τ => ((hA τ).cart hV).1
  have hs' := fun τ => ((hB τ).cart hW).1
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_submodule_thetaFunctions D ψ V W
  have hform := fun f hf u => (GlobalTheory.T.heisenbergDirectionalDeriv_formula_and_smooth _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) f hf u).1
  obtain ⟨Dop, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_heisenberg_derivative_linear_operators _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) hform M
    (fun f hf => h.sm ((hM f).1 hf)) fun u f hf => (hM _).2 (h.theta_hD hψ ((hM f).1 hf) u)
  have hκ : -(2 * Real.pi * Complex.I : ℂ) ≠ 0 := neg_ne_zero.2 Complex.two_pi_I_ne_zero
  have hcomm : ∀ u v, Dop u * Dop v - Dop v * Dop u =
      (-(2 * Real.pi * Complex.I) * (omR V W u v : ℝ) : ℂ) • (1 : Module.End ℂ M) := fun u v => by
    refine LinearMap.ext fun m => Subtype.ext ?_
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, hD1, hD1, hD1, hD1,
      GlobalTheory.T.heisenbergDerivative_commutator_relation _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) hform (h.omR_skew V W) _
        (h.sm ((hM _).1 m.2))]
    rfl
  set j := jR V W s s' with hjdef
  obtain ⟨hβ, n, e, lam, hlam, hE⟩ := GlobalTheory.T.canonicalCommutationRelations_weylNumber M _ Dop (omR V W) _ j hD2 hD3 hκ hcomm (h.omR_skew V W)
    (jR_jR hs hs') (omR_jR hs hs') (h.omR_pos hs hs')
  have hann : ∀ L L', IsJPair θ V W s s' L L' → ∀ m : M, ann ψ V W L L' m =
      ((Dop (piW θ V W (L 1)) + Complex.I • Dop (j (piW θ V W (L 1)))) m : M) := fun L L' hp m => by
    obtain ⟨h1, h2, h3⟩ := (h.isJPair_iff s s' L L').1 hp
    rw [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD1, hD1, ← h3,
      ← h.dRho_eq_hD hψ h1, ← h.dRho_eq_hD hψ h2]
    rfl
  have hcre : ∀ L L', IsJPair θ V W s s' L L' → ∀ m : M, cre ψ V W L L' m =
      ((Dop (piW θ V W (L 1)) - Complex.I • Dop (j (piW θ V W (L 1)))) m : M) := fun L L' hp m => by
    obtain ⟨h1, h2, h3⟩ := (h.isJPair_iff s s' L L').1 hp
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul, hD1, hD1, ← h3,
      ← h.dRho_eq_hD hψ h1, ← h.dRho_eq_hD hψ h2]
    rfl
  have hpair : ∀ u, ∃ L L', IsJPair θ V W s s' L L' ∧ piW θ V W (L 1) = u := fun u => by
    obtain ⟨L, hL, e1⟩ := h.exists_line u
    obtain ⟨L', hL', e2⟩ := h.exists_line (j u)
    exact ⟨L, L', (h.isJPair_iff s s' L L').2 ⟨hL, hL', by rw [e1, e2]⟩, e1⟩
  have hnil : ∀ (N : ℕ) (m : M), Killed (fun u => Dop u + Complex.I • Dop (j u)) N m →
      (m : WA V W → ℂ) ∈ polFun ψ θ V W s s' := fun N m hm => by
    have := GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation _ M (fun u => Dop u + Complex.I • Dop (j u)) (fun u => Dop u - Complex.I • Dop (j u)) n e lam
      hlam hE (Submodule.span ℂ {m : M | IsFockMon ψ θ V W s s' m}) (fun m hm => Submodule.subset_span
        (IsFockMon.vac _ ⟨(hM _).1 m.2, fun L L' hp => by rw [hann L L' hp, hm]; rfl⟩)) (fun u m hm => by
        obtain ⟨L, L', hp, rfl⟩ := hpair u
        refine Submodule.map_span_le _ _ _ |>.2 (fun m' hm' => Submodule.subset_span ?_) (Submodule.mem_map_of_mem hm)
        show IsFockMon ψ θ V W s s' _
        rw [← hcre L L' hp]
        exact IsFockMon.cre L L' _ hp hm') N m hm
    exact Submodule.map_span_le M.subtype _ _ |>.2 (fun m' hm' => Submodule.subset_span hm')
      (Submodule.mem_map_of_mem this)
  constructor
  · rintro ⟨J, hJ, N, hN⟩
    rcases isFockCx_sign h hV hW hA hB hJ with hj | hj
    · exact hnil N ⟨f, (hM f).2 hf⟩ ((h.killed_iff hψ hD1 hJ.cont hJ.real j hj N ⟨f, (hM f).2 hf⟩).1 hN)
    · have hk := (h.killed_iff hψ hD1 hJ.cont hJ.real (-j) hj N ⟨f, (hM f).2 hf⟩).1 hN
      by_cases h0 : ∀ u : RW V W, u = 0
      · have : -j = j := LinearMap.ext fun u => by rw [h0 (j u), h0 ((-j) u)]
        rw [this] at hk
        exact hnil N _ hk
      · obtain ⟨u, hu⟩ := not_forall.1 h0
        obtain ⟨-, n', e', lam', hlam', hE'⟩ := GlobalTheory.T.canonicalCommutationRelations_weylNumber M _ Dop (-omR V W) (2 * Real.pi * Complex.I) (-j) hD2 hD3
          Complex.two_pi_I_ne_zero (fun u v => by rw [hcomm]; simp)
          (fun u v => by simp only [LinearMap.neg_apply]; rw [h.omR_skew])
          (fun u => by simp only [LinearMap.neg_apply, map_neg, neg_neg]; exact jR_jR hs hs' u)
          (fun u v => by simp only [LinearMap.neg_apply, map_neg, neg_neg]; rw [omR_jR hs hs'])
          (fun u hu => by simp only [LinearMap.neg_apply, map_neg, neg_neg]; exact h.omR_pos hs hs' u hu)
        have := GlobalTheory.T.mem_of_isKilledByOperatorProducts_vacuum_creation _ M (fun u => Dop u + Complex.I • Dop ((-j) u)) (fun u => Dop u - Complex.I • Dop ((-j) u))
          n' e' lam' hlam' hE' ⊥ (fun m hm => by
            rw [Submodule.mem_bot]
            refine Subtype.ext (GlobalTheory.T.eq_zero_of_hD_sub_I_smul_hD_eq_zero_of_bounded _ _ (iotaW σ V W) (piW θ V W) (omR V W) (h.pi_iota V W) hform
              (h.omR_skew V W) m (h.sm ((hM _).1 m.2)) (h.bounded hψ ((hM _).1 m.2)) u (j u) (h.omR_pos hs hs' u hu) ?_)
            have h3 : (Dop u + Complex.I • Dop ((-j) u)) m = 0 := hm u
            have h2 : Dop ((-j) u) = -Dop (j u) := by
              have := hD3 (-1) (j u)
              rw [neg_one_smul] at this
              rw [LinearMap.neg_apply, this]; simp
            rw [h2] at h3
            have h1 := congrArg Subtype.val h3
            simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, smul_neg, Submodule.coe_add,
              Submodule.coe_neg, Submodule.coe_smul, hD1] at h1
            rw [sub_eq_add_neg]
            exact h1)
          (fun i m hm => by rw [(Submodule.mem_bot _).1 hm, map_zero]; exact Submodule.zero_mem _) N _ hk
        have hf0 : f = 0 := congrArg Subtype.val ((Submodule.mem_bot _).1 this)
        rw [hf0]
        exact Submodule.zero_mem _
  · intro hp
    let J : WA V W →+ WA V W := (iotaW σ V W).comp (j.toAddMonoidHom.comp (piW θ V W))
    have hc : Continuous J := (h.continuous_iota V W).comp
      (j.continuous_of_finiteDimensional.comp (continuous_pi' hθ V W))
    have hr : ∀ x, IsRealW V W x → IsRealW V W (J x) := fun x _ => h.real_iota V W _
    have hj : ∀ x, IsRealW V W x → piW θ V W (J x) = j (piW θ V W x) := fun x _ => h.pi_iota V W _
    refine ⟨J, isFockCx_of_sign h hV hW hA hB hc hr (Or.inl rfl)
      (fun x hx τ => by rw [one_smul]; exact congrFun (hj x hx) τ), ?_⟩
    have hle : polFun ψ θ V W s s' ≤ (nilSub fun u => Dop u + Complex.I • Dop (j u)).map M.subtype := by
      refine Submodule.span_le.2 fun g hg => ?_
      induction hg with
      | vac g hg =>
        refine ⟨⟨g, (hM g).2 hg.1⟩, ⟨1, fun l hl => ?_⟩, rfl⟩
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.1 hl
        obtain ⟨L, L', hp, rfl⟩ := hpair u
        exact Subtype.ext ((hann L L' hp ⟨g, (hM g).2 hg.1⟩).symm.trans (hg.2 L L' hp))
      | cre L L' g hp _ ih =>
        obtain ⟨m, ⟨N, hN⟩, rfl⟩ := ih
        exact ⟨_, ⟨N + 1, GlobalTheory.T.isKilledByOperatorProducts_succ_creation_apply _ M _ _ (fun u => hβ u (piW θ V W (L 1))) N m hN⟩, (hcre L L' hp m).symm⟩
    obtain ⟨m, ⟨N, hN⟩, rfl⟩ := hle hp
    exact ⟨N, (h.killed_iff hψ hD1 hc hr j hj N m).2 hN⟩

end Fock

variable {X : ThetaX D} {T : ThetaTied D X}

def TieOn (Wl : WeilTied D X T) (s : ∀ V : HSp D, InvFam V) : Prop :=
  AllSome (IsInfFam (D := D)) fun θ => ∀ V W : HSp D, V.rank ≠ W.rank → V.SigOK → W.SigOK →
    X.kfin V W = polSch Wl θ V W (s V) (s W)

def Matches {Wl : WeilTied D X T} (K : Formalism.L2.Theta.KfinTied Wl)
    (b : ∀ V : HSp D, Module.Basis (Fin V.rank) D.host.E V.V) (s : ∀ V : HSp D, InvFam V) : Prop :=
  ∀ V : HSp D, V.SigOK → K.bas V = V.frame.toMatrix (b V) ∧ Adapted V (b V) (s V) ∧ IsSignFam V (s V) ∧
    ∀ τ, Rel V τ (K.cpt V τ) (s V τ)

theorem kfin_iff (Wl : WeilTied D X T)
    (A : ∀ (V : HSp D) (τ : D.what₂.Tau), Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ)
    (s : ∀ V : HSp D, InvFam V) (h : ∀ V : HSp D, V.SigOK → ∀ τ, Rel V τ (A V τ) (s V τ)) :
    (AllSome (IsInfFam (D := D)) fun θ => ∀ (V W : HSp D), V.rank ≠ W.rank → V.SigOK → W.SigOK →
      ∀ Φ : X.Sch V W, Φ ∈ X.kfin V W ↔ IsPolFock Wl.ψ θ V W (A V) (A W) (Wl.evS V W Φ)) ↔ TieOn Wl s := by
  refine and_congr Iff.rfl (forall_congr' fun θ => forall_congr' fun hθ => forall_congr' fun V => forall_congr' fun W =>
    forall_congr' fun hr => forall_congr' fun hV => forall_congr' fun hW => ?_)
  rw [Submodule.ext_iff]
  refine forall_congr' fun Φ => iff_congr Iff.rfl ?_
  have hΦ : Wl.evS V W Φ ∈ {f | IsThetaFun Wl.ψ V W f} := by
    rw [← Wl.evS_range V W hr]; exact ⟨Φ, rfl⟩
  exact isPolFock_iff hθ Wl.ψ_std hV hW (h V hV) (h W hW) hΦ

theorem sig_add {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) :
    (V.sig (tauE D τ)).1 + (V.sig (tauE D τ)).2 = V.rank := by
  have := (Formalism.UG.P.sig_data _ _ _ (hV (tauE D τ))).1
  rw [Fintype.card_fin] at this
  exact this.symm

theorem rel_of_monomial {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) (b : Module.Basis (Fin V.rank) D.host.E V.V)
    (hb : ∀ i j, i ≠ j → V.hT (b i) (b j) = 0) {s : Module.End D.host.E V.V}
    (hs : ∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i)
    {A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ}
    (hA : Aᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * A = gramAt D V τ)
    (hm : ∀ a i j, (A * (V.frame.toMatrix b).map (tauE D τ)) a i ≠ 0 →
      (A * (V.frame.toMatrix b).map (tauE D τ)) a j ≠ 0 → i = j) : Rel V τ A s := by
  obtain ⟨hu, -, h3⟩ := (GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 b
  obtain ⟨hd, hdiag, hth⟩ := h3 hb τ
  set Q := (V.frame.toMatrix b).map (tauE D τ) with hQ
  have hQu : IsUnit Q.det := by
    rw [hQ, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hu.map _
  have h1 := GlobalTheory.T.Jpq_mul_monomial_eq_mul_sign_diagonal _ _ _ (sig_add hV τ) (A * Q) _ hd (by
    rw [← hdiag, ← hA, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]) hm
  refine ⟨hA, ?_⟩
  rw [Matrix.mul_assoc, ← hth s hs, ← Matrix.mul_assoc, ← Matrix.mul_assoc] at h1
  have h2 := congrArg (· * Q⁻¹) h1
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hQu] using h2

theorem toSign {Wl : WeilTied D X T} (K : Formalism.L2.Theta.KfinTied Wl) : ∃ b s, Matches K b s ∧ TieOn Wl s := by
  classical
  have hb : ∀ V : HSp D, ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, V.SigOK → K.bas V = V.frame.toMatrix b := fun V => by
    by_cases hV : V.SigOK
    · obtain ⟨b, hb⟩ := (GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).1 _ (K.bas_unit V hV)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨V.frame, fun h => absurd h hV⟩
  choose b hb using hb
  let s : ∀ V : HSp D, InvFam V := fun V τ => (b V).constr D.host.E fun i =>
    if 0 < (tauE D τ (V.hT (b V i) (b V i))).re then b V i else -b V i
  have hs : ∀ V τ i, s V τ (b V i) = if 0 < (tauE D τ (V.hT (b V i) (b V i))).re then b V i else -b V i :=
    fun V τ i => (b V).constr_basis _ _ i
  have hM : Matches K b s := fun V hV => by
    have ho : ∀ i j, i ≠ j → V.hT (b V i) (b V j) = 0 := fun i j hij => by
      rw [← ((GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 (b V)).2.1 i j, ← hb V hV]
      exact K.bas_orth V hV i j hij
    have h1 := fun τ => (GlobalTheory.T.sign_involution_diagonal_iff D V (b V) ho τ (s V τ)).2 (hs V τ)
    refine ⟨hb V hV, ⟨ho, fun τ => (h1 τ).2⟩, fun τ => (h1 τ).1, fun τ =>
      rel_of_monomial hV τ (b V) ho (hs V τ) (K.cpt_gram V hV τ) ?_⟩
    rw [← hb V hV]
    exact K.cpt_bas V hV τ
  exact ⟨b, s, hM, (kfin_iff Wl K.cpt s fun V hV => (hM V hV).2.2.2).1 K.kfin⟩

theorem ofSign {Wl : WeilTied D X T} (b : ∀ V : HSp D, Module.Basis (Fin V.rank) D.host.E V.V)
    (s : ∀ V : HSp D, InvFam V) (h : ∀ V : HSp D, V.SigOK → Adapted V (b V) (s V) ∧ IsSignFam V (s V))
    (ht : TieOn Wl s) : ∃ K : Formalism.L2.Theta.KfinTied Wl, Matches K b s := by
  have hA : ∀ (V : HSp D) (τ : D.what₂.Tau),
      ∃ A : Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ, V.SigOK →
        Rel V τ A (s V τ) ∧ ∀ a i j, (A * (V.frame.toMatrix (b V)).map (tauE D τ)) a i ≠ 0 →
          (A * (V.frame.toMatrix (b V)).map (tauE D τ)) a j ≠ 0 → i = j := fun V τ => by
    by_cases hV : V.SigOK
    · obtain ⟨⟨ho, hpm⟩, hsf⟩ := h V hV
      obtain ⟨hu, -, h3⟩ := (GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 (b V)
      obtain ⟨hd, hdiag, -⟩ := h3 ho τ
      obtain ⟨A, h1, h2⟩ := GlobalTheory.T.exists_signature_decomposition_diagonal _ _ _ (gramAt D V τ) _ _ (hV (tauE D τ)) (by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact (hu.map _).ne_zero) hd hdiag
      exact ⟨A, fun _ => ⟨rel_of_monomial hV τ (b V) ho
        ((GlobalTheory.T.sign_involution_diagonal_iff D V (b V) ho τ (s V τ)).1 ⟨hsf τ, hpm τ⟩) h1 h2, h2⟩⟩
    · exact ⟨0, fun h => absurd h hV⟩
  choose A hA using hA
  exact ⟨{ cpt := A
           cpt_gram := fun V hV τ => (hA V τ hV).1.1
           bas := fun V => V.frame.toMatrix (b V)
           bas_unit := fun V _ => ((GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 (b V)).1
           bas_orth := fun V hV i j hij => by
            rw [((GlobalTheory.T.frame_basis_matrix_orthogonal_properties D V).2 (b V)).2.1 i j]; exact (h V hV).1.1 i j hij
           cpt_bas := fun V hV τ => (hA V τ hV).2
           kfin := (kfin_iff Wl A s fun V hV τ => (hA V τ hV).1).2 ht },
    fun V hV => ⟨rfl, (h V hV).1, (h V hV).2, fun τ => (hA V τ hV).1⟩⟩

def OneBasis (V : HSp D) (s : InvFam V) : Prop := IsSignFam V s ∧ ∃ b, Adapted V b s

theorem tied_iff (Wl : WeilTied D X T) :
    Nonempty (Formalism.L2.Theta.KfinTied Wl) ↔ ∃ s, (∀ V : HSp D, V.SigOK → OneBasis V (s V)) ∧ TieOn Wl s := by
  constructor
  · rintro ⟨K⟩
    obtain ⟨b, s, hM, ht⟩ := toSign K
    exact ⟨s, fun V hV => ⟨(hM V hV).2.2.1, b V, (hM V hV).2.1⟩, ht⟩
  · rintro ⟨s, hs, ht⟩
    have : ∀ V : HSp D, ∃ b, V.SigOK → Adapted V b (s V) := fun V => by
      by_cases hV : V.SigOK
      · obtain ⟨b, hb⟩ := (hs V hV).2
        exact ⟨b, fun _ => hb⟩
      · exact ⟨V.frame, fun h => absurd h hV⟩
    choose b hb using this
    obtain ⟨K, -⟩ := ofSign b s (fun V hV => ⟨hb V hV, (hs V hV).1⟩) ht
    exact ⟨K⟩

theorem tieOn_of_tiedBy {Wl : WeilTied D X T} {s : ∀ V : HSp D, InvFam V} (h : KfinWeilCompatibleWith Wl s) : TieOn Wl s :=
  ⟨h.2.1, fun θ hθ V W hr _ _ => h.2.2 θ hθ V W hr⟩

theorem oneBasis_of_std {A Y : HSp D} {ι : A.V →ₗ[D.host.E] Y.V} {n : ℕ} {c : Prop} {s : InvFam Y}
    (h : IsStdDec A Y ι n c s) : OneBasis Y s := by
  obtain ⟨e, f, z, -, -, -, -, -, h⟩ := h
  have hP : ∀ τ, ∀ x ∈ LinearMap.range ι ⊔ Submodule.span D.host.E (Set.range fun i => e i + f i), s τ x = x := fun τ => by
    have : LinearMap.range ι ⊔ Submodule.span D.host.E (Set.range fun i => e i + f i) ≤
        LinearMap.eqLocus (s τ) LinearMap.id := sup_le (by rintro _ ⟨x, rfl⟩; exact (h τ).2.1 x)
          (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ((h τ).2.2.1 i).1))
    exact fun x hx => this hx
  have hN : ∀ τ, ∀ x ∈ Submodule.span D.host.E (Set.range fun i => e i - f i) ⊔ Submodule.span D.host.E {z},
      s τ x = -x := fun τ => by
    have : Submodule.span D.host.E (Set.range fun i => e i - f i) ⊔ Submodule.span D.host.E {z} ≤
        LinearMap.eqLocus (s τ) (-LinearMap.id) :=
      sup_le (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ((h τ).2.2.1 i).2))
        (Submodule.span_le.2 (by rintro _ rfl; exact (h τ).2.2.2))
    exact fun x hx => this hx
  obtain ⟨τ₀, -⟩ := (GlobalTheory.T.cmType_restrict_realSubfield_infinitePlace_bijective D).2 (Classical.arbitrary _)
  exact ⟨fun τ => ⟨_, _, (h τ).1, hP τ, hN τ⟩, GlobalTheory.T.exists_adapted_basis_orthogonal D Y s _ _ τ₀ (h τ₀).1 fun τ => ⟨hP τ, hN τ⟩⟩

theorem compare (Wl : WeilTied D X T) :
    (∀ K : Formalism.L2.Theta.KfinTied Wl, ∃ b s, Matches K b s ∧ TieOn Wl s) ∧
    (∀ (b : ∀ V : HSp D, Module.Basis (Fin V.rank) D.host.E V.V) (s : ∀ V : HSp D, InvFam V),
      (∀ V : HSp D, V.SigOK → Adapted V (b V) (s V) ∧ IsSignFam V (s V)) → TieOn Wl s →
        ∃ K : Formalism.L2.Theta.KfinTied Wl, Matches K b s) ∧
    (∀ θ : InfFam D, IsInfFam θ → ∀ V W : HSp D, V.SigOK → W.SigOK → ∀ A B (s : InvFam V) (s' : InvFam W),
      (∀ τ, Rel V τ (A τ) (s τ)) → (∀ τ, Rel W τ (B τ) (s' τ)) →
      (∀ g, IsKinf θ V A g ↔ g ∈ Kinf θ V s) ∧
      (∀ J, IsFockCx θ V W A B J ↔ Continuous J ∧ (∀ x, IsRealW V W x → IsRealW V W (J x)) ∧
        ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
          ∀ x, IsRealW V W x → ∀ τ, wAt θ V W τ (J x) = ε • jAt V W τ (s τ) (s' τ) (wAt θ V W τ x)) ∧
      ∀ f, IsThetaFun Wl.ψ V W f → (IsPolFock Wl.ψ θ V W A B f ↔ f ∈ polFun Wl.ψ θ V W s s')) ∧
    (∀ s, KfinWeilCompatibleWith Wl s → (∀ V : HSp D, V.SigOK → ∃ b, Adapted V b (s V)) → Nonempty (Formalism.L2.Theta.KfinTied Wl)) ∧
    ∀ s, TowerAdapted X s → ∀ t, Odd t → D.R.r + 5 ≤ t → ∀ j, j < D.R.m → OneBasis (X.Ys t j) (s (X.Ys t j)) :=
  ⟨toSign, ofSign, fun _ hθ _ _ hV hW _ _ _ _ hA hB => ⟨isKinf_iff hV hA, isFockCx_iff hθ hV hW hA hB,
      fun _ hf => isPolFock_iff hθ Wl.ψ_std hV hW hA hB hf⟩,
    fun s h hb => (tied_iff Wl).2 ⟨s, fun V hV => ⟨h.1 V, hb V hV⟩, tieOn_of_tiedBy h⟩,
    fun _ h t ht hr j hj => oneBasis_of_std (h t ht hr j hj)⟩

end GlobalTheory.FockCompare

end
