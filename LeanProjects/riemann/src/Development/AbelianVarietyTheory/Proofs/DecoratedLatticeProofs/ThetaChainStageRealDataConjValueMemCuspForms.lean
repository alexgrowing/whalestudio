import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowerWittTowerIsotropicSplitEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SignEquivInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MaximalCompactSortedFrameActsThroughModelCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapRightTranslateRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDimensionalSpanMultilinearValuesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RealData

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

section Frame

variable {n p q : ℕ} (e : Fin n ≃ Fin p ⊕ Fin q)

theorem submatrix_symm_mul (X Y : Matrix (Fin n) (Fin n) ℂ) : X.submatrix e.symm id * Y = (X * Y).submatrix e.symm id := by
  ext i j
  simp [Matrix.mul_apply]

theorem mul_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    B * X.submatrix e.symm id = (B.submatrix e e * X).submatrix e.symm id := by
  have hB : B = (B.submatrix e e).submatrix e.symm e.symm := by ext; simp
  conv_lhs => rw [hB]
  rw [show X.submatrix e.symm id = X.submatrix e.symm (Equiv.refl _) from rfl, submatrix_mul_equiv]
  rfl

theorem conj_submatrix_symm (B : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (X.submatrix e.symm id)ᴴ * B * X.submatrix e.symm id = Xᴴ * B.submatrix e e * X := by
  rw [Matrix.mul_assoc, mul_submatrix_symm, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id, Matrix.mul_assoc]

end Frame

theorem fr_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (M.fr τ).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)

theorem sortedFrame_gram (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    (sortedFrame M hV τ)ᴴ * Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ = gramAt D V τ := by
  rw [sortedFrame, conj_submatrix_symm, Jpq_submatrix, M.fr_gram τ]

theorem isCartanFrame_sortedFrame (M : DSModel V S) (hV : V.SigOK) : GlobalTheory.Cusp.IsCartanFrame V (sortedFrame M hV) :=
  sortedFrame_gram M hV

theorem sortedFrame_cart (M : DSModel V S) (hV : V.SigOK) (τ : D.what₂.Tau) :
    sortedFrame M hV τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * sortedFrame M hV τ := by
  rw [sortedFrame, submatrix_symm_mul, mul_submatrix_symm, Jpq_submatrix, cart, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (fr_det M τ), Matrix.one_mul]

theorem isCartanInv_cart (M : DSModel V S) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (cart M τ) := by
  have hd := fr_det M τ
  have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, conjTranspose_one]
  have hJ : (Formalism.REAL.Jm (M.ε τ)) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Formalism.REAL.Jm, diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp
  have hJh : (Formalism.REAL.Jm (M.ε τ))ᴴ = Formalism.REAL.Jm (M.ε τ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.REAL.Jm, diagonal_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, diagonal_apply, h, Ne.symm h]
  have hg : ((M.fr τ)⁻¹)ᴴ * gramAt D V τ * (M.fr τ)⁻¹ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have e : cart M τ = (M.fr τ)⁻¹ * ((M.fr τ)⁻¹)ᴴ * gramAt D V τ := by
    rw [cart, ← M.fr_gram τ]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (M.fr τ)⁻¹ ((M.fr τ)⁻¹)ᴴ (M.fr τ)ᴴ, h1, Matrix.mul_one]
  rw [e]
  exact GlobalTheory.Doubling.isCartanInv_of_frame (Matrix.nonsing_inv_mul _ hd) hg hJ hJh

theorem exists_maj_cart (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) :
    ∃ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a ∧
      ∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1 := by
  obtain ⟨a, ha, -, hs⟩ := GlobalTheory.Doubling.exists_isMaj_frameInv_eq hθ (fun τ => isCartanInv_cart M τ)
  refine ⟨a, ha, fun τ => ?_⟩
  obtain ⟨ε, hε⟩ := (GlobalTheory.Doubling.isMaj_iff hθ).1 ha τ
  rw [← hs τ, GlobalTheory.Doubling.frameInv]
  have : (compAt θ τ a.1)ᴴ * (gramAt D V τ * (compAt θ τ a.1 * (compAt θ τ a.1)ᴴ * gramAt D V τ)) * compAt θ τ a.1 =
      ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) := by
    simp only [Matrix.mul_assoc]
  rw [this, hε, diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j <;> simp [diagonal_apply, h, Matrix.one_apply] <;> split_ifs <;> simp

theorem exists_kStable (M : DSModel V S) (τ : D.what₂.Tau) {w : M.H τ} (hw : w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    ∃ W : Submodule ℂ (M.H τ), FiniteDimensional ℂ W ∧ w ∈ W ∧ Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) W := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨⊥, inferInstance, zero_mem _, fun g _ v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    obtain ⟨W', h1', h2', h3'⟩ := hy
    refine ⟨W ⊔ W', inferInstance, Submodule.add_mem_sup h2 h2', fun g hg v hv => ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (h3 g hg y hy) (h3' g hg z hz)
  | smul a x _ hx =>
    obtain ⟨W, h1, h2, h3⟩ := hx
    exact ⟨W, h1, W.smul_mem a h2, h3⟩

theorem isKFinite_value (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : IsMultMap θ M J χ T) (v : M.Vec)
    (hv : ∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) :
    GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf θ V (sortedFrame M hV)) (T v) := by
  choose W hWf hvW hWK using fun τ => exists_kStable M τ (hv τ)
  let W' : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => (W τ).comap (M.sm τ).subtype
  have hW' : ∀ τ, FiniteDimensional ℂ (W' τ) := fun τ => by
    haveI := hWf τ
    refine Module.Finite.of_injective (LinearMap.codRestrict (W τ) ((M.sm τ).subtype.comp (W' τ).subtype)
      fun x => x.2) fun x y h => ?_
    exact Subtype.ext (Subtype.ext (congrArg (fun z : W τ => (z : M.H τ)) h))
  have hfd := GlobalTheory.T.finiteDimensional_span_multilinear_values' (fun τ => M.sm τ) (GA D V → ℂ) T W' hW'
  refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfd, fun k hk => ?_⟩
  obtain ⟨v', hv', hx⟩ := GlobalTheory.T.multiplicity_map_right_translate_real_point D θ hθ V S M J χ T hT k (GlobalTheory.Cusp.Kinf_le hk) v
  have e : (fun g => T v (g * k)) = T v' := funext hx
  rw [e]
  refine Submodule.subset_span ⟨v', fun τ => ?_, rfl⟩
  show ((v' τ : M.sm τ) : M.H τ) ∈ W τ
  rw [hv' τ]
  exact hWK τ _ (GlobalTheory.T.maximal_compact_sorted_frame_acts_through_model_compact D θ V S M hV k hθ hk τ) _ (hvW τ)

theorem conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S) (hV : V.SigOK) {J : Set (GA D V)}
    {χ : GA D V → ℂ} (F : SmT M →ₗ[ℂ] (GA D V → ℂ)) (hF : F ∈ MultT θ M J χ) (w : SmT M)
    (hw : w ∈ Submodule.span ℂ {w | ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧
      w = PiTensorProduct.tprod ℂ v}) :
    (fun g => conj (F w g)) ∈ GlobalTheory.Cusp.A0 θ V (sortedFrame M hV) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 hF)
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    have e : F (PiTensorProduct.tprod ℂ v) = PiTensorProduct.lift.symm F v := by
      rw [PiTensorProduct.lift_symm]; rfl
    rw [e]
    have ha := hT.aut v
    refine GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ V _ ha,
      (GlobalTheory.Cusp.conj_mem_cuspCont ⟨ha.cont, ha.left, hT.cusp v⟩).2.2⟩, ?_⟩
    exact GlobalTheory.Mem.AutConj.finiteDimensional_span_star (isKFinite_value θ hθ M hV hT v hv)
      (by rintro f ⟨k, hk, rfl⟩; exact ⟨k, hk, funext fun g => by simp⟩)
  | zero =>
    convert zero_mem (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)) using 1
    funext g; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    funext g; simp
  | smul a x _ hx =>
    convert (GlobalTheory.Cusp.A0 θ V (sortedFrame M hV)).smul_mem (conj a) hx using 1
    funext g; simp

end GlobalTheory.ChainOnto.RealData

open GlobalTheory.ChainOnto

theorem GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, s.Is c j → ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨RealData.sortedFrame s.M hs.sigOK, a, RealData.isCartanFrame_sortedFrame _ _, fun τ => RealData.isCartanInv_cart _ τ,
    fun τ => RealData.sortedFrame_cart _ _ τ, ha, hmaj, fun u v hv => RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end
