import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ConjLine

open GlobalTheory.Mem.Isom

variable {D : D7}

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

variable {V V' : HSp D} (I : IsoMat V V')

theorem isThetaFunO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ} (hf : IsThetaFunO ψ S V f) :
    IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [IsoMat.phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add, I.symplOH_phi]
    simp only [IsoMat.trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [IsoMat.trW] using this

theorem isWeilDatumO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => isThetaFunO_tr I.symm S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact isThetaFunO_tr I S (h.om_pres _ _ (hT f hf))
  · rw [IsoMat.omT_apply, IsoMat.omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [IsoMat.omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport D V V' I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [IsoMat.omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (isThetaFunO_tr I S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

end GlobalTheory.ConjLine

noncomputable section
namespace GlobalTheory.ConjLine
open GlobalTheory.Mem.Isom GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
variable {D : D7}

theorem cT_eq_conjTranspose {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := Matrix.ext fun _ _ => rfl

theorem cmHost_imaginaryGenerator_ne_zero : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)

def sc (D : D7) : D.host.E := star (-D.host.xi0⁻¹)

theorem sc_mul : star (sc D) * sc D * (D.host.xi0 * star D.host.xi0) = 1 := by
  have h := cmHost_imaginaryGenerator_ne_zero (D := D)
  have h' : star D.host.xi0 ≠ 0 := star_ne_zero.2 h
  simp only [sc, star_star, star_neg, star_inv₀]
  field_simp

theorem gram_sc (L L' : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E)
    (hg : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (sc D • τ) * L.gram * (sc D • τ) = L'.gram := by
  rw [cT_eq_conjTranspose, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hg, smul_smul]
  convert one_smul D.host.E L'.gram using 2
  have := sc_mul (D := D)
  simp only [Int.cast_one, one_mul]
  linear_combination this

def isoOf (L L' : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (hr : L.rank = L'.rank)
    (hg : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) : IsoMat L' L where
  P := sc D • τ
  Q := L'.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (sc D • τ) * L.gram
  QP := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ L.gram, gram_sc L L' τ hg,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det L')]
  PQ := by
    refine (Matrix.mul_eq_one_comm_of_equiv (finCongr hr)).2 ?_
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ L.gram, gram_sc L L' τ hg,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det L')]
  gram := gram_sc L L' τ hg

theorem dagger_sc (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (w : WO S L') :
    dagger S L (HMul.hMul ((sc D • τ).map (incA D)) w) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w) := by
  have e : (sc D • τ).map (incA D) = incA D (sc D) • (rat τ : Mx D L.rank L'.rank) := by
    ext i j; simp [rat]
  rw [e, Matrix.smul_mul, dagger, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, adj_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  show incA D (star (sc D)) = _
  simp [sc]

end GlobalTheory.ConjLine

noncomputable section
namespace GlobalTheory.ConjLine
open GlobalTheory.Mem.Isom GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
variable {D : D7}

theorem trW_cj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (hr : L.rank = L'.rank)
    (hg : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) (f : WO L S → ℂ) :
    (isoOf L L' τ hr hg).symm.trW S (cj (dagger S L) f) =
      fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) := by
  funext w
  show starRingEnd ℂ (f (dagger S L (HMul.hMul ((sc D • τ).map (incA D)) w))) = _
  rw [dagger_sc]
  rfl

theorem trivOnF_of_resEta {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D (χ⁻¹ * χ') := by
  intro a
  obtain ⟨η, hη⟩ := h.1
  have e1 := h.2 η hη a
  have e2 := h'.2 η hη a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1, e2, inv_mul_cancel]

theorem conj_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) ∧ ∀ h, om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = fun w => star (om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) := by
  intro D ψ L L' S τ hr hg χz χ χ' om om' hom hom' f hf
  have CA := GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hom.std L S
  have hW : IsWeilDatumO ψ S L χ χz (conjAdjoint om) := (CA.conj_adjoint χz χ om hom).1
  have hF₁ : IsThetaFunO ψ S L (cj (dagger S L) f) := (CA.theta_dagger f).2 hf
  set I := (isoOf L L' τ hr hg).symm with hI
  have hG : IsThetaFunO ψ S L' (I.trW S (cj (dagger S L) f)) := isThetaFunO_tr I S hF₁
  rw [hI, trW_cj] at hG
  refine ⟨hG, fun h => ?_⟩
  have hW₀ : IsWeilDatumO ψ S L' χ χz (I.omT S (conjAdjoint om)) := isWeilDatumO_tr I S hW
  have hom'' : IsWeilDatumO ψ S L' (χ * (χ⁻¹ * χ')) (χz * 1) om' := by
    rw [mul_inv_cancel_left, mul_one]; exact hom'
  obtain ⟨a, b, ha, hb, e⟩ := (GlobalTheory.WeilDetermined.weilDatumDetermined D).2 ψ S L' χ χz (χ⁻¹ * χ') 1
    (I.omT S (conjAdjoint om)) om' (trivOnF_of_resEta hom.resT hom'.resS) (fun _ => rfl) hW₀ hom'' h 1
  have ha1 : a = 1 := by
    obtain ⟨x, hx⟩ := ha.1
    exact (ha.2 x hx).symm
  have hb1 : b = 1 := hb.at_one
  refine (e _ hG).trans ?_
  rw [ha1, hb1, inv_one, one_mul]
  simp only [Circle.coe_one, one_smul]
  rw [← trW_cj L L' S τ hr hg, ← hI, IsoMat.omT_apply, map_one, I.trW_symm_trW, ← trW_cj L L' S τ hr hg, ← hI]
  congr 1
  exact cjEnd_cj (daggerEquiv L S) (om (1, h)) f

end GlobalTheory.ConjLine
