import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacterStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPointsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBoundStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermIntegral

variable {D : D7}

def infLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] e

theorem map_incA_eq {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    x.map (incA D) = finLift x + infLift x := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, finLift, infLift]
  rw [← TensorProduct.add_tmul]
  have : (pairA D.host.F 0 1 + pairA D.host.F 1 0 : AF D.host.F) = 1 := by
    refine Prod.ext ?_ ?_
    · exact zero_add _
    · exact add_zero _
  rw [this]
  rfl

theorem infLift_finPart {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    (infLift x).map (finPart D) = 0 := by
  ext a b
  simp only [Matrix.map_apply, infLift, Matrix.zero_apply]
  show (sndA D.host.F (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] x a b = 0
  have : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem compAt_infLift {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (infLift x) = x.map (tauE D τ) := by
  ext a b
  simp only [compAt, Matrix.map_apply, infLift]
  have : infPart D ((pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] x a b) =
      (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x a b := rfl
  rw [this]
  exact (hθ τ).1 _

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ τ, 2 * (tauE D τ e).re = ((Algebra.trace ℚ D.host.E e : ℚ) : ℝ) := by
  classical
  have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr] at h4
  have h5 := congrArg Complex.re h4
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_re, Complex.re_sum, Complex.conj_re,
    Complex.ratCast_re] at h5
  rw [← h5, Finset.sum_congr rfl fun τ _ => two_mul _, Finset.sum_add_distrib]

theorem phase_add (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Matrix (Fin W.rank) (Fin r) D.host.E)
    (κ κ' : Mx D W.rank r) :
    phase ψ V W C C' y (κ + κ') = phase ψ V W C C' y κ * phase ψ V W C C' y κ' := by
  have h : isoPart V W C (κ + κ') = isoPart V W C κ + isoPart V W C κ' := Matrix.add_mul _ _ _
  unfold phase
  rw [h, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D V W).2.1, AddChar.map_add_eq_mul]

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    isoPart V W C (y.map (incA D)) = ratW W V (y * (adj D C * V.gram)) := by
  show HMul.hMul (y.map (incA D)) ((adj D C * V.gram).map (incA D)) = (y * (adj D C * V.gram)).map (incA D)
  simp only [Matrix.map_mul]

theorem phase_rat (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    phase ψ V W C C' y (x.map (incA D)) = 1 := by
  unfold phase
  rw [isoPart_rat, isoPart_rat]
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (y * (adj D C' * V.gram)) (x * (adj D C * V.gram))
  rw [ha]
  exact hψ.2.2.1 a

theorem trace_tau (τ : D.what₂.Tau) {m n : ℕ} (q : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (q.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (q * x)) := by
  rw [← Matrix.map_mul (f := tauE D τ)]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem ratPair_nat_smul (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) (N : ℕ) :
    ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * ((N : D.host.E) • x))) : ℚ) : ℝ) =
      (N : ℝ) * ratPair W y x := by
  have h : Matrix.trace (pairQ W y * ((N : D.host.E) • x)) = N • Matrix.trace (pairQ W y * x) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, nsmul_eq_mul]
  rw [h, map_nsmul, nsmul_eq_mul, ratPair]
  push_cast
  rfl

theorem integral : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 hY
  obtain ⟨e, he⟩ := GlobalTheory.T.openSubgroup_translate_height_bound D V W r (adj D C * V.gram)
  refine ⟨e, fun U hU => ?_⟩
  obtain ⟨M, hM, hMN⟩ := he U hU
  refine ⟨M, hM, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hx⟩ := hMN g h
  refine ⟨N, hN, hNle, fun F hF hinv y hy x hxi => ?_⟩
  obtain ⟨u, huU, hufin, hact⟩ := hx x hxi
  have h1 : heisO ψ V W (isoPart V W C (finLift ((N : D.host.E) • x))) F = F := by
    have := hinv u huU hufin
    rw [hact] at this
    exact this
  have h2 := GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 hY F hF y (finLift ((N : D.host.E) • x))
  rw [h1] at h2
  have hph : phase ψ V W C C' y (finLift ((N : D.host.E) • x)) = 1 :=
    mul_right_cancel₀ hy (by rw [one_mul]; exact h2.symm)
  have hinf : phase ψ V W C C' y (infLift ((N : D.host.E) • x)) = 1 := by
    have := phase_rat ψ hψ.1 V W C C' y ((N : D.host.E) • x)
    rw [map_incA_eq, phase_add, hph, one_mul] at this
    exact this
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (infLift_finPart _)] at hinf
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hinf
  have hsum : (∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) *
      compAt θ τ (infLift ((N : D.host.E) • x)))).re : ℝ) = (N : ℝ) * ratPair W y x := by
    rw [← ratPair_nat_smul, ← sum_two_re_tauE]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [compAt_infLift hθ, trace_tau]
  rw [hsum] at hn
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : (((N : ℝ) * ratPair W y x : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    push_cast
    ring
  exact_mod_cast h3

end GlobalTheory.MixedTermIntegral

end
