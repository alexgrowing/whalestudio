import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatSign
variable {D : D7}

theorem AA_eq (hc : D.host.ccK = ⊤) : D.host.AA = D.host.AA0 := by
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.ccE
  rw [hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

theorem hRat_one (S T : HSp D) (hS : S.gram = 1) (hT : T.gram = 1) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T x y = ∑ c, ∑ a, star (y c a) * x c a := by
  unfold GlobalTheory.LatVac.hRat
  rw [hS, hT, inv_one]
  simp [Matrix.one_apply]
  rw [Finset.sum_comm]

theorem toMatrix_smul_eq (S T : HSp D) (hS : S.gram = 1) {n : ℕ} (s s' : Fin n → Fin S.rank → D.host.E)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) (r : D.host.E)
    (x : (Fin S.rank → D.host.E) →ₗ[D.host.E] (Fin T.rank → D.host.E)) :
    LinearMap.toMatrix' (r • x) = ∑ i, GlobalTheory.LatVac.genMap S T r (s' i) (x (s i)) := by
  have hd' : ∀ j, (∑ i, star (s' i j) • s i) = Pi.single j 1 := by
    intro j; funext a
    have := hd a j
    rw [hS] at this
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => by ring
  ext a j
  rw [LinearMap.toMatrix'_apply, Matrix.sum_apply]
  simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, hS, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hd' j, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mem_latRat (S T : HSp D) (hS : S.gram = 1) (hc : D.host.ccK = ⊤)
    (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hN : IsSelfDualC S N) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hγ : Matrix.toLin' γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    γ ∈ GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  obtain ⟨n, s, s', hs, hd⟩ := GlobalTheory.T.exists_dual_family_selfDual_hermitianSpace D S N hN
  rw [← LinearMap.toMatrix'_toLin' γ]
  refine Submodule.span_induction (p := fun φ _ => LinearMap.toMatrix' φ ∈
      GlobalTheory.LatVac.latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E))) ?_ ?_ ?_ ?_ hγ
  · rintro _ ⟨r, hr, x, hx, rfl⟩
    rw [toMatrix_smul_eq S T hS s s' hd r x]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r, ?_, s' i, (hs i).2, x (s i), hx _ (hs i).1, rfl⟩
    rw [AA_eq hc]; exact hr
  · rw [map_zero]; exact zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro c x _ hx
    have : c • x = ((c : D.host.E)) • x := (algebraMap_smul D.host.E c x).symm
    rw [this, map_smul]
    exact GlobalTheory.LatVac.smul_mem_latRat c hx

end GlobalTheory.LatSign

namespace GlobalTheory.LatSign
variable {D : D7}
open GlobalTheory.LatVac GlobalTheory.VacSign

theorem exists_trace_one_xi0_mul_star_eq_of_ccK_eq_top (hc : D.host.ccK = ⊤) : ∃ w0 : 𝓞 D.host.E, (w0 : D.host.E) + star (w0 : D.host.E) = 1 ∧
    D.host.xi0 * star (w0 : D.host.E) = (D.host.xi0 + 1) / 2 := by
  set s := D.host.sqrtMinusD with hsdef
  have hsq : s ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hst : star s = -s := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have := D.host.isCMField_hostE
    have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
      NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
    rw [hsdef, h2, map_neg, h1]
    simp
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hsq
    have : (D.host.d : D.host.E) = 0 := by rw [zero_pow two_ne_zero] at hsq; exact neg_eq_zero.1 hsq.symm
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have hxs : D.host.xi0 * s = -1 := by
    unfold Formalism.BasicNotions.Host.xi0
    rw [hc, Ideal.absNorm_top, Nat.cast_one, one_mul, ← hsdef]
    field_simp
  have hm : ((D.host.d + 1 : ℕ) : D.host.E) = 4 * (((D.host.d + 1) / 4 : ℕ) : D.host.E) := by
    have : D.host.d + 1 = 4 * ((D.host.d + 1) / 4) := by omega
    exact_mod_cast congrArg (fun n : ℕ => (n : D.host.E)) this
  have hint : IsIntegral ℤ ((1 + s) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((D.host.d + 1) / 4 : ℕ) : ℤ), by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, eq_intCast, Int.cast_natCast, Polynomial.eval₂_natCast, map_natCast]
    push_cast at hm
    linear_combination (1 / 4 : D.host.E) * hsq - (1 / 4 : D.host.E) * hm
  refine ⟨⟨_, hint⟩, ?_, ?_⟩
  · show (1 + s) / 2 + star ((1 + s) / 2) = 1
    rw [star_div₀, star_add, star_one, hst, star_ofNat]; ring
  · show D.host.xi0 * star ((1 + s) / 2) = (D.host.xi0 + 1) / 2
    rw [star_div₀, star_add, star_one, hst, star_ofNat]
    linear_combination (-1 / 2 : D.host.E) * hxs

theorem sum_conj_eq_trace (D : D7) (e : D.host.E) :
    ∑ t, (tauE D t e + starRingEnd ℂ (tauE D t e)) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
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
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [Finset.sum_add_distrib, h4]

theorem sum_two_re_eq_trace (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  rw [← sum_conj_eq_trace]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem tauE_star' (τ : D.what₂.Tau) (x : D.host.E) : tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) := by
  have := D.host.isCMField_hostE
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) x

theorem sgnW_finTens {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} (w : D.host.E)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    sgnW ψ (incA D w) (finTens 1 γ : WO S T) =
      Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T γ (w • γ)) : ℚ) : ℂ)) := by
  have h3 : symplOH S T (finTens 1 γ) (finTens 1 (w • γ)) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T γ (w • γ)))) := by
    rw [symplOH, symplO_finTens, one_mul, one_mul, RingHom.map_mul]
    exact Prod.ext (mul_zero _) rfl
  rw [sgnW, incA_smul_finTens, h3, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ,
    show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
    Algebra.trace_trace, smul_eq_mul]
  congr 1
  push_cast
  ring

end GlobalTheory.LatSign

namespace GlobalTheory.LatSign
variable {D : D7}
open GlobalTheory.LatVac GlobalTheory.VacSign

theorem tauE_X (S T : HSp D) (hS1 : S.gram = 1) (hT1 : T.gram = 1)
    (hxi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)) (w : D.host.E)
    (hw : D.host.xi0 * star w = (D.host.xi0 + 1) / 2) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (τ : D.what₂.Tau) :
    2 * (tauE D τ (D.host.xi0 * hRat S T γ (w • γ))).re = ∑ c, ∑ a, Complex.normSq (tauE D τ (γ c a)) := by
  have hX : D.host.xi0 * hRat S T γ (w • γ) = ((D.host.xi0 + 1) / 2) * ∑ c, ∑ a, star (γ c a) * γ c a := by
    rw [hRat_one S T hS1 hT1, ← hw, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, star_mul']
    ring
  rw [hX, map_mul, map_div₀, map_add, map_one, hxi, map_ofNat, map_sum]
  simp only [map_sum, map_mul, tauE_star']
  have hn : ∀ c a, starRingEnd ℂ (tauE D τ (γ c a)) * tauE D τ (γ c a) =
      ((Complex.normSq (tauE D τ (γ c a)) : ℝ) : ℂ) := fun c a => (Complex.normSq_eq_conj_mul_self).symm
  simp only [hn, ← Complex.ofReal_sum, Complex.re_mul_ofReal]
  simp

theorem alV_eq (S T : HSp D) (hS1 : S.gram = 1) (hT1 : T.gram = 1) (δ : ℂ) (sc : ℝ)
    (hsc : sc * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹)
    (hxi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)) (w : D.host.E)
    (hw : D.host.xi0 * star w = (D.host.xi0 + 1) / 2) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    alV D.host.d sc (embH (tauE D) δ (Matrix.toLin' γ)) =
      Complex.exp (Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T γ (w • γ)) : ℚ) : ℂ)) := by
  have hz : ∀ τ i j, embH (tauE D) δ (Matrix.toLin' γ) τ i j = δ * tauE D τ (γ i j) := by
    intro τ i j
    simp [embH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  have hHV : HV sc (embH (tauE D) δ (Matrix.toLin' γ)) (embH (tauE D) δ (Matrix.toLin' γ)) =
      ((sc * ‖δ‖ ^ 2 * ∑ τ, ∑ c, ∑ a, Complex.normSq (tauE D τ (γ c a)) : ℝ) : ℂ) := by
    simp only [HV, LinearMap.mk₂'ₛₗ_apply, hz]
    have hm : ∀ τ c a, δ * tauE D τ (γ c a) * starRingEnd ℂ (δ * tauE D τ (γ c a)) =
        ((‖δ‖ ^ 2 * Complex.normSq (tauE D τ (γ c a)) : ℝ) : ℂ) := by
      intro τ c a
      rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_eq_norm_sq]
    simp only [hm, ← Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.ofReal_mul]
    congr 1
    ring
  have hd : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  unfold alV Formalism.L2.Th1.H.alphaQ Formalism.L2.Th1.H.qOf
  rw [hHV, Complex.ofReal_re, ← sum_two_re_eq_trace]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 2
  rw [Finset.sum_congr rfl fun τ _ => tauE_X S T hS1 hT1 hxi w hw γ τ, ← mul_assoc, ← mul_assoc, mul_assoc _ sc, hsc]
  field_simp

end GlobalTheory.LatSign

namespace GlobalTheory.LatSign
open GlobalTheory.LatVac GlobalTheory.VacSign

theorem latSign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v → ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := by
  intro D ψ θ S T a b hS hT δ sc hP g _ h _ N N' hN hN' f _ hl γ hγ v hv z
  subst hS
  subst hT
  have eS : GlobalTheory.AdForm.latFr S rfl N = (N : Set (Fin S.rank → D.host.E)) := by
    ext x; first | exact Iff.rfl | simp [GlobalTheory.AdForm.latFr]
  have eT : GlobalTheory.AdForm.latFr T rfl N' = (N' : Set (Fin T.rank → D.host.E)) := by
    ext x; first | exact Iff.rfl | simp [GlobalTheory.AdForm.latFr]
  have ht : GlobalTheory.AdForm.toHom S T rfl rfl γ = Matrix.toLin' γ := by simp [GlobalTheory.AdForm.toHom]
  rw [eS, eT] at hl
  rw [ht] at hγ ⊢
  have hSD := GlobalTheory.SplitMove.selfDual_move S hP.gS g N hN
  have hTD := GlobalTheory.SplitMove.selfDual_move T hP.gT h N' hN'
  obtain rfl := (isFinOf_iff γ v).1 hv
  have hu : (finTens 1 γ : WO S T) ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E))
      fun _ => True :=
    finTens_mem_latO (one_mem_intAf _) (mem_latRat S T hP.gS hP.cc N N' hSD γ hγ)
  obtain ⟨w, hw0, hxw⟩ := exists_trace_one_xi0_mul_star_eq_of_ccK_eq_top (D := D) hP.cc
  have hw : incA D (w : D.host.E) + cA D (incA D (w : D.host.E)) = 1 := by
    have : cA D (incA D (w : D.host.E)) = incA D (star (w : D.host.E)) := rfl
    rw [this, ← RingHom.map_add, hw0, RingHom.map_one]
  have hΛ : ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True),
        ψ (symplO S T u (incA D (w : D.host.E) • u')) = 1 :=
    fun u hu u' hu' => char_sympl_eq_one hP.std hSD hTD hu (smul_mem_latO w hu')
  have hsign : heisO ψ S T (finTens 1 γ) f = sgnW ψ (incA D (w : D.host.E)) (finTens 1 γ : WO S T) • f :=
    (le_of_two_of_half (sgnGroup ψ hw _ hΛ f)
      (fun u hu => ⟨nsmul_mem hu 2, by rw [hl.1 u hu, sgnW_two ψ hw (hΛ u hu u hu), one_smul]⟩)
      (fun e he u hu hh => ⟨hu, by rw [hl.2 e he u hu hh, sgnW_half ψ _ he hh, one_smul]⟩) hu).2
  have hsq : sgnW ψ (incA D (w : D.host.E)) (finTens 1 γ : WO S T) *
      sgnW ψ (incA D (w : D.host.E)) (finTens 1 γ : WO S T) = 1 := char_half (hΛ _ hu _ hu)
  have hal : alV D.host.d sc (embH (tauE D) δ (Matrix.toLin' γ)) =
      sgnW ψ (incA D (w : D.host.E)) (finTens 1 γ : WO S T) := by
    rw [alV_eq S T hP.gS hP.gT δ sc hP.scale hP.xi (w : D.host.E) hxw γ, sgnW_finTens hP.std]
  rw [hsign, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hal, hsq, one_mul]

end GlobalTheory.LatSign
