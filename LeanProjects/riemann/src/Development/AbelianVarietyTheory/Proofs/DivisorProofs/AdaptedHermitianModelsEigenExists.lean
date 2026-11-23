import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairRankOneTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterKernelIntegralTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianDualLatticeDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelRankOneBoundedDenominatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatCongruenceLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ExpandDenomUniform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_finOne : ∃ e : AF F, evI F e = 0 ∧ ∀ v, evFin F v e = 1 := by
  refine ⟨((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)), ?_, fun v => ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  · show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (1 : FiniteAdeleRing (𝓞 F) F) = 1
    exact map_one _

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  rw [show x + w'.1 + w.1 = x + w.1 + w'.1 by abel]
  congr 2
  ring

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin d → E) : form σ J w v = -σ (form σ J v w) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem L2 (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (ξ β : Fin n → E) (x y : Fin d → E) (t : AF F) :
    symp (cA σ) (-1) (incM F J) (incM F K) (Matrix.vecMulVec (incV F ξ) (incV F y))
      (Matrix.vecMulVec (t • incV F β) (incV F x)) =
      t * algebraMap F (AF F) (Algebra.trace F E (-(form σ J ξ β * form σ K y x))) :=
  GlobalTheory.T.symplectic_pair_rank_one_trace σ J K ξ β x y t

theorem L3 (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (t : AF F) (a : F) (ht : evI F t = 0)
    (hv : ∀ v, evFin F v t = algebraMap F (Fv F v) a) (h1 : ψ t = 1) : ∃ z : ℤ, Algebra.trace ℚ F a = z :=
  GlobalTheory.T.standard_character_kernel_integral_trace (E := F) ψ hψ t a ht hv h1

theorem L4 (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (c : E) (hc : c ≠ 0) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : Fin n → E, (∀ β : Fin n → 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (c * form σ J ξ (fun i => (β i : E))) = z) →
      ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o :=
  GlobalTheory.T.hermitian_dual_lattice_denominator σ J hJ c hc

theorem uniform_denominator_integral_vectors {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (hM : M.IsGood ψ) (x : Fin d → E) : ∃ D : ℕ, 1 ≤ D ∧ ∀ β : Fin n → 𝓞 E, ∃ y z : Fin n × Fin d → 𝓞 F,
      M.co.e (incM F (Matrix.vecMulVec (fun i => (β i : E)) x)) =
        (fun k => algebraMap F (AF F) ((y k : F) / D), fun k => algebraMap F (AF F) ((z k : F) / D)) :=
  GlobalTheory.T.model_rank_one_bounded_denominator M ψ hM x

theorem uniform_denominator_expansion_local (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : κ → AF F),
      (∀ k, evI F (a k) = 0 ∧ evI F (b k) = 0 ∧
        (∀ v, ∃ c ∈ v.adicCompletionIntegers F, evFin F v (a k) = (M₀ : Fv F v) * c) ∧
        (∀ v, ∃ c ∈ v.adicCompletionIntegers F, evFin F v (b k) = (M₀ : Fv F v) * c)) →
      schr ψ (a, b) (pureA F f g) = pureA F f g :=
  GlobalTheory.T.schwartz_bruhat_congruence_level ψ hψ g hg

theorem psi_eq_one {σ : E →ₐ[F] E} {B : Base F E} {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X W₁} {H' : Plane E d d₁} {e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁}
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀) (hψ : IsStd B.ψ) {Ψ : Fn F n d} (hΨ : Ψ ∈ schA F (Fin n × Fin d))
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : u ∈ iso0 n H') (hinv : M.co.rho B.ψ u Ψ = Ψ)
    (w : Matrix (Fin n) (Fin d) (AE F E)) (hne : e₀ (M.co.rho B.ψ w Ψ) ≠ 0) :
    B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) w u) = 1 := by
  have h1 : M.co.rho B.ψ w (M.co.rho B.ψ u Ψ) =
      B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) w u) • M.co.rho B.ψ u (M.co.rho B.ψ w Ψ) := by
    simp only [Darboux.rho]
    rw [schr_comm, M.co.form]
  have h2 : e₀ (M.co.rho B.ψ w Ψ) = B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) w u) • e₀ (M.co.rho B.ψ w Ψ) := by
    conv_lhs => rw [← hinv, h1, map_smul, he.inv u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hψ w Ψ hΨ)]
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
  have h3 := congrFun h2 y
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h3 hy
  exact (mul_eq_right₀ hy).1 h3.symm

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∃ N : ℕ, 1 ≤ N ∧ ∀ (f : SInf F (Fin n × Fin d)) (ξ : Fin n → E),
      e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g)) ≠ 0 → ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH _ e₀ he hB hM hsig g hg
  obtain ⟨r, s, r', s', hX, hW⟩ := hsig
  have hψ : IsStd B.ψ := hB.std
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [form_swap σ hσ hW.skew, hH.xy, map_one]
  obtain ⟨D, hD1, hD⟩ := uniform_denominator_integral_vectors M B.ψ hM H'.x
  obtain ⟨M₀', hM₀'1, hM₀'⟩ := uniform_denominator_expansion_local B.ψ hψ.1 g hg
  obtain ⟨N, hN1, hN⟩ := L4 σ X.J (GlobalTheory.FinUniq.det_ne_zero_herm hX) ((M₀' * D : ℕ) : E)
    (Nat.cast_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
  obtain ⟨e, he0, he1⟩ := exists_finOne (F := F)
  refine ⟨N, hN1, fun f ξ hne => hN ξ fun β => ?_⟩
  set t : AF F := ((M₀' * D : ℕ) : AF F) * e with ht
  have htI : evI F t = 0 := by
    rw [ht, evI_mul, he0, mul_zero]
  have htv : ∀ v, evFin F v t = ((M₀' * D : ℕ) : Fv F v) := fun v => by
    rw [ht, map_mul, he1 v, mul_one, map_natCast]
  set u := Matrix.vecMulVec (t • incV F (fun i => (β i : E))) (incV F H'.x) with hu
  have hu0 : u ∈ iso0 n H' := ⟨_, rfl⟩
  have hΨ : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hinv : M.co.rho B.ψ u (pureA F f g) = pureA F f g := by
    have hu' : u = t • incM F (Matrix.vecMulVec (fun i => (β i : E)) H'.x) := by
      ext i j
      simp [hu, incM, incV, Matrix.vecMulVec_apply, smul_mul_assoc]
    obtain ⟨y, z, hyz⟩ := hD β
    show schr B.ψ (M.co.e u) _ = _
    rw [hu', map_smul, hyz]
    refine hM₀' f _ _ fun k => ⟨?_, ?_, fun v => ?_, fun v => ?_⟩
    · show evI F (t * _) = 0
      rw [evI_mul, htI, zero_mul]
    · show evI F (t * _) = 0
      rw [evI_mul, htI, zero_mul]
    · show ∃ c ∈ v.adicCompletionIntegers F, evFin F v (t * _) = _
      refine ⟨(y k : Fv F v), HeightOneSpectrum.coe_mem_adicCompletionIntegers v (y k), ?_⟩
      have hD0 : (D : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [map_mul, htv, AlgHom.commutes, ← map_natCast (algebraMap F (Fv F v)) (M₀' * D), ← map_mul,
        show ((M₀' * D : ℕ) : F) * ((y k : F) / D) = (M₀' : F) * (y k : F) by field_simp; push_cast; ring,
        map_mul, map_natCast]
      rfl
    · show ∃ c ∈ v.adicCompletionIntegers F, evFin F v (t * _) = _
      refine ⟨(z k : Fv F v), HeightOneSpectrum.coe_mem_adicCompletionIntegers v (z k), ?_⟩
      have hD0 : (D : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [map_mul, htv, AlgHom.commutes, ← map_natCast (algebraMap F (Fv F v)) (M₀' * D), ← map_mul,
        show ((M₀' * D : ℕ) : F) * ((z k : F) / D) = (M₀' : F) * (z k : F) by field_simp; push_cast; ring,
        map_mul, map_natCast]
      rfl
  have hch := psi_eq_one he hψ hΨ hu0 hinv _ hne
  rw [L2] at hch
  obtain ⟨z, hz⟩ := L3 B.ψ hψ _ (((M₀' * D : ℕ) : F) * Algebra.trace F E (-(form σ X.J ξ (fun i => (β i : E)) * form σ W.J H'.y H'.x)))
    (by rw [evI_mul, htI, zero_mul])
    (fun v => by rw [map_mul, htv, AlgHom.commutes, map_mul, map_natCast]) hch
  refine ⟨z, ?_⟩
  rw [← hz, hyx, mul_neg_one, neg_neg, ← Algebra.trace_trace (S := F)]
  congr 1
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]

end GlobalTheory.ExpandDenomUniform
