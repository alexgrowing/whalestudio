import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExistsCommonEigenvectorMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteJointEigensystemsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatricesIntertwiningOfSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfEntries

open Matrix

namespace GlobalTheory.DeligneSerre

theorem eq_top_of_isUnit_det (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ)
    (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O) (m : Ideal R) (hker : ∀ p, σ p = 0 → p ∈ m) (p : R)
    (hp : p ∈ m) (hu : IsUnit (σ p).det) : m = ⊤ := by
  set f := (σ p).charpoly with hf
  have hq : Polynomial.aeval p f ∈ m := by
    apply hker
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly]
  have h0 : algebraMap O R (f.coeff 0) ∈ m := by
    have h := hq
    rw [← Polynomial.X_mul_divX_add f, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    exact (Submodule.add_mem_iff_right m (m.mul_mem_right _ hp)).1 h
  have hc : IsUnit (f.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hu
    exact isUnit_of_mul_isUnit_right hu
  exact Ideal.eq_top_of_isUnit_mem m h0 (hc.map _)

theorem eigen_ringHom (R : Type) [CommRing R] (K : Type) [Field K] (n : ℕ)
    (τ : R →+* Matrix (Fin n) (Fin n) K) (c : Fin n → K) (hc : c ≠ 0)
    (h : ∀ p, ∃ μ : K, τ p *ᵥ c = μ • c) : ∃ χ : R →+* K, ∀ p, τ p *ᵥ c = χ p • c := by
  choose μ hμ using h
  have inj : ∀ a b : K, a • c = b • c → a = b := fun a b h => smul_left_injective K hc h
  refine ⟨{ toFun := μ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hμ⟩
  · apply inj; rw [← hμ, map_one, one_mulVec, one_smul]
  · intro a b; apply inj
    rw [← hμ, map_mul, ← mulVec_mulVec, hμ b, mulVec_smul, hμ a, smul_smul, mul_comm (μ b)]
  · apply inj; rw [← hμ, map_zero, zero_mulVec, zero_smul]
  · intro a b; apply inj; rw [← hμ, map_add, add_mulVec, hμ a, hμ b, add_smul]

theorem norm_det_eq_one (K : Type) [NormedField K] [IsAlgClosed K] (n : ℕ)
    (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ μ : K, (∃ c : Fin n → K, c ≠ 0 ∧ N *ᵥ c = μ • c) → ‖μ‖ = 1) : ‖N.det‖ = 1 := by
  have hroot : ∀ μ ∈ N.charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    apply h
    have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
    have hr := (Polynomial.mem_roots hne).1 hμ
    rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hr
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hr
    refine ⟨v, hv0, ?_⟩
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, mulVec_diagonal]
  rw [Matrix.det_eq_prod_roots_charpoly]
  revert hroot
  generalize N.charpoly.roots = s
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro hs
    rw [Multiset.prod_cons, norm_mul, hs a (Multiset.mem_cons_self a s),
      ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), one_mul]

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem norm_eigen_le_one (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l)
    (μ : PadicAlgCl l) (hc : c ≠ 0) (hN : N.map emb *ᵥ c = μ • c) : ‖μ‖ ≤ 1 := by
  first
  | (rename_i h_1 h_3; revert l h_1 O h_3 emb hle n N c μ hc hN; exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one)
  | exact @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one
  | (apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EigenvalueNormAtMostOne.norm_eigenvalue_le_one ..)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem unitBall_prime (R : Type) [CommRing R] (l : ℕ) [Fact l.Prime] (χ : R →+* PadicAlgCl l)
    (h : ∀ p, ‖χ p‖ ≤ 1) : ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 := by
  refine ⟨{ carrier := {p | ‖χ p‖ < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_,
    fun p => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  · simp
  · intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖χ c‖ * ‖χ x‖ ≤ 1 * ‖χ x‖ := by gcongr; exact h c
      _ < 1 := by simpa using hx
  · refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one]
      show ¬ ‖χ 1‖ < 1
      simp
    · intro a b hab
      show ‖χ a‖ < 1 ∨ ‖χ b‖ < 1
      have hab' : ‖χ a‖ * ‖χ b‖ < 1 := by
        have : ‖χ (a * b)‖ < 1 := hab
        simpa [map_mul, norm_mul] using this
      by_contra hno
      push_neg at hno
      have : 1 * 1 ≤ ‖χ a‖ * ‖χ b‖ := mul_le_mul hno.1 hno.2 zero_le_one (norm_nonneg _)
      linarith

theorem core (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] (emb : O →+* PadicAlgCl l)
    (hle : ∀ a, ‖emb a‖ ≤ 1) (hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a)
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (σ : R →ₐ[O] Matrix (Fin n) (Fin n) O)
    (m : Ideal R) (hm : m.IsMaximal) (hker : ∀ p, σ p = 0 → p ∈ m) :
    ∃ χ : R →+* PadicAlgCl l, (∀ p, ‖χ p‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖χ p‖ < 1) ∧
      (∀ a, χ (algebraMap O R a) = emb a) ∧
      ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, (σ p).map emb *ᵥ c = χ p • c := by
  classical
  let τ : R →+* Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
    (emb.mapMatrix).comp (σ : R →+* Matrix (Fin n) (Fin n) O)
  have hτ : ∀ p, τ p = (σ p).map emb := fun p => rfl
  have hcomm : ∀ p q, Commute (τ p) (τ q) := fun p q => by
    show τ p * τ q = τ q * τ p
    rw [← map_mul, ← map_mul, mul_comm]
  let X : Set (R →+* PadicAlgCl l) :=
    {χ | ∃ c : Fin n → PadicAlgCl l, c ≠ 0 ∧ ∀ p, τ p *ᵥ c = χ p • c}
  have hXfin : X.Finite := by
    have h := GlobalTheory.T.finite_joint_eigenvalues_of_commute (PadicAlgCl l) n R τ hcomm
    refine Set.Finite.of_finite_image (f := fun χ : R →+* PadicAlgCl l => (χ : R → PadicAlgCl l))
      (h.subset ?_) DFunLike.coe_injective.injOn
    rintro _ ⟨χ, ⟨c, hc, hχ⟩, rfl⟩
    exact ⟨c, hc, hχ⟩
  have hXle : ∀ χ ∈ X, ∀ p, ‖χ p‖ ≤ 1 := by
    rintro χ ⟨c, hc, hχ⟩ p
    exact norm_eigen_le_one l O emb hle n (σ p) c (χ p) hc (hχ p)
  have hP : ∀ χ ∈ X, ∃ P : Ideal R, P.IsPrime ∧ ∀ p, p ∈ P ↔ ‖χ p‖ < 1 :=
    fun χ hχ => unitBall_prime R l χ (hXle χ hχ)
  choose! P hPprime hPmem using hP
  have key : ∃ χ ∈ X, m ≤ P χ := by
    by_contra hno
    push_neg at hno
    obtain ⟨p, hpm, hpX⟩ : ∃ p ∈ m, ∀ χ ∈ X, ¬ ‖χ p‖ < 1 := by
      rcases X.eq_empty_or_nonempty with hX | ⟨χ0, hχ0⟩
      · exact ⟨0, m.zero_mem, by simp [hX]⟩
      · have hns : ¬ ((m : Set R) ⊆ ⋃ χ ∈ X, (P χ : Set R)) := by
          rw [Ideal.subset_union_prime_finite hXfin χ0 χ0 (fun χ hχ _ _ => hPprime χ hχ)]
          rintro ⟨χ, hχ, hle'⟩
          exact hno χ hχ hle'
        rw [Set.not_subset] at hns
        obtain ⟨p, hpm, hp⟩ := hns
        refine ⟨p, hpm, fun χ hχ hlt => hp ?_⟩
        exact Set.mem_biUnion hχ ((hPmem χ hχ p).2 hlt)
    have hdet : ‖(τ p).det‖ = 1 := by
      apply norm_det_eq_one (PadicAlgCl l) n (τ p)
      rintro μ ⟨c, hc, hcμ⟩
      let E : Submodule (PadicAlgCl l) (Fin n → PadicAlgCl l) :=
        { carrier := {v | τ p *ᵥ v = μ • v}
          add_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_add, ha, hb, smul_add]
          zero_mem' := by simp
          smul_mem' := by
            intro a v hv
            simp only [Set.mem_setOf_eq] at *
            rw [mulVec_smul, hv, smul_comm] }
      have hcE : c ∈ E := hcμ
      have hE : E ≠ ⊥ := fun h => hc ((Submodule.mem_bot _).1 (h ▸ hcE))
      have hstab : ∀ A ∈ Set.range τ, ∀ v ∈ E, A *ᵥ v ∈ E := by
        rintro _ ⟨q, rfl⟩ v hv
        have hv' : τ p *ᵥ v = μ • v := hv
        show τ p *ᵥ (τ q *ᵥ v) = μ • (τ q *ᵥ v)
        rw [mulVec_mulVec, (hcomm p q).eq, ← mulVec_mulVec, hv', mulVec_smul]
      obtain ⟨v, hvE, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_mem_of_commute (PadicAlgCl l) n (Set.range τ)
        (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hcomm a b) E hE hstab
      obtain ⟨χ, hχ⟩ := eigen_ringHom R (PadicAlgCl l) n τ v hv0 (fun q => hv (τ q) ⟨q, rfl⟩)
      have hχX : χ ∈ X := ⟨v, hv0, hχ⟩
      have hμ : χ p = μ := by
        have h1 : τ p *ᵥ v = μ • v := hvE
        exact smul_left_injective (PadicAlgCl l) hv0 ((hχ p).symm.trans h1)
      rw [← hμ]
      exact le_antisymm (hXle χ hχX p) (not_lt.1 (hpX χ hχX))
    have hdet' : ‖emb (σ p).det‖ = 1 := by
      rw [RingHom.map_det]
      exact hdet
    exact hm.ne_top (eq_top_of_isUnit_det O R n σ m hker p hpm (hunit _ hdet'))
  obtain ⟨χ, hχX, hmP⟩ := key
  have hmeq : m = P χ := hm.eq_of_le (hPprime χ hχX).ne_top hmP
  obtain ⟨c, hc, hχc⟩ := id hχX
  refine ⟨χ, hXle χ hχX, fun p => by rw [hmeq]; exact hPmem χ hχX p, ?_, c, hc, hχc⟩
  intro a
  have h1 := hχc (algebraMap O R a)
  have h2 : τ (algebraMap O R a) *ᵥ c = emb a • c := by
    rw [hτ, AlgHom.commutes, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero emb)]
    ext i
    simp [mulVec_diagonal]
  exact smul_left_injective (PadicAlgCl l) hc (h1.symm.trans h2)

end GlobalTheory.DeligneSerre

namespace GlobalTheory.DeligneSerre

theorem exists_integral_eigensystem : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l), Function.Injective emb → (∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ Set.range emb = {x | x ∈ L ∧ ‖x‖ ≤ 1}) → ∀ (I : Type) (M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∀ (m : Ideal (MvPolynomial I O)), m.IsMaximal → (∀ p : MvPolynomial I O, (∀ x : M, p • x = 0) → p ∈ m) → ∃ θ : I → PadicAlgCl l, (∀ i, ‖θ i‖ ≤ 1) ∧ (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ emb θ p‖ < 1) ∧ ∃ v ∈ Submodule.span (PadicAlgCl l) (Set.range j), v ≠ 0 ∧ ∀ i, Tq i v = θ i • v := by
  intro l _ O _ _ _ emb hinj hL I M _ _ _ _ hfin htf V _ _ j Tq hli hcomp m hm hann
  obtain ⟨L, _, hL⟩ := hL
  have hmemL : ∀ a, emb a ∈ L ∧ ‖emb a‖ ≤ 1 := by
    intro a
    have h : emb a ∈ Set.range emb := ⟨a, rfl⟩
    rw [hL] at h
    exact h
  have hle : ∀ a, ‖emb a‖ ≤ 1 := fun a => (hmemL a).2
  have hunit : ∀ a, ‖emb a‖ = 1 → IsUnit a := by
    intro a ha
    have hne : emb a ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at ha
      exact zero_ne_one ha
    have hinv : (emb a)⁻¹ ∈ Set.range emb := by
      rw [hL]
      refine ⟨L.inv_mem (hmemL a).1, ?_⟩
      rw [norm_inv, ha, inv_one]
    obtain ⟨b, hb⟩ := hinv
    have hab : a * b = 1 := hinj (by rw [map_mul, hb, map_one, mul_inv_cancel₀ hne])
    exact IsUnit.of_mul_eq_one b hab
  obtain ⟨n, σ, e, hσ, he_inj, he_span, he_T⟩ :=
    GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt l O emb I M hfin htf V j Tq hli hcomp
  obtain ⟨χ, hχle, hχm, hχalg, c, hc, hχc⟩ :=
    core l O emb hle hunit (MvPolynomial I O) n σ m hm (fun p hp => hann p (hσ p hp))
  set θ : I → PadicAlgCl l := fun i => χ (MvPolynomial.X i) with hθ
  have hext : MvPolynomial.eval₂Hom emb θ = χ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, hχalg]
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
  have heval : ∀ p, MvPolynomial.eval₂ emb θ p = χ p := fun p =>
    congrArg (fun f : MvPolynomial I O →+* PadicAlgCl l => f p) hext
  refine ⟨θ, fun i => hχle _, fun p => by rw [heval]; exact hχm p, e c, he_span c, ?_, ?_⟩
  · intro h
    exact hc (he_inj (by rw [h, map_zero]))
  · intro i
    rw [he_T, hχc, map_smul]

end GlobalTheory.DeligneSerre
