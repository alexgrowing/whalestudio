import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

section Alg

variable {K : Type} [Field K]

theorem eq_zero_of_pts {M : Type} [Field M] [IsAlgClosed M] [Algebra K M] (p : TRing K) (a : p.R)
    (h : ∀ ψ : p.R →ₐ[K] M, ψ a = 0) : a = 0 := by
  classical
  have hRdef : p.R = (MvPolynomial (Fin p.n) K ⧸ p.I) := rfl
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstanceAs (IsJacobsonRing (MvPolynomial (Fin p.n) K ⧸ p.I))
  haveI hFT : Algebra.FiniteType K p.R :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K p.I) (Ideal.Quotient.mkₐ_surjective K p.I)
  have hrad : (⊥ : Ideal p.R).IsRadical := fun x ⟨k, hk⟩ =>
    (Submodule.mem_bot _).2 (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
  have hjac : (⊥ : Ideal p.R).jacobson = ⊥ := by
    first
    | exact IsJacobsonRing.out inferInstance hrad
    | exact IsJacobsonRing.out' ⊥ hrad
  have ha : a ∈ (⊥ : Ideal p.R).jacobson := by
    set_option synthInstance.maxHeartbeats 400000 in
    refine Ideal.mem_sInf.2 fun J hJ => ?_
    have hJm : J.IsMaximal := hJ.2
    letI := Ideal.Quotient.field J
    haveI : Algebra.FiniteType K (p.R ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ_surjective K J)
    haveI : Module.Finite K (p.R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (p.R ⧸ J)
    haveI : Algebra.IsIntegral K (p.R ⧸ J) := Algebra.IsIntegral.of_finite K _
    haveI : Algebra.IsAlgebraic K (p.R ⧸ J) := Algebra.IsIntegral.isAlgebraic
    let ι : (p.R ⧸ J) →ₐ[K] M := IsAlgClosed.lift
    have h0 := h (ι.comp (Ideal.Quotient.mkₐ K J))
    have h1 : ι (Ideal.Quotient.mk J a) = ι 0 := by
      rw [map_zero]
      exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 (ι.toRingHom.injective h1)
  rw [hjac] at ha
  exact (Submodule.mem_bot _).1 ha

theorem eq_zero_of_cpts (σ : K →+* ℂ) (p : TRing K) (a : p.R) (h : ∀ ψ : p.R →ₐ[K] CAt σ, ψ a = 0) : a = 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  exact eq_zero_of_pts (M := CAt σ) p a h

def cvalR (σ : K →+* ℂ) : CAt σ →+* ℂ := RingHom.id ℂ

def toCAt (σ : K →+* ℂ) (z : ℂ) : CAt σ := z

theorem cvalR_algebraMap (σ : K →+* ℂ) (t : K) : cvalR σ (algebraMap K (CAt σ) t) = σ t := rfl

theorem linIndep_alg_pts [CharZero K] {Kb : Type} [Field Kb] [IsAlgClosed Kb] [Algebra K Kb] [Normal K Kb] (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (v : Fin m → Kb)
    (h : ∀ φ : p.R →ₐ[K] Kb, ∑ i, v i * φ (a i) = 0) : v = 0 := by
  classical
  let L : IntermediateField K Kb := IntermediateField.adjoin K (Set.range v)
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let u : Fin m → L := fun i => ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hu : ∀ i, algebraMap L Kb (u i) = v i := fun i => rfl

  have hg : ∀ (g : L →ₐ[K] Kb) (φ : p.R →ₐ[K] Kb), ∑ i, g (u i) * φ (a i) = 0 := by
    intro g φ
    let G : Kb →ₐ[K] Kb := g.liftNormal Kb
    have hb : Function.Bijective G := Algebra.IsAlgebraic.algHom_bijective G
    let Ge : Kb ≃ₐ[K] Kb := AlgEquiv.ofBijective G hb
    have h1 := h ((Ge.symm : Kb →ₐ[K] Kb).comp φ)
    have h2 := congrArg G h1
    rw [map_zero, map_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hu i, AlgHom.liftNormal_commutes]
    congr 1
    show φ (a i) = G (Ge.symm (φ (a i)))
    exact (Ge.apply_symm_apply (φ (a i))).symm

  have htr : ∀ lam : L, ∀ i, Algebra.trace K L (lam * u i) = 0 := by
    intro lam
    have hpt : ∀ φ : p.R →ₐ[K] Kb, φ (∑ i, Algebra.trace K L (lam * u i) • a i) = 0 := by
      intro φ
      rw [map_sum]
      have : ∀ i, φ (Algebra.trace K L (lam * u i) • a i) =
          (∑ g : L →ₐ[K] Kb, g (lam * u i)) * φ (a i) := by
        intro i
        rw [map_smul, Algebra.smul_def, ← trace_eq_sum_embeddings]
      simp_rw [this, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      have := hg g φ
      calc ∑ i, g (lam * u i) * φ (a i) = g lam * ∑ i, g (u i) * φ (a i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul, mul_assoc]
        _ = 0 := by rw [this, mul_zero]
    have h0 := eq_zero_of_pts p _ hpt
    exact fun i => (Fintype.linearIndependent_iff.1 ha _ h0) i
  funext i
  have hz : u i = 0 := by
    refine (traceForm_nondegenerate K L).1 (u i) fun lam => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact htr lam i
  rw [← hu i, hz, map_zero]
  rfl

theorem linIndep_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (w : Fin m → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ i, w i * cvalR σ (ψ (a i)) = 0) : w = 0 := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  let Kb := AlgebraicClosure K
  letI : Module Kb ℂ := Module.compHom ℂ (ι.toRingHom : Kb →+* ℂ)
  have hsm : ∀ (c : Kb) (z : ℂ), c • z = ι c * z := fun _ _ => rfl
  by_contra hw
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hw (funext hne)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual Kb ℂ, ℓ (w j) ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hj ((Module.forall_dual_apply_eq_zero_iff Kb (w j)).1 hne)
  have hv := linIndep_alg_pts (Kb := AlgebraicClosure K) p a ha (fun i => ℓ (w i)) fun φ => by
    have h1 := congrArg ℓ (h (ι.comp φ : p.R →ₐ[K] ℂ))
    rw [map_zero, map_sum] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : w i * cvalR σ ((ι.comp φ : p.R →ₐ[K] ℂ) (a i)) = φ (a i) • w i := by
      rw [hsm, mul_comm]; rfl
    erw [e, map_smul, smul_eq_mul, mul_comm]
  exact hℓ (congrFun hv j)

theorem descend_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {r : ℕ} (a : Fin r → p.R) (w : Fin r → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ j, w j * cvalR σ (ψ (a j)) = 0) (θ : Module.Dual K (CAt σ)) :
    ∑ j, θ (toCAt σ (w j)) • a j = 0 := by
  classical
  let S : Submodule K p.R := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let e := Module.finBasis K S
  let t : Fin r → Fin (Module.finrank K S) → K := fun j l => e.repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩ l
  have hat : ∀ j, a j = ∑ l, t j l • (e l : p.R) := by
    intro j
    have := e.sum_repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩
    have h2 := congrArg (fun x : S => (x : p.R)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hind : LinearIndependent K (fun l => (e l : p.R)) :=
    e.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have key := linIndep_cpts σ p (fun l => (e l : p.R)) hind (fun l => ∑ j, σ (t j l) * w j) fun ψ => by
    rw [← h ψ]
    simp_rw [hat, map_sum, map_smul, Algebra.smul_def, map_mul, cvalR_algebraMap, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hk : ∀ l, ∑ j, t j l • toCAt σ (w j) = 0 := by
    intro l
    have := congrFun key l
    simp only [Pi.zero_apply] at this
    exact this
  calc ∑ j, θ (toCAt σ (w j)) • a j = ∑ l, θ (∑ j, t j l • toCAt σ (w j)) • (e l : p.R) := by
        simp_rw [hat, Finset.smul_sum, map_sum, map_smul, smul_eq_mul, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = 0 := by simp [hk]

end Alg

end Formalism.L2.Pj
