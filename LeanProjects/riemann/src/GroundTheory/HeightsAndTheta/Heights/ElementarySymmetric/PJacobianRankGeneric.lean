import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StJacobianRankGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem JacobianRankGeneric.kaehler_D_aeval {σ K : Type*} [Fintype σ] [Field K] [Algebra ℂ K] (x : σ → K)
    (f : MvPolynomial σ ℂ) :
    KaehlerDifferential.D ℂ K (aeval x f) =
      ∑ l, aeval x (pderiv l f) • KaehlerDifferential.D ℂ K (x l) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, add_smul]
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hp, Finset.smul_sum, smul_smul, map_add, add_smul,
      Finset.sum_add_distrib, pderiv_X, smul_eq_mul, Pi.single_apply]
    rw [add_left_inj]
    simp [apply_ite, ite_smul]

theorem JacobianRankGeneric.finrank_kaehler_eq_card {k K : Type} [Field k] [Field K] [Algebra k K] (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (H : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by
  have hx : AlgebraicIndependent k (fun i : s => (i : K)) := hs.1
  let _ : Algebra (MvPolynomial s k) K := (aeval (fun i : s => (i : K))).toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial s k) K := IsScalarTower.of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  let _ : Algebra (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    ((hx.aevalEquivField).toRingHom.comp (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)))).toAlgebra
  let e : FractionRing (MvPolynomial s k) ≃ₐ[MvPolynomial s k]
      IntermediateField.adjoin k (Set.range fun i : s => (i : K)) :=
    { hx.aevalEquivField with commutes' := fun q => rfl }
  have : Algebra.FormallyEtale (MvPolynomial s k) (FractionRing (MvPolynomial s k)) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) :=
    .of_equiv e
  have : IsScalarTower (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change aeval (fun i : s => (i : K)) q =
        ((hx.aevalEquivField (algebraMap (MvPolynomial s k) (FractionRing (MvPolynomial s k)) q) : _) : K)
      rw [hx.aevalEquivField_algebraMap_apply_coe]
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K := by
    convert! H <;> simp
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K :=
    .of_isSeparable _ K
  have : Algebra.FormallyEtale (MvPolynomial s k) K :=
    .comp (MvPolynomial s k) (IntermediateField.adjoin k (Set.range fun i : s => (i : K))) K
  have : Module.Free (MvPolynomial s k) Ω[MvPolynomial s k⁄k] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis k s)
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) K).finrank_eq,
    Module.finrank_baseChange, Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis k s),
    Fintype.card_coe]

theorem JacobianRankGeneric.proof : JacobianRankGeneric.Statement := by
  classical
  intro n d J _ hd
  set A := MvPolynomial (Fin n) ℂ ⧸ J
  set K := FractionRing A

  let ψ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] K := (IsScalarTower.toAlgHom ℂ A K).comp (Ideal.Quotient.mkₐ ℂ J)
  let x : Fin n → K := fun l => ψ (X l)
  have hψ : ∀ f, ψ f = aeval x f := fun f => congrArg (fun φ => φ f) (MvPolynomial.aeval_unique ψ)
  have hgrad : ∀ f l, genericGradient J f l = aeval x (pderiv l f) := fun f l => hψ (pderiv l f)
  let Φ : (Fin n → K) →ₗ[K] Ω[K⁄ℂ] :=
    ∑ l, (LinearMap.proj l : (Fin n → K) →ₗ[K] K).smulRight (KaehlerDifferential.D ℂ K (x l))
  have hΦ : ∀ w, Φ w = ∑ l, w l • KaehlerDifferential.D ℂ K (x l) := fun w => by
    simp [Φ, LinearMap.sum_apply]

  have hker : Submodule.span K (genericGradient J '' (J : Set _)) ≤ LinearMap.ker Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have h0 : aeval x f = 0 := by
      rw [← hψ]
      simp only [ψ, AlgHom.comp_apply]
      rw [show Ideal.Quotient.mkₐ ℂ J f = 0 from Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hΦ, hgrad]
    rw [← JacobianRankGeneric.kaehler_D_aeval, h0, map_zero]

  have hsurj : LinearMap.range Φ = ⊤ := by
    have hA : ∀ f, KaehlerDifferential.D ℂ K (ψ f) ∈ LinearMap.range Φ := fun f =>
      ⟨fun l => aeval x (pderiv l f), by rw [hΦ, hψ, JacobianRankGeneric.kaehler_D_aeval]⟩
    rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, v, _, rfl⟩ := IsFractionRing.div_surjective (A := A) a
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hf := hA f
    have hg := hA g
    change KaehlerDifferential.D ℂ K (ψ f / ψ g) ∈ _
    rw [Derivation.leibniz_div]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ hg))

  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ℂ K
  have hcard : s.card = d := by
    have h1 := hs.cardinalMk_eq_trdeg
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing ℂ (A := A) K
    rw [hd, ← h1, Cardinal.mk_coe_finset] at h2
    simp at h2
    exact_mod_cast h2.symm
  have hrank : Module.finrank K Ω[K⁄ℂ] = d := by
    rw [JacobianRankGeneric.finrank_kaehler_eq_card s hs H, hcard]

  have h1 := Submodule.finrank_mono hker
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hsurj, finrank_top, hrank, Module.finrank_fin_fun] at h2
  change Module.finrank K (Submodule.span K (genericGradient J '' (J : Set _))) ≤ n - d
  calc _ ≤ _ := h1
    _ = n - d := by
      generalize Module.finrank K (LinearMap.ker Φ) = m at h2 ⊢
      omega

end

end GroundTheory.Heights₂.Heights
