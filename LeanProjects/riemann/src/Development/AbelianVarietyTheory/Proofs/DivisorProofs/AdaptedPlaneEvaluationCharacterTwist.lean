import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfSkewHermitianSelfDualLatticeSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipCpt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_adapted (B : Base F E) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}
    {i₀ i₁ : ℕ} (hσ : ∀ x, σ (σ x) = x) (hL : W.L.IsLattice E) (hJ : W.J.det ≠ 0)
    (hA : H.IsAdapted σ B W W₁ i₀ i₁) : W₁.J.det ≠ 0 := by
  have hdec := fun z => GlobalTheory.UnipCocompact.exists_decomp hL hA z
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -⟩ := hA

  have hinj : ∀ u : Fin d₁ → E, H.ι *ᵥ u = 0 → u = 0 := by
    subst hn
    let Φ : E × (Fin d₁ → E) × E →ₗ[E] (Fin (d₁ + 2) → E) :=
      (LinearMap.smulRight LinearMap.id H.x).comp (LinearMap.fst E E ((Fin d₁ → E) × E)) +
      (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin d₁ → E) E).comp (LinearMap.snd E E ((Fin d₁ → E) × E))) +
      (LinearMap.smulRight LinearMap.id H.y).comp ((LinearMap.snd E (Fin d₁ → E) E).comp (LinearMap.snd E E ((Fin d₁ → E) × E)))
    have hΦ : ∀ s u r, Φ (s, u, r) = s • H.x + H.ι *ᵥ u + r • H.y := fun s u r => by simp [Φ]
    have hsurj : Function.Surjective Φ := fun z => by
      obtain ⟨s, t, u, rfl⟩ := hdec z
      exact ⟨(s, u, t), hΦ s u t⟩
    have hΦinj : Function.Injective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mpr hsurj
    intro u hu
    have h0 : Φ (0, u, 0) = Φ (0, 0, 0) := by rw [hΦ, hΦ, hu]; simp
    exact congrArg (fun p : E × (Fin d₁ → E) × E => p.2.1) (hΦinj h0)
  intro hd
  obtain ⟨u, hu, hJu⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
  have hι : ∀ v : Fin d₁ → E, form σ W.J (H.ι *ᵥ u) (H.ι *ᵥ v) = 0 := fun v => by
    have hσv : (fun i => σ ((H.ι *ᵥ v) i)) = H.ι.map σ *ᵥ (fun i => σ (v i)) :=
      funext fun i => RingHom.map_mulVec (σ : E →+* E) H.ι v i
    simp only [form]
    rw [hσv, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hgram, hJu, zero_dotProduct]
  have hall : ∀ z, form σ W.J (H.ι *ᵥ u) z = 0 := fun z => by
    obtain ⟨s, t, w, rfl⟩ := hdec z
    rw [GlobalTheory.UnipCocompact.form_add, GlobalTheory.UnipCocompact.form_add, GlobalTheory.UnipCocompact.form_smul,
      GlobalTheory.UnipCocompact.form_smul, (horth u).1, (horth u).2, hι w]
    simp
  have hrow : (H.ι *ᵥ u) ᵥ* W.J = 0 := funext fun j => by
    have h := hall (Pi.single j 1)
    have hs : (fun i => σ ((Pi.single j (1 : E) : Fin d → E) i)) = Pi.single j 1 := funext fun i => by
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    simp only [form] at h
    rw [hs, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h
    exact h
  have hzero : H.ι *ᵥ u = 0 := by
    by_contra hne
    exact hJ (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hrow⟩)
  exact hu (hinj u hzero)

theorem exists_compact_reps : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
      ∃ K : Set (unip σ W H'), IsCompact K ∧ ∀ u : unip σ W H', ∃ γ : unip σ W H', γ.1 ∈ ratU σ W.J ∧ γ⁻¹ * u ∈ K := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hA _ e₀ _ χX χW om r s r' s' hP
  have hcm := hP.base.cm
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hW := hP.skew
  have hJ : W.J.det ≠ 0 := GlobalTheory.SkewDet.det_ne_zero_of_isSkew F E σ B d r' s' W hW
  have hJ₁ : W₁.J.det ≠ 0 := det_ne_zero_of_adapted B hσ hW.lat hJ hA
  obtain ⟨K, hK, hKu⟩ := GlobalTheory.UnipCocptForm.cocompact_unip_form W W₁ H' hcm hW.skew hA.rank hA.xx hA.yy hA.xy
    hA.orth hA.gram hJ hJ₁
  refine ⟨K, hK, fun u => ?_⟩
  obtain ⟨γ, hγ, hγu⟩ := hKu u
  refine ⟨γ⁻¹, ?_, by rwa [inv_inv]⟩
  exact (ratU σ W.J).inv_mem (Subgroup.mem_subgroupOf.1 hγ)

end GlobalTheory.ThK.UnipCpt
