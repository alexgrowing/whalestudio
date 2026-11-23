import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

private theorem mem_submodule_of_basis_matrix {L M : Type*} [Field L] [AddCommGroup M] [Module L M] {P : Submodule L M}
    {d : ℕ} (b : Module.Basis (Fin d) L P) (g : M →ₗ[L] M) (A : Matrix (Fin d) (Fin d) L)
    (hb : ∀ j, g (b j) = ∑ i, A i j • (b i : M)) : ∀ x ∈ P, g x ∈ P := by
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : M) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
    exact h.symm
  rw [hx', map_sum]
  refine Submodule.sum_mem _ (fun i _ => ?_)
  rw [map_smul, hb]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (b k).2))

private theorem aeval_matrix_eq_zero_of_aeval_zero_on_submodule {L M : Type*} [Field L] [AddCommGroup M] [Module L M] {P : Submodule L M}
    {d : ℕ} (b : Module.Basis (Fin d) L P) (g : M →ₗ[L] M) (A : Matrix (Fin d) (Fin d) L)
    (hb : ∀ j, g (b j) = ∑ i, A i j • (b i : M)) (Q : Polynomial L)
    (hQ : ∀ x ∈ P, Polynomial.aeval g Q x = 0) : Polynomial.aeval A Q = 0 := by
  have hP := mem_submodule_of_basis_matrix b g A hb
  have hmat : LinearMap.toMatrixAlgEquiv b (g.restrict hP) = A := by
    ext i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    have h : g.restrict hP (b j) = ∑ k, A k j • b k := by
      apply Subtype.ext
      simp [LinearMap.restrict_apply, hb]
    rw [h, b.repr_sum_self]
  have hcoe : ∀ (Q' : Polynomial L) (y : P),
      ((Polynomial.aeval (g.restrict hP) Q' y : P) : M) = Polynomial.aeval g Q' y := by
    intro Q' y
    induction Q' using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, LinearMap.add_apply, hp, hq]
    | monomial k a =>
      simp only [Polynomial.aeval_monomial, Module.End.pow_restrict k hP, Module.End.mul_apply,
        Module.algebraMap_end_apply, LinearMap.restrict_apply, SetLike.val_smul]
  have h0 : Polynomial.aeval (g.restrict hP) Q = 0 := by
    ext y
    rw [hcoe]
    simpa using hQ y y.2
  rw [← hmat, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h0, map_zero]

theorem UpperTheory.Gal.Mod.esStep :
    TowES → PlaceData → GrPass → ESStep := by
  intro hT hP hG E Ω _ _ _ _ _ l _ ι H θ hN dd ρ hcont hpc w hl n ϑ R hcong hroots A hA
  obtain ⟨ρ₀, ⟨b, hb⟩, hgr⟩ := hpc
  obtain ⟨C, p, f, hp, hpw, hnorm, hon, hC⟩ := hcong
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP E Ω w A hA
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hinv : ∀ σ : Gal(Ω/E), ∀ x ∈ piece l H Ω (Qbar l) θ,
      galV l H Ω (Qbar l) σ x ∈ piece l H Ω (Qbar l) θ := by
    intro σ
    exact mem_submodule_of_basis_matrix b (galV l H Ω (Qbar l) σ) (ρ₀ σ : Matrix (Fin dd) (Fin dd) (Qbar l)) (hb σ)
  have key := fun σ hσA => hT l p f n hp (Ow w) (h6 p hpw) E (by exact_mod_cast hp.ne_zero)
    (by rw [← hnorm]; exact h3) Ω A h1 h2 (h5 l hl) (Qbar l) H θ hN C ϑ hC hinv σ hσA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨hsA, hsv⟩ := h7 s hs
    have hM : Polynomial.aeval (ρ₀ s : Matrix (Fin dd) (Fin dd) (Qbar l))
        (Polynomial.X - 1 : Polynomial (Qbar l)) = 0 := by
      refine aeval_matrix_eq_zero_of_aeval_zero_on_submodule b (galV l H Ω (Qbar l) s) _ (hb s) _ (fun x hx => ?_)
      simp [(key s hsA x hx).1 hsv]
    have hM' := hG (G E Ω) (Qbar l) dd ρ₀ ρ hgr s _ hM
    simp only [map_sub, Polynomial.aeval_X, map_one, sub_eq_zero] at hM'
    exact Units.ext hM'
  · obtain ⟨hσA, hσv⟩ := h8 _ σ hσ
    rw [h4, hnorm] at hσv
    have hM : Polynomial.aeval (ρ₀ σ⁻¹ : Matrix (Fin dd) (Fin dd) (Qbar l))
        (crystallineComparison.heckePol (normV w) n ϑ) = 0 := by
      refine aeval_matrix_eq_zero_of_aeval_zero_on_submodule b (galV l H Ω (Qbar l) σ⁻¹) _ (hb σ⁻¹) _ (fun x hx => ?_)
      rw [← (key σ hσA x hx).2 hσv, crystallineComparison.heckePol, h4, hnorm, map_sum, LinearMap.sum_apply,
        Finset.sum_range (fun j => (Polynomial.aeval (galV l H Ω (Qbar l) σ⁻¹))
          (Polynomial.C ((-1) ^ j * ((p ^ f : ℕ) : Qbar l) ^ j.choose 2 * ϑ j) * Polynomial.X ^ (n - j)) x)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, Module.End.pow_apply]
      congr 1
      push_cast [co]
      ring
    have hM' := hG (G E Ω) (Qbar l) dd ρ₀ ρ hgr σ⁻¹ _ hM
    obtain ⟨hϑ0, hpol⟩ := hroots
    have hQ : crystallineComparison.heckePol (normV w) n ϑ =
        Polynomial.C (ϑ 0) * Polynomial.map ι.symm.toRingHom (crystallineComparison.rootPol R) := by
      have h := congrArg (Polynomial.map ι.symm.toRingHom) hpol
      rw [Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C] at h
      simpa using h
    rw [hQ, map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      smul_eq_zero] at hM'
    exact hM'.resolve_left hϑ0
