import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AutomorphicArithmetic.DivisorFrames.ExistsComplexExtensionCountable
import Development.AutomorphicArithmetic.DivisorFrames.FiniteOfFiniteExtensions
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
open IsLocalRing NumberField IsDedekindDomain GlobalTheory.ValCount
open scoped Classical

private theorem UpperTheory.relative_norm_embedding_product (K L : Type) [Field K] [Field L] (φ : K →+* L) (hφ : φ.Finite)
    (ι : K →+* ℂ) [Fintype {q : L →+* ℂ // q.comp φ = ι}] (x : L) :
    ι (rnorm φ x) = ∏ q : {q : L →+* ℂ // q.comp φ = ι}, q.1 x := by
  let : Algebra K L := φ.toAlgebra
  let : Algebra K ℂ := ι.toAlgebra
  have : Module.Finite K L := hφ
  have : CharZero K := RingHom.charZero ι
  have h := Algebra.norm_eq_prod_embeddings K ℂ x
  let e : (L →ₐ[K] ℂ) ≃ {q : L →+* ℂ // q.comp φ = ι} :=
    { toFun := fun f => ⟨f.toRingHom, f.comp_algebraMap⟩
      invFun := fun q => { q.1 with commutes' := fun a => RingHom.congr_fun q.2 a }
      left_inv := fun f => rfl
      right_inv := fun q => rfl }
  refine h.trans ?_
  exact Fintype.prod_equiv e _ _ fun f => rfl

private theorem UpperTheory.extension_embedding_card (F F' : Type) [Field F] [Field F'] [Countable F'] (ε : F →+* F')
    (σ : F' →+* ℂ) (K : Type) [Field K] (k : F →+* K) (J : Type) (L : J → Type) [∀ j, Field (L j)]
    (φ : ∀ j, K →+* L j) (c : ∀ j, F' →+* L j) (n : ℕ)
    (h : ∀ ι : K →+* ℂ, ι.comp k = σ.comp ε →
      Nat.card {q : Σ j, (L j →+* ℂ) // q.2.comp (φ q.1) = ι ∧ q.2.comp (c q.1) = σ} = n)
    (ι : K →+* ℂ) (hι : ι.comp k = σ.comp ε) (σ' : F' →+* ℂ) (hσ' : σ'.comp ε = σ.comp ε) :
    Nat.card {q : Σ j, (L j →+* ℂ) // q.2.comp (φ q.1) = ι ∧ q.2.comp (c q.1) = σ'} = n := by
  obtain ⟨τ, hτ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq σ σ'
  have h1 : (τ.symm.toRingHom.comp ι).comp k = σ.comp ε := by
    ext a
    have e1 : ι (k a) = σ (ε a) := RingHom.congr_fun hι a
    have e2 : σ' (ε a) = σ (ε a) := RingHom.congr_fun hσ' a
    show τ.symm (ι (k a)) = σ (ε a)
    rw [e1, ← e2, ← hτ, τ.symm_apply_apply, hτ, e2]
  rw [← h _ h1]
  refine Nat.card_congr
    { toFun := fun q => ⟨⟨q.1.1, τ.symm.toRingHom.comp q.1.2⟩, ?_, ?_⟩
      invFun := fun q => ⟨⟨q.1.1, τ.toRingHom.comp q.1.2⟩, ?_, ?_⟩
      left_inv := fun q => ?_
      right_inv := fun q => ?_ }
  · show (τ.symm.toRingHom.comp q.1.2).comp (φ q.1.1) = _
    rw [RingHom.comp_assoc, q.2.1]
  · show (τ.symm.toRingHom.comp q.1.2).comp (c q.1.1) = _
    rw [RingHom.comp_assoc, q.2.2]
    ext a
    show τ.symm (σ' a) = σ a
    rw [← hτ, τ.symm_apply_apply]
  · show (τ.toRingHom.comp q.1.2).comp (φ q.1.1) = _
    rw [RingHom.comp_assoc, q.2.1]
    ext a
    exact τ.apply_symm_apply _
  · show (τ.toRingHom.comp q.1.2).comp (c q.1.1) = _
    rw [RingHom.comp_assoc, q.2.2]
    ext a
    exact hτ a
  · obtain ⟨⟨j, q⟩, hq⟩ := q
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
    ext a
    exact τ.apply_symm_apply _
  · obtain ⟨⟨j, q⟩, hq⟩ := q
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq ?_))
    ext a
    exact τ.symm_apply_apply _

theorem UpperTheory.embedding_count_extensions :
    ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (ε : F →+* F') (σ : F' →+* ℂ) (K : Type) [Field K] [Countable K] (k : F →+* K) (J : Type) [Fintype J] (L : J → Type) [∀ j, Field (L j)] [∀ j, Countable (L j)] (φ : ∀ j, K →+* L j) (c : ∀ j, F' →+* L j), (∀ j, (φ j).comp k = (c j).comp ε) → ∀ n : ℕ, 0 < n → (∀ ι : K →+* ℂ, ι.comp k = σ.comp ε → Nat.card {q : Σ j, (L j →+* ℂ) // q.2.comp (φ q.1) = ι ∧ q.2.comp (c q.1) = σ} = n) → (∀ j, (φ j).Finite) ∧ ∀ x : F', ∏ j, rnorm (φ j) (c j x) = k (rnorm ε x) ^ n := by
  intro F F' _ _ _ _ ε σ K _ _ k J _ L _ _ φ c hc n hn h
  have : Countable F' := Countable.of_equiv _ (Module.finBasis ℚ F').equivFun.toEquiv.symm
  obtain ⟨ι, hι⟩ := UpperTheory.exists_complex_extension_countable F K k (σ.comp ε)
  let T := {q : Σ j, (L j →+* ℂ) // q.2.comp (φ q.1) = ι}
  let S := {s : F' →+* ℂ // s.comp ε = σ.comp ε}
  let g : T → S := fun t => ⟨t.1.2.comp (c t.1.1), by
    rw [RingHom.comp_assoc, ← hc, ← RingHom.comp_assoc, t.2, hι]⟩
  have hcard : ∀ s : S, Nat.card {t : T // g t = s} = n := fun s => by
    rw [← UpperTheory.extension_embedding_card F F' ε σ K k J L φ c n h ι hι s.1 s.2]
    exact Nat.card_congr
      { toFun := fun t => ⟨t.1.1, t.1.2, congrArg Subtype.val t.2⟩
        invFun := fun q => ⟨⟨q.1, q.2.1⟩, Subtype.ext q.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hfib : ∀ s : S, Finite {t : T // g t = s} := fun s =>
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hn.ne')
  have hT : Finite T := Finite.of_equiv _ (Equiv.sigmaFiberEquiv g)
  let e : (Σ j, {q : L j →+* ℂ // q.comp (φ j) = ι}) ≃ T :=
    { toFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2⟩
      invFun := fun t => ⟨t.1.1, ⟨t.1.2, t.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfin : ∀ j, Finite {q : L j →+* ℂ // q.comp (φ j) = ι} := fun j =>
    Finite.of_injective (fun q => e ⟨j, q⟩) (e.injective.comp sigma_mk_injective)
  have hφ : ∀ j, (φ j).Finite := fun j => UpperTheory.finite_of_finite_extensions K (L j) (φ j) ι (hfin j)
  refine ⟨hφ, fun x => ι.injective ?_⟩
  have hε : ε.Finite := by
    let : Algebra F F' := ε.toAlgebra
    have : IsScalarTower ℚ F F' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Module.Finite.of_restrictScalars_finite ℚ F F'
  let := fun j => Fintype.ofFinite {q : L j →+* ℂ // q.comp (φ j) = ι}
  let := Fintype.ofFinite T
  have h1 : ι (k (rnorm ε x)) = ∏ s : S, s.1 x :=
    (RingHom.congr_fun hι _).trans (UpperTheory.relative_norm_embedding_product F F' ε hε (σ.comp ε) x)
  rw [map_prod, map_pow, h1, ← Finset.prod_pow]
  simp_rw [fun j => UpperTheory.relative_norm_embedding_product K (L j) (φ j) (hφ j) ι (c j x)]
  rw [← Fintype.prod_sigma (fun q : (Σ j, {q : L j →+* ℂ // q.comp (φ j) = ι}) => q.2.1 (c q.1 x)),
    Fintype.prod_equiv e (fun q => q.2.1 (c q.1 x)) (fun t => (g t).1 x) (fun _ => rfl),
    ← Fintype.prod_fiberwise g]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => s.1 x) (fun t _ => by rw [t.2]), Finset.prod_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
