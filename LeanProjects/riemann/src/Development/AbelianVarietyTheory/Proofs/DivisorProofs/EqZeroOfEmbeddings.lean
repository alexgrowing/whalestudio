import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

open IsLocalRing

namespace GlobalTheory.VandermondeEmbeddingVanishing

theorem eq_zero_of_embeddings {K L Ω : Type} [Field K] [Field L] [Field Ω] [IsAlgClosed Ω] [Algebra K L] [Algebra K Ω]
    [Module.Finite K L] [Algebra.IsSeparable K L] {ι : Type} [Fintype ι] (b : Module.Basis ι K L) (c : ι → Ω)
    (h : ∀ s : L →ₐ[K] Ω, ∑ t, s (b t) * c t = 0) : c = 0 := by
  classical
  have hcard : Fintype.card ι = Fintype.card (L →ₐ[K] Ω) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis b]
  let e : ι ≃ (L →ₐ[K] Ω) := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex K Ω b e).det ≠ 0 := by
    intro h0
    have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two (K := K) (E := Ω) (b := ⇑b) e
    rw [h0, zero_pow two_ne_zero, map_eq_zero_iff _ (algebraMap K Ω).injective] at hd
    exact Algebra.discr_not_zero_of_basis K b hd
  have hmul : Matrix.mulVec (Algebra.embeddingsMatrixReindex K Ω b e).transpose c = 0 := by
    ext j
    simpa [Matrix.mulVec, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix_apply] using h (e j)
  exact Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hmul

theorem exists_functional {T M Ω : Type} [CommRing T] [IsLocalRing T] [AddCommGroup M] [Module T M] [Field Ω]
    [Algebra (ResidueField T) Ω] [Algebra T Ω] [IsScalarTower T (ResidueField T) Ω] (ϖ : T)
    (hϖ : maximalIdeal T = Ideal.span {ϖ}) (z : M) (hz : ¬ ∃ y : M, z = ϖ • y) : ∃ lam : M →ₗ[T] Ω, lam z ≠ 0 := by
  classical
  let N : Submodule T M := maximalIdeal T • ⊤
  let _ : Module (ResidueField T) (M ⧸ N) := Module.instQuotientIdealSubmoduleHSMulTop M (maximalIdeal T)
  have hq : (Submodule.Quotient.mk z : M ⧸ N) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    show z ∉ maximalIdeal T • (⊤ : Submodule T M)
    rw [hϖ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    rintro ⟨y, -, hy⟩
    exact hz ⟨y, hy.symm⟩
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ResidueField T) (M ⧸ N), f (Submodule.Quotient.mk z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hq ((Module.forall_dual_apply_eq_zero_iff (ResidueField T) _).mp hcon)
  refine ⟨LinearMap.mk (AddHom.mk (fun m => algebraMap (ResidueField T) Ω (f (Submodule.Quotient.mk m)))
    (fun a b => by simp only [Submodule.Quotient.mk_add, map_add])) (fun a m => ?_), ?_⟩
  · have hs : (Submodule.Quotient.mk (a • m) : M ⧸ N) = residue T a • Submodule.Quotient.mk m := rfl
    simp only [RingHom.id_apply]
    rw [hs, map_smul, smul_eq_mul, map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply T (ResidueField T) Ω a]
    rfl
  · exact (map_ne_zero (algebraMap (ResidueField T) Ω)).mpr hf

theorem mem_spanBy_iff {R F : Type} [CommRing R] [CommRing F] [Algebra R F] (S : Set F) (x : F) :
    x ∈ GlobalTheory.Desc.spanBy (algebraMap R F) S ↔ x ∈ Submodule.span R S := by
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Submodule.sum_mem _ fun i _ => by
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (ht i))
  · intro hx
    obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp hx
    exact ⟨n, f, fun i => g i, fun i => (g i).2, by rw [← hfg]; simp only [Algebra.smul_def]⟩

section Main

variable {O T F F₁ Ω : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
  [Field F] [Field F₁] [Algebra O T] [IsLocalHom (algebraMap O T)] [Algebra T F₁] [Field Ω] [IsAlgClosed Ω]
  [Algebra (ResidueField O) Ω] [Algebra (ResidueField T) Ω] [Algebra T Ω] [IsScalarTower T (ResidueField T) Ω]
  [Module.Finite (ResidueField O) (ResidueField T)] [Algebra.IsSeparable (ResidueField O) (ResidueField T)]

def Van (Ω : Type) [Field Ω] [Algebra (ResidueField O) Ω] [Algebra T Ω] (θ : F →+* F₁) (π : O) (W : Subalgebra T F₁) : Prop :=
  ∀ (s : ResidueField T →ₐ[ResidueField O] Ω) (lam : ↥(Subalgebra.toSubmodule W) →ₗ[T] Ω) (n : ℕ) (r : Fin n → T)
    (w : Fin n → F) (hw : ∀ (i : Fin n), θ (w i) ∈ Subalgebra.toSubmodule W), ∀ y ∈ W,
    ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
      ∑ i : Fin n, s (residue T (r i)) * lam ⟨θ (w i), hw i⟩ = 0

theorem compat {c₀ : O →+* F} {θ : F →+* F₁} (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) {π : O}
    {W : Subalgebra T F₁} (hV : Van Ω θ π W) (lam : ↥(Subalgebra.toSubmodule W) →ₗ[T] Ω)
    (h1 : lam ⟨1, W.one_mem⟩ ≠ 0) (o : O) :
    algebraMap (ResidueField O) Ω (residue O o) = algebraMap T Ω (algebraMap O T o) := by
  classical
  let s : ResidueField T →ₐ[ResidueField O] Ω := IsAlgClosed.lift
  have hco : ∀ x, θ (c₀ x) = algebraMap T F₁ (algebraMap O T x) := fun x => RingHom.congr_fun hc x
  have hmem : ∀ x, θ (c₀ x) ∈ Subalgebra.toSubmodule W := fun x => by
    rw [Subalgebra.mem_toSubmodule, hco]
    exact W.algebraMap_mem _
  have hl : ∀ x, lam ⟨θ (c₀ x), hmem x⟩ = algebraMap T Ω (algebraMap O T x) * lam ⟨1, W.one_mem⟩ := by
    intro x
    rw [← Algebra.smul_def, ← map_smul]
    congr 1
    ext
    simp only [hco, Submodule.coe_smul, Algebra.algebraMap_eq_smul_one]
  have key := hV s lam 2 ![1, -algebraMap O T o] ![c₀ o, c₀ 1] (fun i => by fin_cases i <;> exact hmem _) 0 W.zero_mem
    (by simp [Fin.sum_univ_two, hco])
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one] at key
  rw [hl, hl, map_one, map_one, map_one, map_one, one_mul, map_neg, map_neg, ← IsLocalRing.ResidueField.algebraMap_residue,
    AlgHom.commutes] at key
  have hsub : (algebraMap T Ω (algebraMap O T o) - algebraMap (ResidueField O) Ω (residue O o)) * lam ⟨1, W.one_mem⟩ = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp hsub with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h h1

theorem comp_div {c₀ : O →+* F} {θ : F →+* F₁} (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) {π : O}
    (hπ : Irreducible (algebraMap O T π)) {W : Subalgebra T F₁} (hV : Van Ω θ π W)
    {ι : Type} [Fintype ι] (b : Module.Basis ι (ResidueField O) (ResidueField T))
    {n : ℕ} (r : Fin n → T) (w : Fin n → F) (hw : ∀ i, θ (w i) ∈ W) (y : F₁) (hy : y ∈ W)
    (hr : ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y)
    (o : ι → Fin n → O) (ho : ∀ t i, residue O (o t i) = b.repr (residue T (r i)) t) (t : ι) :
    ∃ y' ∈ W, ∑ i, algebraMap T F₁ (algebraMap O T (o t i)) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y' := by
  classical
  have hmax : maximalIdeal T = Ideal.span {algebraMap O T π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
  have hsum : ∑ i, algebraMap T F₁ (algebraMap O T (o t i)) * θ (w i) ∈ W :=
    W.sum_mem fun i _ => W.mul_mem (W.algebraMap_mem _) (hw i)
  by_cases hone : ∃ y₁ ∈ W, (1 : F₁) = algebraMap T F₁ (algebraMap O T π) * y₁
  · obtain ⟨y₁, hy₁, e₁⟩ := hone
    exact ⟨y₁ * ∑ i, algebraMap T F₁ (algebraMap O T (o t i)) * θ (w i), W.mul_mem hy₁ hsum,
      by rw [← mul_assoc, ← e₁, one_mul]⟩
  obtain ⟨lam₀, hl₀⟩ := exists_functional (Ω := Ω) (M := Subalgebra.toSubmodule W) _ hmax ⟨1, W.one_mem⟩ (by
    rintro ⟨y, hy⟩
    exact hone ⟨y, y.2, by simpa [Algebra.smul_def] using congrArg Subtype.val hy⟩)
  have hcompat := compat hc hV lam₀ hl₀
  by_contra hno
  obtain ⟨lam, hlam⟩ := exists_functional (Ω := Ω) (M := Subalgebra.toSubmodule W) _ hmax ⟨_, hsum⟩ (by
    rintro ⟨y, hy⟩
    exact hno ⟨y, y.2, by simpa [Algebra.smul_def] using congrArg Subtype.val hy⟩)
  apply hlam
  let cc : ι → Ω := fun t => ∑ i, algebraMap (ResidueField O) Ω (residue O (o t i)) * lam ⟨θ (w i), hw i⟩
  have hcc : cc = 0 := by
    refine eq_zero_of_embeddings b cc fun s => ?_
    have hs := hV s lam n r w hw y hy hr
    rw [← hs]
    simp only [cc, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← b.sum_repr (residue T (r i)), map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [map_smul, ← ho, Algebra.smul_def]
    ring
  have he : (⟨_, hsum⟩ : Subalgebra.toSubmodule W) = ∑ i, algebraMap O T (o t i) • ⟨θ (w i), hw i⟩ := by
    ext
    simp [Algebra.smul_def]
  rw [he, map_sum]
  have hct : cc t = 0 := by rw [hcc]; rfl
  rw [← hct]
  simp only [cc, map_smul, Algebra.smul_def, hcompat]

theorem div_span (hinj : Function.Injective (algebraMap T F₁)) {c₀ : O →+* F} {θ : F →+* F₁}
    (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) {π : O}
    (hπ : Irreducible (algebraMap O T π)) {W : Subalgebra T F₁} (hV : Van Ω θ π W)
    {n : ℕ} (w : Fin n → F) (hw : ∀ i, θ (w i) ∈ W) (S : Finset (Fin n)) :
    ∀ (r : Fin n → T), (∀ i ∉ S, r i = 0) → ∀ y ∈ W,
      ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
      y ∈ Submodule.span T (θ '' (θ ⁻¹' (W : Set F₁))) := by
  classical
  intro r _ y hy hr
  have hmax : maximalIdeal T = Ideal.span {algebraMap O T π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
  have hco : ∀ x, θ (c₀ x) = algebraMap T F₁ (algebraMap O T x) := fun x => RingHom.congr_fun hc x
  have hϖ : algebraMap T F₁ (algebraMap O T π) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hπ.ne_zero
  let b := Module.finBasis (ResidueField O) (ResidueField T)
  choose o ho using fun t (i : Fin n) => IsLocalRing.residue_surjective (b.repr (residue T (r i)) t)
  choose β hβ using fun t => IsLocalRing.residue_surjective (b t)
  have hdiff : ∀ i, ∃ r' : T, r i = ∑ t, algebraMap O T (o t i) * β t + algebraMap O T π * r' := by
    intro i
    have hm : r i - ∑ t, algebraMap O T (o t i) * β t ∈ maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sum]
      simp only [map_mul, ← IsLocalRing.ResidueField.algebraMap_residue, ho, hβ]
      conv_lhs => enter [1]; rw [← b.sum_repr (residue T (r i))]
      simp [Algebra.smul_def]
    rw [hmax, Ideal.mem_span_singleton'] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, by rw [mul_comm _ a, ha]; ring⟩
  choose r' hr' using hdiff
  choose y' hy' hyeq using fun t => comp_div hc hπ hV b r w (fun i => hw i) y hy hr o (fun t i => ho t i) t
  have hmem' : ∀ t, y' t ∈ θ '' (θ ⁻¹' (W : Set F₁)) := by
    intro t
    have hne : θ (c₀ π) ≠ 0 := by rw [hco]; exact hϖ
    have hval : θ ((∑ i, c₀ (o t i) * w i) * (c₀ π)⁻¹) = y' t := by
      rw [map_mul, map_inv₀, map_sum]
      simp only [map_mul, hco]
      rw [hyeq t, mul_comm, ← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    exact ⟨_, by rw [Set.mem_preimage, hval]; exact hy' t, hval⟩
  have hyeq' : y = ∑ t, algebraMap T F₁ (β t) * y' t + ∑ i, algebraMap T F₁ (r' i) * θ (w i) := by
    apply mul_left_cancel₀ hϖ
    rw [← hr]
    simp only [hr', map_add, map_sum, map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_add, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [mul_left_comm, ← hyeq t, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [hyeq']
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun t _ => ?_) (Submodule.sum_mem _ fun i _ => ?_)
  · rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem' t))
  · rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w i, hw i, rfl⟩)

theorem gaussAt (hinj : Function.Injective (algebraMap T F₁)) (c₀ : O →+* F) (θ : F →+* F₁)
    (hc : θ.comp c₀ = (algebraMap T F₁).comp (algebraMap O T)) (π : O)
    (hπ : Irreducible (algebraMap O T π)) (W : Subalgebra T F₁)
    (hW : ∀ x : F₁, ∃ n : ℕ, algebraMap T F₁ (algebraMap O T π) ^ n * x ∈ W)
    (hV : ∀ (s : ResidueField T →ₐ[ResidueField O] Ω) (lam : ↥(Subalgebra.toSubmodule W) →ₗ[T] Ω) (n : ℕ)
      (r : Fin n → T) (w : Fin n → F) (hw : ∀ (i : Fin n), θ (w i) ∈ Subalgebra.toSubmodule W), ∀ y ∈ W,
      ∑ i : Fin n, algebraMap T F₁ (r i) * θ (w i) = algebraMap T F₁ (algebraMap O T π) * y →
        ∑ i : Fin n, s (residue T (r i)) * lam ⟨θ (w i), hw i⟩ = 0) :
    GlobalTheory.Desc.GaussAt (algebraMap T F₁) (maximalIdeal T) θ (θ ⁻¹' (W : Set F₁)) (W : Set F₁) := by
  classical
  have hϖ0 : algebraMap O T π ≠ 0 := hπ.ne_zero
  have hco : ∀ x, θ (c₀ x) = algebraMap T F₁ (algebraMap O T x) := fun x => RingHom.congr_fun hc x
  have claim : ∀ (K : ℕ) (v : F₁), v ∈ W → ∀ (m : ℕ) (r : Fin m → T) (u : Fin m → F), (∀ i, θ (u i) ∈ W) →
      algebraMap T F₁ (algebraMap O T π) ^ K * v = ∑ i, algebraMap T F₁ (r i) * θ (u i) →
      v ∈ Submodule.span T (θ '' (θ ⁻¹' (W : Set F₁))) := by
    intro K
    induction K with
    | zero =>
      intro v _ m r u hu he
      rw [pow_zero, one_mul] at he
      rw [he]
      exact Submodule.sum_mem _ fun i _ => by
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u i, hu i, rfl⟩)
    | succ k ih =>
      intro v hv m r u hu he
      have hvk : algebraMap T F₁ (algebraMap O T π) ^ k * v ∈ W :=
        W.mul_mem (W.pow_mem (W.algebraMap_mem _) _) hv
      have hsp := div_span (Ω := Ω) hinj hc hπ hV u hu Finset.univ r (by simp) _ hvk (by rw [← he, pow_succ]; ring)
      obtain ⟨m', f, g, hfg⟩ := Submodule.mem_span_set'.mp hsp
      choose u' hu' hgu using fun j => (g j).2
      exact ih v hv m' f u' hu' (by rw [← hfg]; simp only [Algebra.smul_def, hgu])
  rintro v ⟨d, hd0, hdv⟩
  constructor
  · intro hv
    refine ⟨1, (maximalIdeal.isMaximal T).ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one), ?_⟩
    rw [map_one, one_mul, mem_spanBy_iff]
    obtain ⟨n, r, t, ht, hdv'⟩ := hdv
    choose u hu using ht
    choose N hN using fun i => hW (θ (u i))
    obtain ⟨K, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (mul_ne_zero (pow_ne_zero (∑ i, N i) hϖ0) hd0) hπ
    refine claim K v hv n (fun i => ↑e⁻¹ * r i) (fun i => c₀ π ^ (∑ j, N j) * u i) (fun i => ?_) ?_
    · rw [map_mul, map_pow, hco, ← Nat.sub_add_cancel (Finset.single_le_sum (fun j _ => Nat.zero_le (N j))
        (Finset.mem_univ i)), pow_add, mul_assoc]
      exact W.mul_mem (W.pow_mem (W.algebraMap_mem _) _) (hN i)
    · have h2 : algebraMap T F₁ (↑e * algebraMap O T π ^ K) * v =
          algebraMap T F₁ (algebraMap O T π ^ (∑ j, N j)) * ∑ i, algebraMap T F₁ (r i) * t i := by
        rw [← he, map_mul, mul_assoc, hdv']
      have hu' : ∀ i, t i = θ (u i) := fun i => (hu i).symm
      simp only [hu'] at h2
      calc algebraMap T F₁ (algebraMap O T π) ^ K * v
          = algebraMap T F₁ ↑e⁻¹ * (algebraMap T F₁ (↑e * algebraMap O T π ^ K) * v) := by
            rw [map_mul, map_pow, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
        _ = ∑ i, algebraMap T F₁ (↑e⁻¹ * r i) * θ (c₀ π ^ (∑ j, N j) * u i) := by
            rw [h2, Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [map_mul, map_pow, hco]
            ring
  · rintro ⟨s, hs, hsv⟩
    rw [mem_spanBy_iff] at hsv
    have hsW : algebraMap T F₁ s * v ∈ Subalgebra.toSubmodule W :=
      Submodule.span_le.mpr (by rintro x ⟨a, ha, rfl⟩; exact ha) hsv
    obtain ⟨u, rfl⟩ : IsUnit s := by
      by_contra hnu
      exact hs ((IsLocalRing.mem_maximalIdeal s).mpr hnu)
    have hv : v = algebraMap T F₁ ↑u⁻¹ * (algebraMap T F₁ ↑u * v) := by
      rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
    show v ∈ W
    rw [hv]
    exact W.mul_mem (W.algebraMap_mem _) hsW

end Main

end GlobalTheory.VandermondeEmbeddingVanishing
