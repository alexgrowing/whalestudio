import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsResEqOfUnitInChart

noncomputable section
namespace GlobalTheory.HenselZero

open IsLocalRing GlobalTheory.SqZero

theorem formallySmooth_quotient {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [Fintype ι] [DecidableEq ι] (f : ι → S) (τ : ι → Derivation R S S)
    (h : IsUnit (Matrix.of fun i k => τ k (f i)).det) :
    Algebra.FormallySmooth R (S ⧸ Ideal.span (Set.range f)) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun B _ _ I hI g => ?_
  obtain ⟨g', hg'⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (g.comp (Ideal.Quotient.mkₐ R _))
  have hg : ∀ a, Ideal.Quotient.mk I (g' a) = g (Ideal.Quotient.mk _ a) := fun a => congr($hg' a)
  have hf : ∀ i, g' (f i) ∈ I := fun i => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  let M : Matrix ι ι B := Matrix.of fun i k => g' (τ k (f i))
  have hM : IsUnit M.det := by
    have := h.map g'
    rw [AlgHom.map_det] at this
    exact this
  let t : ι → B := M⁻¹.mulVec fun i => - g' (f i)
  have ht : ∀ k, t k ∈ I := fun k => Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (neg_mem (hf i))
  have hMt : M.mulVec t = fun i => - g' (f i) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM, Matrix.one_mulVec]
  have h0 : ∀ i j, t i * t j = 0 := fun i j => by
    have := Ideal.mul_mem_mul (ht i) (ht j)
    rwa [← sq, hI] at this
  refine ⟨Ideal.Quotient.liftₐ _ (addDers τ g' t h0) fun a ha => ?_, ?_⟩
  · refine (Ideal.span_le (I := RingHom.ker (addDers τ g' t h0))).2 ?_ ha
    rintro _ ⟨i, rfl⟩
    have : ∑ k, g' (τ k (f i)) * t k = - g' (f i) := congrFun hMt i
    show addDers τ g' t h0 (f i) = 0
    rw [addDers_apply, this, add_neg_cancel]
  · refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun a => ?_)
    show Ideal.Quotient.mk I (addDers τ g' t h0 a) = g (Ideal.Quotient.mk _ a)
    rw [addDers_apply, map_add, hg, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (ht k)), add_zero]

theorem exists_derivation_lift {R S K : Type} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
    [CommRing K] [Algebra R K] (u : S →ₐ[R] K) (hu : Function.Surjective u) (D : S →ₗ[R] K)
    (hD : ∀ a b, D (a * b) = u a * D b + u b * D a) : ∃ τ : Derivation R S S, ∀ a, u (τ a) = D a := by
  let _ : Algebra S K := (u : S →+* K).toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq fun r => (u.commutes r).symm
  let D' : Derivation R S K := Derivation.mk' D hD
  obtain ⟨l, hl⟩ := Module.projective_lifting_property (Algebra.linearMap S K) D'.liftKaehlerDifferential hu
  refine ⟨l.compDer (KaehlerDifferential.D R S), fun a => ?_⟩
  exact (congr($hl (KaehlerDifferential.D R S a))).trans (D'.liftKaehlerDifferential_comp_D a)

theorem exists_algHom_ker_eq {O S ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra O S]
    [Algebra.FormallySmooth O S] [Fintype ι] [DecidableEq ι] (f : ι → S) (u : S →+* ResidueField O)
    (hu : ∀ r, u (algebraMap O S r) = residue O r) (hf : ∀ i, u (f i) = 0)
    (χ : ι → (S →+* DualNumber (ResidueField O))) (h₁ : ∀ k a, (χ k a).fst = u a)
    (h₂ : ∀ k r, χ k (algebraMap O S r) = algebraMap (ResidueField O) _ (residue O r))
    (hd : (Matrix.of fun i k => (χ k (f i)).snd).det ≠ 0)
    (hm : maximalIdeal S ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map (algebraMap O S)) :
    ∃ ψ : S →ₐ[O] O, (∀ a, residue O (ψ a) = u a) ∧ RingHom.ker ψ = Ideal.span (Set.range f) := by
  let u' : S →ₐ[O] ResidueField O := ⟨u, hu⟩
  have hs : Function.Surjective u' := fun c => by
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨_, hu r⟩
  have hker : RingHom.ker u = maximalIdeal S := eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective u hs)
  have hτ : ∀ k, ∃ τ : Derivation O S S, ∀ a, u (τ a) = (χ k a).snd := fun k =>
    exists_derivation_lift u' hs
      { toFun := fun a => (χ k a).snd
        map_add' := fun a b => by simp
        map_smul' := fun r a => by
          rw [Algebra.smul_def, map_mul, h₂, Algebra.smul_def]
          simp [TrivSqZeroExt.algebraMap_eq_inl] }
      fun a b => by simp [h₁, mul_comm]; rfl
  choose τ hτ using hτ
  have hunit : IsUnit (Matrix.of fun i k => τ k (f i)).det := by
    rw [← notMem_maximalIdeal, ← hker, RingHom.mem_ker, RingHom.map_det]
    refine fun h => hd (Eq.trans ?_ h)
    congr 1
    ext i k
    exact (hτ k _).symm
  have := formallySmooth_quotient f τ hunit
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker u' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hf i)
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal O)
    (Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) u' fun a ha => hle ha)
  let ψ : S →ₐ[O] O := g.comp (Ideal.Quotient.mkₐ O _)
  have hψ : ∀ a, residue O (ψ a) = u a := fun a => congr($hg (Ideal.Quotient.mk _ a))
  have hle' : Ideal.span (Set.range f) ≤ RingHom.ker ψ := fun a ha => by
    show g (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  refine ⟨ψ, hψ, le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal S)
    (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) fun a ha => ?_) hle'⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have ha₀ : ψ a = 0 := ha
  have ha' : a ∈ maximalIdeal S := by rw [← hker, RingHom.mem_ker, ← hψ, ha₀, map_zero]
  replace ha' := hm ha'
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at ha'
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 ha'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hc
  refine Submodule.add_mem_sup hb (Submodule.smul_mem_smul (r := algebraMap O S π) (n := c) ?_ ?_)
  · rw [← hker, RingHom.mem_ker, hu, residue_eq_zero_iff]
    exact hπ.not_isUnit
  · have hb₀ : ψ b = 0 := hle' hb
    rw [map_add, hb₀, zero_add, map_mul, AlgHom.commutes] at ha₀
    exact (mul_eq_zero.1 ha₀).resolve_left hπ.ne_zero

end GlobalTheory.HenselZero
end
