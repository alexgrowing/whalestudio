import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AutomorphicFormsFiniteIdeal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterTensorProductMemRange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutFinLit GlobalTheory.Published.AutFin
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.EnvCentre

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

theorem adjoin_range_ι_eq_top (L : Type) [LieRing L] [LieAlgebra ℂ L] :
    Algebra.adjoin ℂ (Set.range (ι ℂ : L → UniversalEnvelopingAlgebra ℂ L)) = ⊤ := by
  have hs : Function.Surjective (mkAlgHom ℂ L) := by
    intro z
    obtain ⟨t, rfl⟩ := Quot.exists_rep z
    exact ⟨t, rfl⟩
  rw [← (AlgHom.range_eq_top _).mpr hs, ← Algebra.map_top, ← TensorAlgebra.adjoin_range_ι,
    AlgHom.map_adjoin, ← Set.range_comp]
  rfl

theorem mem_of_ι_mem {L C : Type} [LieRing L] [LieAlgebra ℂ L] [Ring C] [Algebra ℂ C]
    (f : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] C) (S : Subalgebra ℂ C)
    (h : ∀ x, f (ι ℂ x) ∈ S) (a : UniversalEnvelopingAlgebra ℂ L) : f a ∈ S := by
  have : Algebra.adjoin ℂ (Set.range (ι ℂ : L → UniversalEnvelopingAlgebra ℂ L)) ≤ S.comap f :=
    Algebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact h x)
  rw [adjoin_range_ι_eq_top] at this
  exact this Algebra.mem_top

theorem commute_of_ι {L₁ L₂ C : Type} [LieRing L₁] [LieAlgebra ℂ L₁] [LieRing L₂]
    [LieAlgebra ℂ L₂] [Ring C] [Algebra ℂ C]
    (f : UniversalEnvelopingAlgebra ℂ L₁ →ₐ[ℂ] C) (g : UniversalEnvelopingAlgebra ℂ L₂ →ₐ[ℂ] C)
    (h : ∀ x y, Commute (f (ι ℂ x)) (g (ι ℂ y))) (a : UniversalEnvelopingAlgebra ℂ L₁)
    (b : UniversalEnvelopingAlgebra ℂ L₂) : Commute (f a) (g b) := by
  have h1 : ∀ y, f a ∈ Subalgebra.centralizer ℂ {g (ι ℂ y)} := fun y =>
    mem_of_ι_mem f _ (fun x => by
      rw [Subalgebra.mem_centralizer_iff]; rintro _ rfl; exact ((h x y).eq).symm) a
  have h2 : g b ∈ Subalgebra.centralizer ℂ {f a} :=
    mem_of_ι_mem g _ (fun y => by
      rw [Subalgebra.mem_centralizer_iff]; rintro _ rfl
      have := h1 y; rw [Subalgebra.mem_centralizer_iff] at this
      exact (this _ rfl).symm) b
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact h2 _ rfl

section Decomp

variable {M L₁ L₂ : Type} [LieRing M] [LieAlgebra ℂ M] [LieRing L₁] [LieAlgebra ℂ L₁]
  [LieRing L₂] [LieAlgebra ℂ L₂]

noncomputable def fwd (j₁ : L₁ →ₗ⁅ℂ⁆ M) (j₂ : L₂ →ₗ⁅ℂ⁆ M) (hc : ∀ x y, ⁅j₁ x, j₂ y⁆ = 0) :
    UniversalEnvelopingAlgebra ℂ L₁ ⊗[ℂ] UniversalEnvelopingAlgebra ℂ L₂ →ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ M :=
  Algebra.TensorProduct.lift (lift ℂ ((ι ℂ).comp j₁)) (lift ℂ ((ι ℂ).comp j₂))
    (commute_of_ι _ _ (fun x y => by
      rw [lift_ι_apply, lift_ι_apply, commute_iff_lie_eq, LieHom.comp_apply, LieHom.comp_apply,
        ← LieHom.map_lie, hc, map_zero]))

noncomputable def bwdLie (p₁ : M →ₗ⁅ℂ⁆ L₁) (p₂ : M →ₗ⁅ℂ⁆ L₂) :
    M →ₗ⁅ℂ⁆ UniversalEnvelopingAlgebra ℂ L₁ ⊗[ℂ] UniversalEnvelopingAlgebra ℂ L₂ :=
  { toLinearMap :=
      ((Algebra.TensorProduct.includeLeft : UniversalEnvelopingAlgebra ℂ L₁ →ₐ[ℂ] _).toLinearMap ∘ₗ
          ((ι ℂ : L₁ →ₗ⁅ℂ⁆ _) : L₁ →ₗ[ℂ] _) ∘ₗ (p₁ : M →ₗ[ℂ] L₁)) +
        ((Algebra.TensorProduct.includeRight :
            UniversalEnvelopingAlgebra ℂ L₂ →ₐ[ℂ] _).toLinearMap ∘ₗ
          ((ι ℂ : L₂ →ₗ⁅ℂ⁆ _) : L₂ →ₗ[ℂ] _) ∘ₗ (p₂ : M →ₗ[ℂ] L₂))
    map_lie' := by
      intro x y
      change ι ℂ (p₁ ⁅x, y⁆) ⊗ₜ[ℂ] 1 + 1 ⊗ₜ[ℂ] ι ℂ (p₂ ⁅x, y⁆) =
        ⁅ι ℂ (p₁ x) ⊗ₜ[ℂ] 1 + 1 ⊗ₜ[ℂ] ι ℂ (p₂ x), ι ℂ (p₁ y) ⊗ₜ[ℂ] 1 + 1 ⊗ₜ[ℂ] ι ℂ (p₂ y)⁆
      simp only [LieHom.map_lie, LieRing.of_associative_ring_bracket]
      generalize ι ℂ (p₁ x) = a
      generalize ι ℂ (p₁ y) = c
      generalize ι ℂ (p₂ x) = b
      generalize ι ℂ (p₂ y) = d
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.sub_tmul, TensorProduct.tmul_sub]
      abel }

theorem bwdLie_apply (p₁ : M →ₗ⁅ℂ⁆ L₁) (p₂ : M →ₗ⁅ℂ⁆ L₂) (x : M) :
    bwdLie p₁ p₂ x = ι ℂ (p₁ x) ⊗ₜ[ℂ] 1 + 1 ⊗ₜ[ℂ] ι ℂ (p₂ x) := rfl

theorem fwd_tmul (j₁ : L₁ →ₗ⁅ℂ⁆ M) (j₂ : L₂ →ₗ⁅ℂ⁆ M) (hc : ∀ x y, ⁅j₁ x, j₂ y⁆ = 0) (a b) :
    fwd j₁ j₂ hc (a ⊗ₜ b) = lift ℂ ((ι ℂ).comp j₁) a * lift ℂ ((ι ℂ).comp j₂) b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

noncomputable def decomp (j₁ : L₁ →ₗ⁅ℂ⁆ M) (j₂ : L₂ →ₗ⁅ℂ⁆ M) (p₁ : M →ₗ⁅ℂ⁆ L₁)
    (p₂ : M →ₗ⁅ℂ⁆ L₂) (hc : ∀ x y, ⁅j₁ x, j₂ y⁆ = 0) (h11 : ∀ x, p₁ (j₁ x) = x)
    (h21 : ∀ x, p₂ (j₁ x) = 0) (h12 : ∀ y, p₁ (j₂ y) = 0) (h22 : ∀ y, p₂ (j₂ y) = y)
    (hs : ∀ z, j₁ (p₁ z) + j₂ (p₂ z) = z) :
    (UniversalEnvelopingAlgebra ℂ L₁ ⊗[ℂ] UniversalEnvelopingAlgebra ℂ L₂) ≃ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ M :=
  AlgEquiv.ofAlgHom (fwd j₁ j₂ hc) (lift ℂ (bwdLie p₁ p₂))
    (by
      ext z
      simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply, lift_ι_apply,
        bwdLie_apply, map_add, fwd_tmul, map_one, mul_one, one_mul, AlgHom.id_apply]
      rw [← map_add, hs])
    (by
      apply Algebra.TensorProduct.ext
      · ext x
        simp only [LieHom.comp_apply, AlgHom.coe_toLieHom, AlgHom.comp_apply,
          Algebra.TensorProduct.includeLeft_apply, fwd_tmul, map_one, mul_one, lift_ι_apply,
          AlgHom.id_apply]
        rw [bwdLie_apply, h11, h21, map_zero,
          TensorProduct.tmul_zero, add_zero]
      · ext y
        change lift ℂ (bwdLie p₁ p₂) (fwd j₁ j₂ hc (1 ⊗ₜ[ℂ] ι ℂ y)) = 1 ⊗ₜ[ℂ] ι ℂ y
        rw [fwd_tmul, map_one, one_mul, lift_ι_apply, LieHom.comp_apply, lift_ι_apply,
          bwdLie_apply, h12, h22, map_zero,
          TensorProduct.zero_tmul, zero_add])

theorem decomp_left (j₁ : L₁ →ₗ⁅ℂ⁆ M) (j₂ : L₂ →ₗ⁅ℂ⁆ M) (p₁ p₂ hc h11 h21 h12 h22 hs) (a) :
    decomp j₁ j₂ p₁ p₂ hc h11 h21 h12 h22 hs (a ⊗ₜ 1) = lift ℂ ((ι ℂ).comp j₁) a := by
  rw [decomp, AlgEquiv.ofAlgHom_apply, fwd_tmul, map_one, mul_one]

theorem decomp_right (j₁ : L₁ →ₗ⁅ℂ⁆ M) (j₂ : L₂ →ₗ⁅ℂ⁆ M) (p₁ p₂ hc h11 h21 h12 h22 hs) (b) :
    decomp j₁ j₂ p₁ p₂ hc h11 h21 h12 h22 hs (1 ⊗ₜ b) = lift ℂ ((ι ℂ).comp j₂) b := by
  rw [decomp, AlgEquiv.ofAlgHom_apply, fwd_tmul, map_one, one_mul]

end Decomp

section Sum

open DirectSum

variable {σ : Type} [DecidableEq σ] (L : σ → Type) [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]

theorem toLieAlgebra_of {N : Type} [LieRing N] [LieAlgebra ℂ N] (f : ∀ i, L i →ₗ⁅ℂ⁆ N) (hf)
    (i : σ) (x : L i) : toLieAlgebra N f hf (of L i x) = f i x :=
  toModule_lof ℂ (φ := fun i => (f i : L i →ₗ[ℂ] N)) i x

noncomputable def inclRest (a : σ) : (⨁ k : {i // i ≠ a}, L k.1) →ₗ⁅ℂ⁆ ⨁ i, L i :=
  toLieAlgebra _ (fun k : {i // i ≠ a} => lieAlgebraOf ℂ σ L k.1)
    (fun _ _ hkl x y => lie_of_of_ne L (fun h => hkl (Subtype.ext h)) x y)

noncomputable def projRestAt (a i : σ) : L i →ₗ⁅ℂ⁆ ⨁ k : {i // i ≠ a}, L k.1 :=
  if h : i = a then 0 else lieAlgebraOf ℂ {i // i ≠ a} (fun k => L k.1) ⟨i, h⟩

theorem projRestAt_self (a : σ) (x : L a) : projRestAt L a a x = 0 := by
  rw [projRestAt, dif_pos rfl]; rfl

theorem projRestAt_ne (a i : σ) (h : i ≠ a) (x : L i) :
    projRestAt L a i x = of (fun k : {i // i ≠ a} => L k.1) ⟨i, h⟩ x := by
  rw [projRestAt, dif_neg h]; rfl

noncomputable def projRest (a : σ) : (⨁ i, L i) →ₗ⁅ℂ⁆ ⨁ k : {i // i ≠ a}, L k.1 :=
  toLieAlgebra _ (projRestAt L a) (fun i j hij x y => by
    by_cases hi : i = a
    · subst hi; rw [projRestAt_self, zero_lie]
    by_cases hj : j = a
    · subst hj; rw [projRestAt_self, lie_zero]
    rw [projRestAt_ne L a i hi, projRestAt_ne L a j hj]
    exact lie_of_of_ne (fun k : {i // i ≠ a} => L k.1) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
      (fun h => hij (congrArg Subtype.val h)) x y)

theorem inclRest_of (a : σ) (k : {i // i ≠ a}) (x : L k.1) :
    inclRest L a (of (fun k : {i // i ≠ a} => L k.1) k x) = of L k.1 x :=
  toLieAlgebra_of (fun k : {i // i ≠ a} => L k.1) _ _ k x

theorem projRest_of (a i : σ) (x : L i) : projRest L a (of L i x) = projRestAt L a i x :=
  toLieAlgebra_of L _ _ i x

theorem comp_of_same (a : σ) (x : L a) : lieAlgebraComponent ℂ σ L a (of L a x) = x :=
  of_eq_same a x

theorem comp_of_ne (a i : σ) (h : i ≠ a) (x : L i) :
    lieAlgebraComponent ℂ σ L a (of L i x) = 0 :=
  of_eq_of_ne i a x h.symm

noncomputable def splitOff (a : σ) :
    (UniversalEnvelopingAlgebra ℂ (L a) ⊗[ℂ]
      UniversalEnvelopingAlgebra ℂ (⨁ k : {i // i ≠ a}, L k.1)) ≃ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ (⨁ i, L i) :=
  decomp (lieAlgebraOf ℂ σ L a) (inclRest L a) (lieAlgebraComponent ℂ σ L a) (projRest L a)
    (fun x y => by
      induction y using DirectSum.induction_on with
      | zero => rw [map_zero, lie_zero]
      | of k y => rw [inclRest_of]; exact lie_of_of_ne L k.2.symm x y
      | add y z hy hz => rw [map_add, lie_add, hy, hz, add_zero])
    (fun x => comp_of_same L a x)
    (fun x => (projRest_of L a a x).trans (projRestAt_self L a x))
    (fun y => by
      induction y using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]
      | of k y => rw [inclRest_of]; exact comp_of_ne L a k.1 k.2 y
      | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero])
    (fun y => by
      induction y using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]
      | of k y => rw [inclRest_of, projRest_of, projRestAt_ne L a k.1 k.2]
      | add y z hy hz => rw [map_add, map_add, hy, hz])
    (fun z => by
      induction z using DirectSum.induction_on with
      | zero => simp only [map_zero, add_zero]
      | of i y =>
        by_cases h : i = a
        · subst h
          rw [comp_of_same, projRest_of, projRestAt_self, map_zero, add_zero]; rfl
        · rw [comp_of_ne L a i h, projRest_of, projRestAt_ne L a i h, map_zero, zero_add]
          exact inclRest_of L a ⟨i, h⟩ y
      | add y z hy hz =>
        simp only [map_add]
        rw [add_add_add_comm, hy, hz])

end Sum

theorem algHom_ext_ι {L C : Type} [LieRing L] [LieAlgebra ℂ L] [Ring C] [Algebra ℂ C]
    {f g : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] C} (h : ∀ x, f (ι ℂ x) = g (ι ℂ x)) : f = g :=
  UniversalEnvelopingAlgebra.hom_ext ℂ (LieHom.ext h)

theorem center_directSum_card (n : ℕ) : ∀ (σ : Type) [Fintype σ] [DecidableEq σ],
    Fintype.card σ = n → ∀ (L : σ → Type) [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)]
    (m : ∀ i, UniversalEnvelopingAlgebra ℂ (L i) →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ (⨁ i, L i)),
    (∀ i x, m i (ι ℂ x) = ι ℂ (DirectSum.of L i x : ⨁ i, L i)) →
    Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (⨁ i, L i)) = Algebra.adjoin ℂ
      (⋃ i, m i '' (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (L i)) : Set _)) := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro σ _ _ hn L _ _ m hm
  rcases isEmpty_or_nonempty σ with he | ⟨⟨a⟩⟩
  · rw [Set.iUnion_of_empty, Algebra.adjoin_empty]
    refine le_antisymm (fun z _ => ?_) bot_le
    refine mem_of_ι_mem (AlgHom.id ℂ _) ⊥ (fun x => ?_) z
    have hx : x = 0 := DFinsupp.ext fun i => isEmptyElim i
    rw [hx, map_zero, map_zero]
    exact zero_mem _
  · let m' : ∀ k : {i // i ≠ a}, UniversalEnvelopingAlgebra ℂ (L k.1) →ₐ[ℂ]
        UniversalEnvelopingAlgebra ℂ (⨁ k : {i // i ≠ a}, L k.1) := fun k =>
      lift ℂ ((ι ℂ).comp (DirectSum.lieAlgebraOf ℂ {i // i ≠ a} (fun k => L k.1) k))
    have hm' : ∀ k x, m' k (ι ℂ x) =
        ι ℂ (DirectSum.of (fun k : {i // i ≠ a} => L k.1) k x) := fun k x => lift_ι_apply _ _ _
    have hlt : Fintype.card {i // i ≠ a} < n :=
      hn ▸ Fintype.card_subtype_lt (x := a) (fun h => h rfl)
    have IH' := IH _ hlt {i // i ≠ a} rfl (fun k => L k.1) m' hm'
    let J : UniversalEnvelopingAlgebra ℂ (⨁ k : {i // i ≠ a}, L k.1) →ₐ[ℂ]
        UniversalEnvelopingAlgebra ℂ (⨁ i, L i) := lift ℂ ((ι ℂ).comp (inclRest L a))
    have hJ : ∀ k u, J (m' k u) = m k.1 u := fun k u => by
      have : J.comp (m' k) = m k.1 := algHom_ext_ι fun x => by
        rw [AlgHom.comp_apply, hm', hm, lift_ι_apply, LieHom.comp_apply, inclRest_of]
      exact AlgHom.congr_fun this u
    have hE1 : ∀ u, splitOff L a (u ⊗ₜ 1) = m a u := fun u => by
      have : lift ℂ ((ι ℂ).comp (DirectSum.lieAlgebraOf ℂ σ L a)) = m a :=
        algHom_ext_ι fun x => by rw [hm, lift_ι_apply]; rfl
      rw [← this]
      exact decomp_left _ _ _ _ _ _ _ _ _ _ u
    have hE2 : ∀ b, splitOff L a (1 ⊗ₜ b) = J b := fun b =>
      decomp_right _ _ _ _ _ _ _ _ _ _ b
    rw [GlobalTheory.CenterTensor.center_eq_adjoin _ _ _ (splitOff L a)]
    simp only [hE1, hE2]
    refine le_antisymm (Algebra.adjoin_le (Set.union_subset ?_ ?_))
      (Algebra.adjoin_le (Set.iUnion_subset fun i => ?_))
    · rintro _ ⟨u, hu, rfl⟩
      exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨a, u, hu, rfl⟩)
    · rintro _ ⟨b, hb, rfl⟩
      rw [IH'] at hb
      refine (Subalgebra.mem_comap _ J b).1 (Algebra.adjoin_le (S := Subalgebra.comap J _) ?_ hb)
      intro y hy
      obtain ⟨k, u, hu, rfl⟩ := Set.mem_iUnion.1 hy
      exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨k.1, u, hu, (hJ k u).symm⟩)
    · rintro _ ⟨u, hu, rfl⟩
      by_cases h : i = a
      · subst h
        exact Algebra.subset_adjoin (Or.inl ⟨u, hu, rfl⟩)
      · refine Algebra.subset_adjoin (Or.inr ⟨m' ⟨i, h⟩ u, ?_, hJ ⟨i, h⟩ u⟩)
        rw [IH']
        exact Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨⟨i, h⟩, u, hu, rfl⟩)

theorem center_directSum : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : ι → Type) [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℂ (L i)] (m : ∀ i, UniversalEnvelopingAlgebra ℂ (L i) →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ (⨁ i, L i)), (∀ i x, m i (UniversalEnvelopingAlgebra.ι ℂ x) = UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of L i x : ⨁ i, L i)) → Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (⨁ i, L i)) = Algebra.adjoin ℂ (⋃ i, m i '' (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (L i)) : Set _)) :=
  fun σ _ _ L _ _ m hm => center_directSum_card _ σ rfl L m hm

end GlobalTheory.EnvCentre
