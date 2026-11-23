import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.GlOperatorsFormRepresentation
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LiePolarizationDerEqZeroOfDisjoint
import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.StandardPathBasisAnyRing

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.Joints Formalism.MainNotions.LemmaBAlt

section

variable {R : Type} [CommRing R] {N r K : ℕ}

theorem multideg_mapDomain_headVar (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    multideg (m.mapDomain (plVar (K := K))) i = multideg m i := by
  classical
  unfold multideg
  rw [Fin.sum_univ_add]
  have h1 : ∀ c : Fin r, (m.mapDomain (plVar (K := K))) (i, Fin.castAdd K c) = m (i, c) := by
    intro c
    have : (i, Fin.castAdd K c) = plVar (K := K) (i, c) := rfl
    rw [this, Finsupp.mapDomain_apply]
    intro a b h
    simp only [plVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective r K h.2)
  have h2 : ∀ c : Fin K, (m.mapDomain (plVar (K := K))) (i, Fin.natAdd r c) = 0 := by
    intro c
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨l, a⟩, h⟩
    simp only [plVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

theorem multideg_mapDomain_tailVar (m : Fin N × Fin K →₀ ℕ) (i : Fin N) :
    multideg (m.mapDomain (tanVar (r := r))) i = multideg m i := by
  classical
  unfold multideg
  rw [Fin.sum_univ_add]
  have h1 : ∀ c : Fin K, (m.mapDomain (tanVar (r := r))) (i, Fin.natAdd r c) = m (i, c) := by
    intro c
    have : (i, Fin.natAdd r c) = tanVar (r := r) (i, c) := rfl
    rw [this, Finsupp.mapDomain_apply]
    intro a b h
    simp only [tanVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective K r h.2)
  have h2 : ∀ c : Fin r, (m.mapDomain (tanVar (r := r))) (i, Fin.castAdd K c) = 0 := by
    intro c
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨⟨l, a⟩, h⟩
    simp only [tanVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  simp only [h1, h2, Finset.sum_const_zero, zero_add]

theorem multideg_add_apply {n : ℕ} (x y : Fin N × Fin n →₀ ℕ) (i : Fin N) :
    multideg (x + y) i = multideg x i + multideg y i := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

theorem rename_mul_rename_mem_multihomogeneous {b' b'' B : Fin N → ℕ} (hb : ∀ i, b' i + b'' i = B i) {G1 : MvPolynomial (Fin N × Fin r) R}
    {G2 : MvPolynomial (Fin N × Fin K) R} (h1 : G1 ∈ Pol R r b') (h2 : G2 ∈ Pol R K b'') :
    rename (plVar (K := K)) G1 * rename (tanVar (r := r)) G2 ∈ Pol R (r + K) B := by
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at h1 h2 ⊢
  intro m hm
  have hm' := MvPolynomial.support_mul _ _ (Finset.mem_coe.1 hm)
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.1 hm'
  have g1 := MvPolynomial.support_rename_of_injective (p := G1) (f := plVar (K := K)) (by
    intro a b h
    simp only [plVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective r K h.2))
  have g2 := MvPolynomial.support_rename_of_injective (p := G2) (f := tanVar (r := r)) (by
    intro a b h
    simp only [tanVar, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective K r h.2))
  rw [g1] at hm1
  rw [g2] at hm2
  obtain ⟨n1, hn1, rfl⟩ := Finset.mem_image.1 hm1
  obtain ⟨n2, hn2, rfl⟩ := Finset.mem_image.1 hm2
  intro i
  rw [multideg_add_apply, multideg_mapDomain_headVar, multideg_mapDomain_tailVar, h1 (Finset.mem_coe.2 hn1) i, h2 (Finset.mem_coe.2 hn2) i, hb i]

end

theorem productBasis_mem_multihomogeneous (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    (x : PIdx r K LL B) : pvec R r K LL B x ∈ Pol R (r + K) B := by
  obtain ⟨b', b'', hb, ⟨P1, h1⟩, ⟨P2, h2⟩⟩ := x.2.1
  unfold pvec PsiPl PsiTan
  refine rename_mul_rename_mem_multihomogeneous hb ?_ ?_
  · rw [← h1]
    exact standardWord_mem_multihomogeneous R P1 _ (h1 ▸ x.2.2.1)
  · rw [← h2]
    exact standardWord_mem_multihomogeneous R P2 _ (h2 ▸ x.2.2.2)

theorem rename_mul_rename_mem_span_productBasis (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ)
    {b' b'' : Fin N → ℕ} (hb : ∀ i, b' i + b'' i = B i) {G1 : MvPolynomial (Fin N × Fin r) R}
    {G2 : MvPolynomial (Fin N × Fin K) R} (h1 : G1 ∈ Pol R r b') (h2 : G2 ∈ Pol R K b'') :
    rename (plVar (K := K)) G1 * rename (tanVar (r := r)) G2 ∈ Submodule.span R (Set.range (pvec R r K LL B)) := by
  rw [← (standardPath_basis_any_ring R N r LL b').2] at h1
  rw [← (standardPath_basis_any_ring R N K LL b'').2] at h2
  induction h1 using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨P1, I', hI', rfl⟩ := hy
    induction h2 using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨P2, I'', hI'', rfl⟩ := hz
      exact Submodule.subset_span
        ⟨⟨((P1.mu, I'), (P2.mu, I'')), ⟨b', b'', hb, ⟨P1, rfl⟩, ⟨P2, rfl⟩⟩, hI', hI''⟩, rfl⟩
    | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add, mul_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul, mul_smul_comm]; exact Submodule.smul_mem _ _ ha
  | zero => rw [map_zero, zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ _ ha

theorem headVar_injective (N r K : ℕ) : Function.Injective (plVar (N := N) (r := r) (K := K)) := by
  intro a b h
  simp only [plVar, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective r K h.2)

theorem tailVar_injective (N r K : ℕ) : Function.Injective (tanVar (N := N) (r := r) (K := K)) := by
  intro a b h
  simp only [tanVar, Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.natAdd_injective K r h.2)

theorem finsupp_eq_head_add_tail {N r K : ℕ} (m : Fin N × Fin (r + K) →₀ ℕ) :
    m = (m.comapDomain plVar (headVar_injective N r K).injOn).mapDomain plVar +
      (m.comapDomain tanVar (tailVar_injective N r K).injOn).mapDomain tanVar := by
  classical
  ext ⟨i, c⟩
  rw [Finsupp.add_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) c
  · have e1 : (i, Fin.castAdd K a) = plVar (K := K) (i, a) := rfl
    rw [e1, Finsupp.mapDomain_apply (headVar_injective N r K), Finsupp.comapDomain_apply,
      Finsupp.mapDomain_of_notMem_range, add_zero]
    rintro ⟨⟨l, b⟩, h⟩
    simp only [tanVar, plVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  · have e1 : (i, Fin.natAdd r a) = tanVar (r := r) (i, a) := rfl
    rw [e1, Finsupp.mapDomain_apply (tailVar_injective N r K), Finsupp.comapDomain_apply,
      Finsupp.mapDomain_of_notMem_range, zero_add]
    rintro ⟨⟨l, b⟩, h⟩
    simp only [tanVar, plVar, Prod.mk.injEq] at h
    have := congrArg Fin.val h.2
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega

theorem monomial_mem_multihomogeneous_multideg (R : Type) [CommRing R] {N n : ℕ} (m : Fin N × Fin n →₀ ℕ) :
    monomial m (1 : R) ∈ Pol R n (fun i => multideg m i) := by
  classical
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m' hm'
  have := MvPolynomial.support_monomial_subset (Finset.mem_coe.1 hm')
  rw [Finset.mem_singleton] at this
  subst this
  intro i
  rfl

theorem span_productBasis_eq_multihomogeneous (R : Type) [CommRing R] (N r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    Submodule.span R (Set.range (pvec R r K LL B)) = Pol R (r + K) B := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact productBasis_mem_multihomogeneous R N r K LL B x
  · intro G hG
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG
    rw [G.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hB := hG (Finset.mem_coe.2 hm)
    set m1 := m.comapDomain plVar (headVar_injective N r K).injOn with hm1
    set m2 := m.comapDomain tanVar (tailVar_injective N r K).injOn with hm2
    have hs : m = m1.mapDomain plVar + m2.mapDomain tanVar := finsupp_eq_head_add_tail m
    have hmon : monomial m (coeff m G) = coeff m G •
        (rename (plVar (K := K)) (monomial m1 (1 : R)) * rename (tanVar (r := r)) (monomial m2 (1 : R))) := by
      rw [rename_monomial, rename_monomial, monomial_mul, ← hs, smul_monomial, one_mul, smul_eq_mul, mul_one]
    rw [hmon]
    refine Submodule.smul_mem _ _ (rename_mul_rename_mem_span_productBasis R N r K LL B (b' := fun i => multideg m1 i)
      (b'' := fun i => multideg m2 i) ?_ (monomial_mem_multihomogeneous_multideg R m1) (monomial_mem_multihomogeneous_multideg R m2))
    intro i
    have := hB i
    rw [hs, multideg_add_apply, multideg_mapDomain_headVar, multideg_mapDomain_tailVar] at this
    exact this

end Formalism.MainNotions.G.ColumnFamilies
