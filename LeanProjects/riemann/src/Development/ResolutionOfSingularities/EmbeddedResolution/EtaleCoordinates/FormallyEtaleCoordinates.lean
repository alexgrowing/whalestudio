import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
open scoped TensorProduct

namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

section

private theorem exists_minimal_spanning_finset {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] (C : Set V) (bb : ι → V) :
    ∀ (n : ℕ) (J : Finset ι), J.card ≤ n →
      Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤ →
      ∃ J' : Finset ι, Submodule.span K (C ∪ bb '' (↑J' : Set ι)) = ⊤ ∧
        ∀ j ∈ J', Submodule.span K (C ∪ bb '' (↑(J'.erase j) : Set ι)) ≠ ⊤ := by
  intro n
  induction n with
  | zero =>
      intro J hcard hJ
      refine ⟨J, hJ, fun j hj => ?_⟩
      have hpos : 0 < J.card := Finset.card_pos.mpr ⟨j, hj⟩
      exact absurd hcard (by omega)
  | succ n ih =>
      intro J hcard hJ
      by_cases hs : ∃ j ∈ J, Submodule.span K (C ∪ bb '' (↑(J.erase j) : Set ι)) = ⊤
      · obtain ⟨j, hjJ, hPj⟩ := hs
        refine ih (J.erase j) ?_ hPj
        have hce : (J.erase j).card = J.card - 1 := Finset.card_erase_of_mem hjJ
        omega
      · push Not at hs
        exact ⟨J, hJ, hs⟩

private theorem span_union_image_erase_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ι : Type*} [DecidableEq ι] {C : Set V} {bb : ι → V} {J : Finset ι} {j0 : ι}
    (hJtop : Submodule.span K (C ∪ bb '' (↑J : Set ι)) = ⊤)
    (hb : bb j0 ∈ Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι))) :
    Submodule.span K (C ∪ bb '' (↑(J.erase j0) : Set ι)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hJtop, Submodule.span_le]
  rintro v (hv | ⟨j, hj, rfl⟩)
  · exact Submodule.subset_span (Set.mem_union_left _ hv)
  · by_cases hjj : j = j0
    · rw [hjj]
      exact hb
    · exact Submodule.subset_span (Set.mem_union_right _
        ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hjj, Finset.mem_coe.mp hj⟩), rfl⟩)

theorem exists_basis_sum_of_linearIndependent {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (h : ℕ)
    (c : Fin h → V) (hc : LinearIndependent K c) :
    ∃ (J : Finset ι) (B : Module.Basis (Fin h ⊕ {j : ι // j ∈ J}) K V),
      (∀ i : Fin h, B (Sum.inl i) = c i) ∧
        ∀ j : {j : ι // j ∈ J}, B (Sum.inr j) = b (j : ι) := by
  classical
  have hPuniv : Submodule.span K
      (Set.range c ∪ (⇑b) '' (↑(Finset.univ : Finset ι) : Set ι)) = ⊤ := by
    refine le_antisymm le_top ?_
    have hsub : Set.range (⇑b) ⊆ Set.range c ∪ (⇑b) '' (↑(Finset.univ : Finset ι) : Set ι) := by
      rintro _ ⟨i, rfl⟩
      exact Set.mem_union_right _ ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), rfl⟩
    calc (⊤ : Submodule K V) = Submodule.span K (Set.range (⇑b)) := b.span_eq.symm
      _ ≤ _ := Submodule.span_mono hsub
  obtain ⟨J, hJtop, hJmin⟩ :=
    exists_minimal_spanning_finset (K := K) (Set.range c) (⇑b)
      (Finset.univ : Finset ι).card Finset.univ le_rfl hPuniv
  have hrange : Set.range (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι)))
      = Set.range c ∪ (⇑b) '' (↑J : Set ι) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      cases x with
      | inl i => exact Set.mem_union_left _ ⟨i, rfl⟩
      | inr j => exact Set.mem_union_right _ ⟨(j : ι), Finset.mem_coe.mpr j.2, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨j, Finset.mem_coe.mp hj⟩, rfl⟩
  have hli : LinearIndependent K (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι))) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : (∑ i : Fin h, g (Sum.inl i) • c i)
        + (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι)) = 0 := by
      rw [Fintype.sum_sum_type] at hg
      exact hg
    have hz : ∀ j : {j : ι // j ∈ J}, g (Sum.inr j) = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j0, hj0⟩ := hcon
      have hsplit : (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι))
          = g (Sum.inr j0) • b (j0 : ι)
            + ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι) :=
        (Finset.add_sum_erase Finset.univ
          (fun j : {j : ι // j ∈ J} => g (Sum.inr j) • b (j : ι)) (Finset.mem_univ j0)).symm
      rw [hsplit] at hg'
      have hA : (∑ i : Fin h, g (Sum.inl i) • c i)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩)
      have hB : (∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι))
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
        have hne : (j : ι) ≠ (j0 : ι) := by
          intro hh
          exact (Finset.ne_of_mem_erase hj) (Subtype.ext hh)
        exact Submodule.subset_span (Set.mem_union_right _
          ⟨(j : ι), Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, j.2⟩), rfl⟩)
      have hxmem : g (Sum.inr j0) • b (j0 : ι)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        have hid : g (Sum.inr j0) • b (j0 : ι)
            = ((∑ i : Fin h, g (Sum.inl i) • c i)
                + (g (Sum.inr j0) • b (j0 : ι)
                  + ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι)))
              - (∑ i : Fin h, g (Sum.inl i) • c i)
              - ∑ j ∈ Finset.univ.erase j0, g (Sum.inr j) • b (j : ι) := by
          abel
        rw [hid, hg']
        exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.zero_mem _) hA) hB
      have hbj0 : b (j0 : ι)
          ∈ Submodule.span K (Set.range c ∪ (⇑b) '' (↑(J.erase (j0 : ι)) : Set ι)) := by
        have hsm := Submodule.smul_mem _ (g (Sum.inr j0))⁻¹ hxmem
        rwa [smul_smul, inv_mul_cancel₀ hj0, one_smul] at hsm
      exact hJmin (j0 : ι) j0.2 (span_union_image_erase_eq_top hJtop hbj0)
    intro x
    cases x with
    | inl i =>
        have hzero : (∑ j : {j : ι // j ∈ J}, g (Sum.inr j) • b (j : ι)) = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [hz j, zero_smul]
        rw [hzero, add_zero] at hg'
        exact Fintype.linearIndependent_iff.mp hc (fun i => g (Sum.inl i)) hg' i
    | inr j => exact hz j
  have hsp : (⊤ : Submodule K V)
      ≤ Submodule.span K (Set.range (Sum.elim c (fun j : {j : ι // j ∈ J} => b (j : ι)))) := by
    rw [hrange]
    exact le_of_eq hJtop.symm
  refine ⟨J, Module.Basis.mk hli hsp, fun i => ?_, fun j => ?_⟩
  · exact Module.Basis.mk_apply hli hsp (Sum.inl i)
  · exact Module.Basis.mk_apply hli hsp (Sum.inr j)

end

section

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S'] [Algebra S S']
  [IsScalarTower (MvPolynomial ι k) S S']

theorem algebraMap_coord (i : ι) :
    algebraMap S S' (coord k ι S i) = coord k ι S' i := by
  rw [coord_def, coord_def]
  exact (IsScalarTower.algebraMap_apply (MvPolynomial ι k) S S' (MvPolynomial.X i)).symm

end

section

variable (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
  (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
  [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
  [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
  [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
  [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']

private theorem repr_map_basisKaehler
    (k : Type*) [CommRing k] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (S : Type*) [CommRing S] (S' : Type*) [CommRing S']
    [Algebra k S] [Algebra k S'] [Algebra (MvPolynomial ι k) S] [Algebra (MvPolynomial ι k) S']
    [Algebra S S'] [IsScalarTower k (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S']
    [IsScalarTower k S S'] [IsScalarTower (MvPolynomial ι k) S S']
    [Algebra.FormallyEtale (MvPolynomial ι k) S] [Algebra.FormallyEtale (MvPolynomial ι k) S']
    (ω : KaehlerDifferential k S) (i : ι) :
    (basisKaehler k ι S').repr (KaehlerDifferential.map k k S S' ω) i
      = algebraMap S S' ((basisKaehler k ι S).repr ω i) := by
  have hb : ∀ j : ι, KaehlerDifferential.map k k S S' (basisKaehler k ι S j)
      = basisKaehler k ι S' j := by
    intro j
    simp only [basisKaehler_apply, KaehlerDifferential.map_D,
      algebraMap_coord]
  have hω : ω = ∑ j : ι, (basisKaehler k ι S).repr ω j • basisKaehler k ι S j :=
    ((basisKaehler k ι S).sum_repr ω).symm
  have key : KaehlerDifferential.map k k S S' ω
      = ∑ j : ι, algebraMap S S' ((basisKaehler k ι S).repr ω j) • basisKaehler k ι S' j := by
    conv_lhs => rw [hω]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [map_smul, hb j]
    exact algebra_compatible_smul S' ((basisKaehler k ι S).repr ω j) (basisKaehler k ι S' j)
  rw [key]
  simp only [Module.Basis.repr_sum_self]

theorem algebraMap_det_basisKaehler (v : ι → S) :
    algebraMap S S' ((basisKaehler k ι S).det fun i : ι => KaehlerDifferential.D k S (v i)) =
      (basisKaehler k ι S').det
        fun i : ι => KaehlerDifferential.D k S' (algebraMap S S' (v i)) := by
  have hmat : (algebraMap S S').mapMatrix
        ((basisKaehler k ι S).toMatrix fun i : ι => KaehlerDifferential.D k S (v i))
      = (basisKaehler k ι S').toMatrix
        fun i : ι => KaehlerDifferential.D k S' (algebraMap S S' (v i)) := by
    ext i j
    have h0 : KaehlerDifferential.D k S' (algebraMap S S' (v j))
        = KaehlerDifferential.map k k S S' (KaehlerDifferential.D k S (v j)) := by
      simp only [KaehlerDifferential.map_D]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, h0]
    exact (repr_map_basisKaehler k ι S S' (KaehlerDifferential.D k S (v j)) i).symm
  rw [Module.Basis.det_apply, Module.Basis.det_apply, RingHom.map_det, hmat]

end

section

theorem formallyEtale_of_isUnit_det_of_eq_coord (k : Type*) [CommRing k] (ι : Type*) [Fintype ι]
    [DecidableEq ι] (T : Type*) [CommRing T] [Algebra k T] [Algebra (MvPolynomial ι k) T]
    [IsScalarTower k (MvPolynomial ι k) T] [Algebra.FormallySmooth k T]
    (e : Module.Basis ι T (KaehlerDifferential k T)) (w : ι → T)
    (hw : ∀ i : ι, w i = JacobianCriterion.coord k ι T i)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T (w i))) :
    Algebra.FormallyEtale (MvPolynomial ι k) T := by
  have hfun : (fun i : ι => KaehlerDifferential.D k T (JacobianCriterion.coord k ι T i)) =
      fun i : ι => KaehlerDifferential.D k T (w i) := by
    funext i
    rw [hw i]
  have h : IsUnit (e.det fun i : ι =>
      KaehlerDifferential.D k T (JacobianCriterion.coord k ι T i)) := by
    rw [hfun]
    exact hdet
  exact JacobianCriterion.formallyEtale_of_isUnit_det k ι T e h

theorem formallyEtale_aeval_of_isUnit_det {k : Type*} [CommRing k] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {T : Type*} [CommRing T] [Algebra k T] [Algebra.FormallySmooth k T]
    (e : Module.Basis ι T (KaehlerDifferential k T)) (w : ι → T)
    (hdet : IsUnit (e.det fun i : ι => KaehlerDifferential.D k T (w i))) :
    letI : Algebra (MvPolynomial ι k) T :=
      (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
    Algebra.FormallyEtale (MvPolynomial ι k) T := by
  let instAeval : Algebra (MvPolynomial ι k) T :=
    (MvPolynomial.aeval w : MvPolynomial ι k →ₐ[k] T).toRingHom.toAlgebra
  have hmap : ∀ p : MvPolynomial ι k,
      algebraMap (MvPolynomial ι k) T p = MvPolynomial.aeval w p := fun _ => rfl
  have instTower : IsScalarTower k (MvPolynomial ι k) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [hmap, MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  show Algebra.FormallyEtale (MvPolynomial ι k) T
  refine formallyEtale_of_isUnit_det_of_eq_coord k ι T e w (fun i => ?_) hdet
  show w i = algebraMap (MvPolynomial ι k) T (MvPolynomial.X i)
  rw [hmap, MvPolynomial.aeval_X]

end

section

theorem span_range_eq_span_range_of_eq_mul_isUnit {A : Type*} [CommRing A] {n : ℕ}
    (y z c : Fin n → A) (hc : ∀ i, IsUnit (c i)) (hz : ∀ i, z i = y i * c i) :
    Ideal.span (Set.range z) = Ideal.span (Set.range y) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro w ⟨i, rfl⟩
    rw [SetLike.mem_coe, hz i]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro w ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := hc i
    have hy : y i = z i * (↑v⁻¹ : A) := by
      rw [hz i, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [SetLike.mem_coe, hy]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_generators_maximalIdeal_of_linearIndependent_D (k : Type*) [CommRing k] (S : Type*) [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] (A : Type*) [CommRing A] [Algebra S A] [Algebra k A]
    [IsLocalization q.primeCompl A] [IsLocalRing A] (h : ℕ) (y : Fin h → A)
    (hspan : Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A)
    (hindep : LinearIndependent (IsLocalRing.ResidueField A)
      fun i : Fin h =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) :
    ∃ s : Fin h → S,
      (∀ i : Fin h, s i ∈ q) ∧
      Ideal.span (Set.range fun i : Fin h => algebraMap S A (s i)) =
        IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
            KaehlerDifferential.D k A (algebraMap S A (s i)) := by
  classical
  choose p hp using fun i : Fin h =>
    IsLocalization.surj (M := q.primeCompl) (S := A) (y i)
  obtain ⟨s, c, hcu, hmul⟩ : ∃ (s : Fin h → S) (c : Fin h → A),
      (∀ i, IsUnit (c i)) ∧ ∀ i, algebraMap S A (s i) = y i * c i :=
    ⟨fun i => (p i).1, fun i => algebraMap S A ((p i).2 : S),
      fun i => IsLocalization.map_units (M := q.primeCompl) (S := A) ((p i).2),
      fun i => (hp i).symm⟩
  have hymem : ∀ i : Fin h, y i ∈ IsLocalRing.maximalIdeal A := by
    intro i
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · intro i
    by_contra hni
    have hunit : IsUnit (algebraMap S A (s i)) :=
      IsLocalization.map_units (M := q.primeCompl) (S := A) ⟨s i, hni⟩
    have hmem : algebraMap S A (s i) ∈ IsLocalRing.maximalIdeal A := by
      rw [hmul i]
      exact Ideal.mul_mem_right _ _ (hymem i)
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit
  · refine Eq.trans ?_ hspan
    exact span_range_eq_span_range_of_eq_mul_isUnit y
      (fun i : Fin h => algebraMap S A (s i)) c hcu hmul
  · have hne : ∀ i : Fin h, IsLocalRing.residue A (c i) ≠ 0 := fun i =>
      ((hcu i).map (IsLocalRing.residue A)).ne_zero
    have hfun : (fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
        KaehlerDifferential.D k A (algebraMap S A (s i))) =
        fun i : Fin h => IsLocalRing.residue A (c i) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      rw [hmul i]
      exact KaehlerDifferential.residue_tmul_D_mul_of_mem_maximalIdeal k A (y i) (c i) (hymem i)
    have hsmul : ((fun i : Fin h => Units.mk0 (IsLocalRing.residue A (c i)) (hne i)) •
        fun i : Fin h => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A]
          KaehlerDifferential.D k A (y i)) =
        fun i : Fin h => IsLocalRing.residue A (c i) •
          ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (y i)) := by
      funext i
      simp [Units.smul_def]
    have key := hindep.units_smul
      (fun i : Fin h => Units.mk0 (IsLocalRing.residue A (c i)) (hne i))
    rw [hfun, ← hsmul]
    exact key

end

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
