import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsOpenNormalSubgroupKillsOfGroupDetLawIsCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DKillsPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem map_nat {n : ℕ} {A A' G B B' : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G)
    [CommRing B] [CommRing B'] [Algebra A B] [Algebra A' B'] (f : A →+* A') (φ : B →+* B')
    (hφ : ∀ a, φ (algebraMap A B a) = algebraMap A' B' (f a)) (x : MonoidAlgebra B G) :
    (D.map f).D B' (MonoidAlgebra.mapRingHom G φ x) = φ (D.D B x) := by
  letI : Algebra A B' := ((algebraMap A' B').comp f).toAlgebra
  exact D.nat B B' { φ with commutes' := hφ } x

private theorem mapR_comp {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G]
    (f : A →+* B) (g : B →+* C) (x : MonoidAlgebra A G) :
    MonoidAlgebra.mapRingHom G g (MonoidAlgebra.mapRingHom G f x) = MonoidAlgebra.mapRingHom G (g.comp f) x := by
  ext a; simp

private theorem kills_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (D : GDet n A G)
    (f : A →+* A') (z : MonoidAlgebra A G) (hz : D.Kills z) :
    (D.map f).Kills (MonoidAlgebra.mapRingHom G f z) := by
  intro B _ _ h
  letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
  rw [mapR_comp]
  exact hz B h

theorem UpperTheory.V.CA.d_closed :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (I : Ideal A) [IsHausdorff I A], D.IsCont I → ∀ Z : Set (MonoidAlgebra A G), (∀ z ∈ Z, D.Kills z) → ∀ y ∈ closureIdeal I Z, D.Kills y := by
  intro n A G _ _ D _ _ _ _ I _ hD Z hZ y hy
  have key : ∀ N : ℕ, (D.map (Ideal.Quotient.mk (I ^ N))).Kills
      (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk (I ^ N)) y) := by
    intro N
    obtain ⟨H, hH⟩ := exists_openNormalSubgroup_kills_of_groupDetLaw_isCont D I hD N
    have hiff : ∀ x, x ∈ (D.map (Ideal.Quotient.mk (I ^ N))).toDet.ker ↔
        (D.map (Ideal.Quotient.mk (I ^ N))).Kills x := fun x =>
      (d_ker _ x).1.trans (d_toDet _ x).2.2.2
    have hy' := (TwoSidedIdeal.mem_iInf _).1 ((TwoSidedIdeal.mem_iInf _).1 hy N) H
    have hle : TwoSidedIdeal.span
        (Z ∪ {z | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪ {z | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) ≤
        TwoSidedIdeal.comap (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk (I ^ N)))
          (D.map (Ideal.Quotient.mk (I ^ N))).toDet.ker := by
      rw [TwoSidedIdeal.span_le]
      rintro z ((hz | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
      · rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hiff]
        exact kills_map D _ z (hZ z hz)
      · rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, MonoidAlgebra.mapRingHom_single,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, MonoidAlgebra.single_zero]
        exact TwoSidedIdeal.zero_mem _
      · rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, hiff, map_sub, map_one, MonoidAlgebra.mapRingHom_single,
          map_one]
        exact hH h hh
    exact (hiff _).1 ((TwoSidedIdeal.mem_comap _).1 (hle hy'))
  have key2 : ∀ (k : ℕ) (h : MonoidAlgebra (MvPolynomial (Fin k) A) G),
      D.D (MvPolynomial (Fin k) A)
        (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial (Fin k) A)) y) = 1 := by
    intro k h
    rw [← sub_eq_zero]
    refine MvPolynomial.ext _ _ fun β => ?_
    rw [MvPolynomial.coeff_zero]
    refine IsHausdorff.haus (inferInstance : IsHausdorff I A) _ fun N => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq_zero_iff_mem, ← MvPolynomial.coeff_map,
      map_sub, map_one]
    have h1 := map_nat D (Ideal.Quotient.mk (I ^ N))
      (MvPolynomial.map (σ := Fin k) (Ideal.Quotient.mk (I ^ N))) (fun a => by simp)
      (1 + h * MonoidAlgebra.mapRingHom G (algebraMap A (MvPolynomial (Fin k) A)) y)
    have h2 := key N (MvPolynomial (Fin k) (A ⧸ I ^ N))
      (MonoidAlgebra.mapRingHom G (MvPolynomial.map (σ := Fin k) (Ideal.Quotient.mk (I ^ N))) h)
    have h3 : (MvPolynomial.map (σ := Fin k) (Ideal.Quotient.mk (I ^ N))).comp
        (algebraMap A (MvPolynomial (Fin k) A)) =
        (algebraMap (A ⧸ I ^ N) (MvPolynomial (Fin k) (A ⧸ I ^ N))).comp (Ideal.Quotient.mk (I ^ N)) :=
      RingHom.ext fun a => by simp
    rw [map_add, map_one, map_mul, mapR_comp, h3, ← mapR_comp, h2] at h1
    rw [← h1, sub_self, MvPolynomial.coeff_zero]
  refine (d_toDet D y).2.2.2.1 (d_kills_poly D.toDet y Set.univ Submodule.span_univ fun k h _ => ?_)
  change D.D _ (ofT A G _ _) = 1
  rw [map_add, map_one, map_mul, ofT_tmul, one_smul]
  exact key2 k _
