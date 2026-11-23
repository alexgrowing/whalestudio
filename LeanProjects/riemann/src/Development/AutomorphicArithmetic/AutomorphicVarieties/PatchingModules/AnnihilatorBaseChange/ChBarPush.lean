import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem gDet_chi_map_C_mapRingHom_gen {n : ℕ} {B B' G : Type} [CommRing B] [CommRing B'] [Group G] (g : B →+* B') (D : GDet n B G) (m : ℕ) (y : Fin m → MonoidAlgebra B G) : ((D.map g).map MvPolynomial.C).chi (MonoidAlgebra.mapRingHom G (MvPolynomial.map g) (GDet.gen y)) = Polynomial.map (MvPolynomial.map g) ((D.map MvPolynomial.C).chi (GDet.gen y)) := by
  letI i0 : Algebra B (Polynomial (MvPolynomial (Fin m) B)) := RingHom.toAlgebra ((algebraMap (MvPolynomial (Fin m) B) (Polynomial (MvPolynomial (Fin m) B))).comp MvPolynomial.C)
  letI i1 : Algebra B (Polynomial (MvPolynomial (Fin m) B')) := RingHom.toAlgebra (((algebraMap (MvPolynomial (Fin m) B') (Polynomial (MvPolynomial (Fin m) B'))).comp MvPolynomial.C).comp g)
  let φ : Polynomial (MvPolynomial (Fin m) B) →ₐ[B] Polynomial (MvPolynomial (Fin m) B') :=
    { Polynomial.mapRingHom (MvPolynomial.map g) with
      commutes' := fun b => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat _ _ φ (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y))
  have hx : MonoidAlgebra.mapRingHom G (φ : Polynomial (MvPolynomial (Fin m) B) →+* Polynomial (MvPolynomial (Fin m) B')) (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y)) = MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapRingHom G (MvPolynomial.map g) (GDet.gen y)) := by
    ext h
    simp [φ, MonoidAlgebra.mapRingHom, MonoidAlgebra.single_apply, Finsupp.single_apply]
    rcases eq_or_ne h 1 with rfl | hh
    · simp [Polynomial.coeff_X]
    · simp [Finsupp.single_eq_of_ne hh, Finsupp.single_eq_of_ne hh.symm]
  rw [hx] at key
  exact key

private theorem gDet_mapRingHom_mem_ch_map_of_mem_ch {n : ℕ} {B B' G : Type} [CommRing B] [CommRing B'] [Group G] (g : B →+* B') (D : GDet n B G) (z : MonoidAlgebra B G) (hz : z ∈ D.CH) : MonoidAlgebra.mapRingHom G g z ∈ (D.map g).CH := by
  obtain ⟨m, y, β, hz⟩ := hz
  refine ⟨m, fun j => MonoidAlgebra.mapRingHom G g (y j), β, fun h => ?_⟩
  have hgen : GDet.gen (fun j => MonoidAlgebra.mapRingHom G g (y j)) = MonoidAlgebra.mapRingHom G (MvPolynomial.map g) (GDet.gen y) := by
    ext h
    simp [GDet.gen, Finsupp.finset_sum_apply, MonoidAlgebra.mapRingHom]
  have hcomm : (MonoidAlgebra.mapRingHom G (MvPolynomial.map g)).comp (algebraMap (MvPolynomial (Fin m) B) (MonoidAlgebra (MvPolynomial (Fin m) B) G)) = (algebraMap (MvPolynomial (Fin m) B') (MonoidAlgebra (MvPolynomial (Fin m) B') G)).comp (MvPolynomial.map g) := by
    refine RingHom.ext fun q => ?_
    simp [MonoidAlgebra.mapRingHom, MonoidAlgebra.coe_algebraMap, Finsupp.mapRange_single]
  rw [hgen, gDet_chi_map_C_mapRingHom_gen, Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomm, ← Polynomial.hom_eval₂]
  simp [MonoidAlgebra.mapRingHom, MvPolynomial.coeff_map, hz h, Polynomial.aeval_def]

private theorem monoidAlgebra_map_mapDomain_comm {R S G G' : Type} [Semiring R] [Semiring S] (F : R →+ S) (p : G → G') (x : MonoidAlgebra R G) : MonoidAlgebra.map F (MonoidAlgebra.mapDomain p x) = MonoidAlgebra.mapDomain p (MonoidAlgebra.map F x) := by
  ext h
  simp only [MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_mapDomain]
  rw [Finsupp.mapDomain_mapRange _ _ _ _ (map_add F)]

private theorem gDet_mapDomainRingHom_mem_ch_of_mem_ch_comap {n : ℕ} {B' G G' : Type} [CommRing B'] [Group G] [Group G'] (p : G →* G') (D' : GDet n B' G') (z : MonoidAlgebra B' G) (hz : z ∈ (D'.comap p).CH) : MonoidAlgebra.mapDomainRingHom B' p z ∈ D'.CH := by
  obtain ⟨m, y, β, hz⟩ := hz
  refine ⟨m, fun j => MonoidAlgebra.mapDomainRingHom B' p (y j), β, fun h => ?_⟩
  have hgen : GDet.gen (fun j => MonoidAlgebra.mapDomainRingHom B' p (y j)) = MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p (GDet.gen y) := by
    simp [GDet.gen, map_sum, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom, Finsupp.mapDomain_smul, monoidAlgebra_map_mapDomain_comm]
  have hchi : ((D'.comap p).map MvPolynomial.C).chi (GDet.gen y) = (D'.map MvPolynomial.C).chi (MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p (GDet.gen y)) := by
    have e : MonoidAlgebra.mapDomainRingHom (Polynomial (MvPolynomial (Fin m) B')) p (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y)) = MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G' Polynomial.C (MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p (GDet.gen y)) := by
      rw [map_sub]
      simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom, monoidAlgebra_map_mapDomain_comm]
    calc ((D'.comap p).map MvPolynomial.C).chi (GDet.gen y) = (D'.map MvPolynomial.C).D (Polynomial (MvPolynomial (Fin m) B')) (MonoidAlgebra.mapDomainRingHom (Polynomial (MvPolynomial (Fin m) B')) p (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (GDet.gen y))) := rfl
      _ = _ := by rw [e]; rfl
  have hcomm : (MonoidAlgebra.mapDomainRingHom (MvPolynomial (Fin m) B') p).comp (algebraMap (MvPolynomial (Fin m) B') (MonoidAlgebra (MvPolynomial (Fin m) B') G)) = algebraMap (MvPolynomial (Fin m) B') (MonoidAlgebra (MvPolynomial (Fin m) B') G') := by
    refine RingHom.ext fun q => ?_
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coe_algebraMap]
  have hzW : z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) ((Polynomial.aeval (GDet.gen y)) (((D'.comap p).map MvPolynomial.C).chi (GDet.gen y))) := by
    ext g
    simp [hz g]
  rw [hgen, ← hchi, Polynomial.aeval_def, ← hcomm, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hzW, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply, ← monoidAlgebra_map_mapDomain_comm]
  simp

theorem UpperTheory.V.Pa.Core.chBarPush :
    ∀ (n : ℕ) (B B' G G' : Type) [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B'] [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (g : B →+* B') [IsLocalHom g] (p : G →* G') (D : GDet n B G) (D' : GDet n B' G') (Z : Set (MonoidAlgebra B G)), Continuous p → D.map g = D'.comap p → ∀ z ∈ D.chBar Z, MonoidAlgebra.mapDomainRingHom B' p (MonoidAlgebra.mapRingHom G g z) ∈ D'.chBar ((fun y => MonoidAlgebra.mapDomainRingHom B' p (MonoidAlgebra.mapRingHom G g y)) '' Z) := by
  intro n B B' G G' _ _ _ _ _ _ _ _ g _ p D D' Z hp hD z hz
  unfold GDet.chBar closureIdeal at hz ⊢
  simp only [TwoSidedIdeal.mem_iInf] at hz ⊢
  intro N H'
  let H : OpenNormalSubgroup G := ⟨H'.toOpenSubgroup.comap p hp, H'.isNormal'.comap p⟩
  have hzN := hz N H
  let φ : MonoidAlgebra B G →+* MonoidAlgebra B' G' := (MonoidAlgebra.mapDomainRingHom B' p).comp (MonoidAlgebra.mapRingHom G g)
  have hm : Ideal.map g (maximalIdeal B) ≤ maximalIdeal B' := Ideal.map_le_iff_le_comap.2 (fun x hx => (mem_maximalIdeal _).2 ((map_mem_nonunits_iff g x).2 ((mem_maximalIdeal _).1 hx)))
  refine (TwoSidedIdeal.mem_comap φ).1 ((TwoSidedIdeal.span_le.2 ?_) hzN)
  rintro x (((hx | hx) | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩) <;> rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap] <;> apply TwoSidedIdeal.subset_span
  · refine Or.inl (Or.inl (Or.inl ?_))
    apply gDet_mapDomainRingHom_mem_ch_of_mem_ch_comap
    rw [← hD]
    exact gDet_mapRingHom_mem_ch_map_of_mem_ch g D x hx
  · exact Or.inl (Or.inl (Or.inr ⟨x, hx, rfl⟩))
  · refine Or.inl (Or.inr ⟨g a, Ideal.pow_right_mono hm N (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem g ha), ?_⟩)
    simp [φ, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
  · refine Or.inr ⟨p h, hh, ?_⟩
    show φ (MonoidAlgebra.single h 1 - 1) = _
    rw [map_sub, map_one]
    simp [φ, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
