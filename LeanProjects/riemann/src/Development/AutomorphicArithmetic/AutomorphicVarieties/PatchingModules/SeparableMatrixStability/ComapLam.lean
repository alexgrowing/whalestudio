import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem md_comm {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+ B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.map φ y) =
      MonoidAlgebra.map φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomainRingHom_apply]
  apply MonoidAlgebra.coeff_injective
  simp only [MonoidAlgebra.coeff_map, MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.mapDomain_mapRange _ _ _ _ (map_add φ)

private theorem md_comm' {A B G G' : Type} [CommRing A] [CommRing B] [Group G] [Group G'] (f : G →* G')
    (φ : A →+* B) (y : MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom B f (MonoidAlgebra.mapRingHom G φ y) =
      MonoidAlgebra.mapRingHom G' φ (MonoidAlgebra.mapDomainRingHom A f y) := by
  exact md_comm f φ.toAddMonoidHom y

private theorem md_surj (A : Type) {G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G')
    (hf : Function.Surjective f) : Function.Surjective (MonoidAlgebra.mapDomainRingHom A f) := by
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hf y.coeff
  refine ⟨MonoidAlgebra.ofCoeff x, ?_⟩
  apply MonoidAlgebra.coeff_injective
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_ofCoeff, hx]

private theorem comap_chi {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    (y : MonoidAlgebra A G) : (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y) := by
  show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom _ f
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C y)) = _
  rw [map_sub, md_comm', MonoidAlgebra.mapDomainRingHom_apply (Polynomial A) f (MonoidAlgebra.single 1 Polynomial.X),
    MonoidAlgebra.mapDomain_single, map_one]
  rfl

private theorem md_gen {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) :
    MonoidAlgebra.mapDomainRingHom _ f (GDet.gen y) = GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j) := by
  unfold GDet.gen
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_smul,
    ← MonoidAlgebra.mapDomainRingHom_apply, md_comm']

private theorem mem_CH {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (z : MonoidAlgebra A G) :
    z ∈ D.CH ↔ ∃ (m : ℕ) (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ),
      z = MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β) (Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))) := by
  simp only [GDet.CH, Set.mem_setOf_eq]
  refine exists_congr fun m => exists_congr fun y => exists_congr fun β => ?_
  constructor
  · intro h
    apply MonoidAlgebra.coeff_injective
    ext g
    rw [h g, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl
  · intro h g
    rw [h, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply]
    rfl

private theorem md_CH {n : ℕ} {A G G' : Type} [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G')
    {m : ℕ} (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) :
    MonoidAlgebra.mapDomainRingHom A f (MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen y)
        (((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y)))) =
    MonoidAlgebra.map (MvPolynomial.coeffAddMonoidHom β)
      (Polynomial.aeval (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j))
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
          (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)))) := by
  rw [md_comm]
  congr 1
  have hc : ((D.comap f).map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y) =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi
        (GDet.gen fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) := by
    rw [← md_gen]
    exact comap_chi f (D.map MvPolynomial.C) (GDet.gen y)
  rw [hc, ← md_gen]
  exact (Polynomial.aeval_algHom_apply
    (MonoidAlgebra.mapDomainAlgHom (R := MvPolynomial (Fin m) A) (A := MvPolynomial (Fin m) A) f) _ _).symm

theorem UpperTheory.V.Pa.comap_lam :
    ∀ (n : ℕ) (A G G' : Type) [CommRing A] [Group G] [Group G'] (f : G →* G') (D : GDet n A G'), (∀ y, (D.comap f).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ i y, (D.comap f).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ y, (D.comap f).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A f y)) ∧ (∀ (B : Type) [CommRing B] (φ : A →+* B), (D.comap f).map φ = (D.map φ).comap f) ∧ (∀ ρ : G' →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).comap f = GDet.ofRep (ρ.comp f)) ∧ (Function.Surjective f → (∀ D' : GDet n A G', D'.comap f = D.comap f → D' = D) ∧ MonoidAlgebra.mapDomainRingHom A f '' (D.comap f).CH = D.CH) := by
  intro n A G G' _ _ _ f D
  refine ⟨comap_chi f D, ?_, ?_, ?_, ?_, ?_⟩
  · intro i y
    simp only [GDet.lam, comap_chi]
  · intro y
    simp only [GDet.tr, GDet.lam, comap_chi]
  · intro B _ φ
    apply GDet.ext
    intro C _ _ x
    rfl
  · intro ρ
    apply GDet.ext
    intro B _ _ x
    have key : ((GDet.repAlg ρ B).comp (MonoidAlgebra.mapDomainAlgHom (R := B) (A := B) f)) =
        GDet.repAlg (ρ.comp f) B := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, MonoidAlgebra.mapDomainAlgHom]
      · exact Subsingleton.elim _ _
    show Matrix.det (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B f x)) =
      Matrix.det (GDet.repAlg (ρ.comp f) B x)
    rw [← key]
    rfl
  · intro hf
    constructor
    · intro D' h
      apply GDet.ext
      intro B _ _ x
      obtain ⟨x', rfl⟩ := md_surj B f hf x
      exact congrArg (fun E : GDet n A G => E.D B x') h
    · ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨m, y, β, rfl⟩ := (mem_CH _ _).1 hw
        exact (mem_CH _ _).2 ⟨m, _, β, md_CH f D y β⟩
      · intro hz
        obtain ⟨m, y', β, rfl⟩ := (mem_CH _ _).1 hz
        choose y hy using fun j => md_surj A f hf (y' j)
        have hy' : (fun j => MonoidAlgebra.mapDomainRingHom A f (y j)) = y' := funext hy
        refine ⟨_, (mem_CH _ _).2 ⟨m, y, β, rfl⟩, ?_⟩
        rw [md_CH, hy']
