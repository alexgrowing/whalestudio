import Development.EtaleCohomology.EtaleSheaves.LineOneCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartAcycPf

theorem acyc_of_iso {q : ℕ} {E E' : Spc} (e : E ≅ E') (h : Acyc q E') : Acyc q E := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q E n i, z = pull _ e.hom (tw q i) n (pull _ e.inv (tw q i) n z) := by
    intro z
    rw [← pull_comp, e.hom_inv_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull _ e.inv (tw q i) n x) (pull _ e.inv (tw q i) n y)]

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h2 : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    rw [Polynomial.map_map]; ext n; simp
  rw [← h2]
  change Polynomial.eval (e.toRingHom a) _ = 0
  rw [Polynomial.eval_map_apply, ha, map_zero]

theorem fib_iso_quot {A : Type} [CommRing A] [IsLocalRing A] {U : Scheme.{0}} [IsAffine U]
    (f : U ⟶ Spec (CommRingCat.of A)) :
    ∃ (φ : A →+* Γ(U, ⊤)), Nonempty (fib f ≅ Spec (CommRingCat.of
      (Γ(U, ⊤) ⧸ (IsLocalRing.maximalIdeal A).map φ))) := by
  let e := U.isoSpec
  let φ := Spec.preimage (e.inv ≫ f)
  have hf : f = e.hom ≫ Spec.map φ := by
    rw [Spec.map_preimage]; simp
  letI : Algebra A Γ(U, ⊤) := φ.hom.toAlgebra
  refine ⟨φ.hom, ⟨?_⟩⟩
  refine (pullback.congrHom hf rfl) ≪≫
    (asIso (pullback.map (e.hom ≫ Spec.map φ) (cpt A) (Spec.map φ) (cpt A) e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))) ≪≫ ?_
  refine (pullbackSpecIso A Γ(U, ⊤) (IsLocalRing.ResidueField A)) ≪≫ ?_
  let i := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := A) Γ(U, ⊤)
    (IsLocalRing.maximalIdeal A)).toRingEquiv.toCommRingCatIso
  exact Scheme.Spec.mapIso i.op

theorem ChartAcyc_of (hQ : QuotAcyc) : ChartAcyc := by
  intro H q A _ _ Z U p ι hι hU hZ hq
  have : IsIntegral Z := hZ.1
  by_cases hne : Nonempty U
  · have : IsIntegral U := isIntegral_of_isOpenImmersion ι
    obtain ⟨φ, ⟨e⟩⟩ := fib_iso_quot (ι ≫ p)
    have hdom : IsDomain Γ(U, ⊤) := inferInstance
    have haff : IsAffineOpen (ι ''ᵁ (⊤ : U.Opens)) := (isAffineOpen_top U).image_of_isOpenImmersion ι
    have hnV : ((ι ''ᵁ (⊤ : U.Opens) : Z.Opens) : Set Z).Nonempty := by
      obtain ⟨x⟩ := hne
      exact ⟨ι x, x, trivial, rfl⟩
    have haic : AIC Γ(U, ⊤) :=
      aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ haff hnV)
    have hqB : IsUnit (q : Γ(U, ⊤)) := by
      simpa using hq.map φ
    exact acyc_of_iso (sch.mapIso e) (hQ H q Γ(U, ⊤) _ haic hqB)
  · rw [not_nonempty_iff] at hne
    obtain ⟨x⟩ : Nonempty Z := inferInstance
    obtain ⟨V, ⟨W, hW, rfl⟩, hxW, -⟩ := (Z.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hWne : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hdom : IsDomain Γ(Z, W) := inferInstance
    have haic : AIC Γ(Z, W) := hZ.2 W hW ⟨x, hxW⟩
    let ψ : CommRingCat.of A ⟶ Γ(Z, W) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
    have hqC : IsUnit (q : Γ(Z, W)) := by
      simpa using hq.map ψ.hom
    have h1 := hQ H q Γ(Z, W) ⊤ haic hqC
    have : IsEmpty (fib (ι ≫ p)) := ⟨fun y => hne.elim ((pullback.fst (ι ≫ p) (cpt A)) y)⟩
    have : Subsingleton (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have : IsEmpty (Spec (CommRingCat.of (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))))) :=
      ⟨fun y => (show PrimeSpectrum (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) from y).isPrime.ne_top (Subsingleton.elim _ _)⟩
    exact acyc_of_iso (sch.mapIso (isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty)) h1

end LateralTheory.E.ChartAcycPf
