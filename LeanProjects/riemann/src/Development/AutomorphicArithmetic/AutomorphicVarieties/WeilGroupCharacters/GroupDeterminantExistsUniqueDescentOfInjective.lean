import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCoefMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

open TensorProduct UpperTheory.V.CA in
private theorem exists_poly {n : ℕ} {A' A G : Type} [CommRing A'] [CommRing A] [Group G] (f : A' →+* A)
    (D : GDet n A G) (h : ∀ i g, D.lam i (MonoidAlgebra.single g 1) ∈ f.range) (S : Finset G) :
    ∃ P : MvPolynomial G A', ∀ (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G),
      x.coeff.support ⊆ S → D.D B x = MvPolynomial.eval₂ ((algebraMap A B).comp f) x.coeff P := by
  classical
  let z : S → MonoidAlgebra A G := fun g => MonoidAlgebra.single g 1
  have h1 : ∀ α, MvPolynomial.coeff α (D.toDet.poly z) ∈ f.range := by
    refine d_coef_mem D.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) f.range ?_ z (fun a => ⟨a, rfl⟩)
    rintro x ⟨g, rfl⟩ i - -
    rw [(d_toDet D _).2.1]
    exact h i g
  obtain ⟨Q, hQ⟩ : D.toDet.poly z ∈ Set.range (MvPolynomial.map f) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    obtain ⟨α, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
    exact h1 α
  refine ⟨MvPolynomial.rename Subtype.val Q, fun B _ _ x hx => ?_⟩
  have h2 := (d_poly D.toDet z).2 B (fun g => x.coeff g)
  rw [MvPolynomial.eval₂_rename, ← MvPolynomial.eval₂_map, hQ]
  refine Eq.trans ?_ h2
  change _ = D.D B (ofT A G B _)
  congr 1
  rw [map_sum]
  simp only [z, ofT_tmul, MonoidAlgebra.mapRingHom_single, map_one, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [Finset.sum_coe_sort S (fun g => MonoidAlgebra.single g (x.coeff g))]
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  exact Finsupp.sum_of_support_subset _ hx _ (by simp)

private theorem exists_lift {R B G : Type} [CommRing R] [CommRing B] [Group G] (π : R →+* B)
    (hπ : Function.Surjective π) (x : MonoidAlgebra B G) :
    ∃ y : MonoidAlgebra R G, MonoidAlgebra.mapRingHom G π y = x ∧ y.coeff.support ⊆ x.coeff.support := by
  classical
  choose s hs using hπ
  refine ⟨MonoidAlgebra.ofCoeff (x.coeff.mapRange (fun b => if b = 0 then 0 else s b) (by simp)), ?_, ?_⟩
  · ext g
    by_cases hg : x.coeff g = 0 <;> simp [hg, hs]
  · exact Finsupp.support_mapRange (hf := by simp)

private theorem supp_map {R B G : Type} [CommRing R] [CommRing B] [Group G] (π : R →+* B) (y : MonoidAlgebra R G) :
    (MonoidAlgebra.mapRingHom G π y).coeff.support ⊆ y.coeff.support := by
  intro g hg
  rw [Finsupp.mem_support_iff] at hg ⊢
  intro h0
  exact hg (by rw [MonoidAlgebra.coeff_mapRingHom, h0, map_zero])

private theorem aeval_nat {A' B B' G : Type} [CommRing A'] [CommRing B] [CommRing B'] [Algebra A' B] [Algebra A' B']
    [Group G] (φ : B →ₐ[A'] B') (x : MonoidAlgebra B G) (Q : MvPolynomial G A') :
    MvPolynomial.aeval (MonoidAlgebra.mapRingHom G (φ : B →+* B') x).coeff Q = φ (MvPolynomial.aeval x.coeff Q) := by
  rw [MvPolynomial.comp_aeval_apply]
  congr 2

theorem UpperTheory.V.W.groupDeterminant_existsUnique_descent_of_injective :
    ∀ (n : ℕ) (A' A G : Type) [CommRing A'] [CommRing A] [Group G] (f : A' →+* A), Function.Injective f → ∀ D : GDet n A G, (∀ i g, D.lam i (MonoidAlgebra.single g 1) ∈ f.range) → ∃! D' : GDet n A' G, D'.map f = D := by
  intro n A' A G _ _ _ f hf D h
  classical
  choose P hP using exists_poly f D h
  have hinj : ∀ σ : Type, Function.Injective (MvPolynomial.map (σ := σ) f) := fun σ => MvPolynomial.map_injective f hf
  have hpoly : ∀ (σ : Type) (S : Finset G) (y : MonoidAlgebra (MvPolynomial σ A') G), y.coeff.support ⊆ S →
      MvPolynomial.map f (MvPolynomial.aeval y.coeff (P S)) =
        D.D (MvPolynomial σ A) (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) y) := by
    intro σ S y hy
    rw [hP S _ _ ((supp_map _ y).trans hy), MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left]
    congr 1
    ext a : 1
    simp
  have hsurj : ∀ (B : Type) [CommRing B] [Algebra A' B],
      Function.Surjective ((MvPolynomial.aeval (R := A') (id : B → B) : MvPolynomial B A' →ₐ[A'] B) :
        MvPolynomial B A' →+* B) := fun B _ _ b => ⟨MvPolynomial.X b, by simp⟩
  let F : ∀ (B : Type) [CommRing B] [Algebra A' B], MonoidAlgebra B G → B :=
    fun B _ _ x => MvPolynomial.aeval x.coeff (P x.coeff.support)
  have hS : ∀ (B : Type) [CommRing B] [Algebra A' B] (x : MonoidAlgebra B G) (S : Finset G), x.coeff.support ⊆ S →
      F B x = MvPolynomial.aeval x.coeff (P S) := by
    intro B _ _ x S hx
    obtain ⟨y, hy, hs⟩ := exists_lift _ (hsurj B) x
    have e : MvPolynomial.aeval y.coeff (P x.coeff.support) = MvPolynomial.aeval y.coeff (P S) :=
      hinj B (by rw [hpoly B _ y hs, hpoly B _ y (hs.trans hx)])
    have e1 := aeval_nat (MvPolynomial.aeval (R := A') (id : B → B)) y (P S)
    have e2 := aeval_nat (MvPolynomial.aeval (R := A') (id : B → B)) y (P x.coeff.support)
    rw [hy] at e1 e2
    rw [e1, ← e, ← e2]
  have hnat : ∀ (B B' : Type) [CommRing B] [Algebra A' B] [CommRing B'] [Algebra A' B'] (φ : B →ₐ[A'] B')
      (x : MonoidAlgebra B G), F B' (MonoidAlgebra.mapRingHom G (φ : B →+* B') x) = φ (F B x) := by
    intro B B' _ _ _ _ φ x
    rw [hS B' _ _ (supp_map _ x), aeval_nat]
  have hF : ∀ (σ : Type) (y : MonoidAlgebra (MvPolynomial σ A') G), MvPolynomial.map f (F _ y) =
      D.D (MvPolynomial σ A) (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) y) :=
    fun σ y => hpoly σ _ y subset_rfl
  have hsmul : ∀ {R B : Type} [CommRing R] [CommRing B] (π : R →+* B) (r : R) (y : MonoidAlgebra R G),
      MonoidAlgebra.mapRingHom G π (r • y) = π r • MonoidAlgebra.mapRingHom G π y := by
    intro R B _ _ π r y
    ext g
    simp
  let D' : GDet n A' G :=
    { D := fun B _ _ =>
        { toFun := F B
          map_one' := by
            have e : F (MvPolynomial B A') 1 = 1 := hinj B (by rw [hF, map_one, map_one, map_one])
            have e1 := hnat _ B (MvPolynomial.aeval (R := A') (id : B → B)) 1
            rwa [e, map_one, map_one] at e1
          map_mul' := fun x₁ x₂ => by
            obtain ⟨y₁, rfl, -⟩ := exists_lift _ (hsurj B) x₁
            obtain ⟨y₂, rfl, -⟩ := exists_lift _ (hsurj B) x₂
            have e : F (MvPolynomial B A') (y₁ * y₂) = F _ y₁ * F _ y₂ :=
              hinj B (by rw [map_mul, hF, hF, hF, map_mul, map_mul])
            rw [← map_mul, hnat, hnat, hnat, e, map_mul] }
      nat := hnat
      homog := fun B _ _ b x => by
        obtain ⟨y, rfl, -⟩ := exists_lift _ (hsurj B) x
        obtain ⟨c, rfl⟩ := hsurj B b
        have e : F (MvPolynomial B A') (c • y) = c ^ n * F _ y :=
          hinj B (by rw [map_mul, hF, hF, hsmul, D.homog, map_pow])
        change F B _ = _ * F B _
        rw [← hsmul, hnat, hnat, e, map_mul, map_pow]
        rfl }
  have hD' : D'.map f = D := GDet.ext fun B _ _ x => (hP _ B x subset_rfl).symm
  refine ⟨D', hD', fun D'' hD'' => UpperTheory.V.CA.d_gext _ _ fun g i _ _ => hf ?_⟩
  rw [← ((UpperTheory.V.CA.d_gmap D'').2.2.1 f _).2 i, ← ((UpperTheory.V.CA.d_gmap D').2.2.1 f _).2 i, hD', hD'']
