import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieChart

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

theorem algChart_of_isStandardSmooth {R : Type} [CommRing R] (B : Type) [CommRing B] [Algebra R B]
    (hB : (algebraMap R B).IsStandardSmooth) (ε' : B →ₐ[R] R) :
    ∃ (n : ℕ) (π : ∀ m : ℕ, B →ₐ[R] JetR R (Fin n) m),
      (∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m) ∧
      (∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε') ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
        ∀ φ : B →ₐ[R] A, aug.comp φ = ε' →
          ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ ψ.comp (π m) = φ := by
  obtain ⟨n, g, hgC, hg⟩ := hB.exists_etale_mvPolynomial
  letI : Algebra (MvPolynomial (Fin n) R) B := g.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) B := IsScalarTower.of_algebraMap_eq' hgC.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) B := hg
  have hπ : ∀ m : ℕ, ∃ π : B →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧
      ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j := fun m =>
    etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨n, π, ?_, ?_, ?_⟩
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro j
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · intro m
    refine etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
      exact hπaug m
    · ext s
      simp
    · intro j
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
      rfl
  · intro A _ _ aug m hJ φ' hφ'aug
    have hJn := nil_of_pow _ hJ
    have hmem : ∀ j : Fin n, φ' (sX (S := B) R j) -
        algebraMap R A (ε' (sX (S := B) R j)) ∈ RingHom.ker aug := by
      intro j
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ'aug, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun j : Fin n => φ' (sX (S := B) R j) - algebraMap R A (ε' (sX (S := B) R j))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun j => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem j
    have hψπ : ψ.comp (π m) = φ' := by
      refine etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · exact hφ'aug
      · intro j
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, hψπ⟩, ?_⟩
    rintro ψ₂ ⟨_, h4⟩
    apply jet_ext
    intro j
    rw [jetLift_zR]
    have := AlgHom.congr_fun h4 (sX R j)
    rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
    rw [← this, add_sub_cancel_left]

theorem univChart_of_chart {R : Type} [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (C : Chart G)
    (hC : (alg0 C).IsStandardSmooth) :
    ∃ (d : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x := by
  obtain ⟨n, π, htr, hze, huniv⟩ := algChart_of_isStandardSmooth Γ(G.left, C.U) hC (eps C)
  refine ⟨n, fun m => pt C (π m), fun m => ?_, fun m => ?_, ?_⟩
  · rw [spMap_pt, htr]
  · rw [spMap_pt, hze, pt_eps]
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    have hy' : spMap aug ≫ y = pt C ((Algebra.ofId R R).comp (eps C)) := by rw [pt_eps]; exact hy
    obtain ⟨φ, rfl⟩ := exists_pt C y (le_preimage_of_nil C aug (aug_surj aug) (elt_nil _ hJn) y _ hy')
    have hφ : aug.comp φ = eps C := by
      have := pt_injective C ((spMap_pt C aug φ).symm.trans hy')
      rw [this]
      ext b
      rfl
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := huniv A aug m hJ φ hφ
    refine ⟨ψ, ⟨hψ1, by rw [spMap_pt, hψ2]⟩, ?_⟩
    rintro ψ₂ ⟨h1, h2⟩
    rw [spMap_pt] at h2
    exact hψu ψ₂ ⟨h1, (pt_injective C h2).symm⟩

theorem univChart_baseChange_of_chart {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (C : Chart G) (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G)
    (hx : IsUnivChart G n x) :
    ∃ x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (algebraMap R R' ∘ c)).left ≫ pullback.fst G.hom (fB R R') =
          Spec.map (CommRingCat.ofHom (dualMapR (algebraMap R R'))) ≫ (tvec (x := x) c).left := by
  have hin : ∀ m, ∃ π : Γ(G.left, C.U) →ₐ[R] JetR R (Fin n) m, x m = pt C π := fun m =>
    exists_pt C (x m) (le_preimage_of_nil C (jetAug R (Fin n) m) (aug_surj _)
      (elt_nil _ (ker_jetAug_nil (Fin n) m)) (x m) ((Algebra.ofId R R).comp (eps C))
      ((spMap_jetAug_alt hx m).trans (pt_eps C R).symm))
  choose π hπ using hin
  have hoe : (Algebra.ofId R R).comp (eps C) = eps C := AlgHom.ext fun _ => rfl
  have hπa : ∀ m, (jetAug R (Fin n) m).comp (π m) = eps C := fun m => by
    rw [← hoe]
    apply pt_injective C
    rw [← spMap_pt, ← hπ, spMap_jetAug_alt hx, pt_eps]
  have hπtr : ∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hπ, ← hπ, hx.1 m])
  have hπ0 : ∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp (eps C) := fun m =>
    pt_injective C (by rw [← spMap_pt, ← hπ, hx.2.1 m, pt_eps])
  have huniv : ∀ m, IsUnivRing (eps C) m (π m) := by
    intro m A _ _ aug hJ h hh
    have hy : spMap aug ≫ pt C h = 1 := by rw [spMap_pt, hh, ← hoe, pt_eps]
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := hx.2.2 A aug m hJ (pt C h) hy
    refine ⟨ψ, ⟨h1, pt_injective C (by rw [← spMap_pt, ← hπ]; exact h2)⟩, fun ψ₂ hψ₂ => hu ψ₂ ⟨hψ₂.1, ?_⟩⟩
    rw [hπ, spMap_pt, ← hψ₂.2]
  refine ⟨fun m => pullR G (pt C ((jetMapA n m).comp (π m))), ⟨fun m => ?_, fun m => ?_, ?_⟩, fun c => ?_⟩
  · apply pushR_inj G
    rw [pushR_spMap, pushR_pullR, pushR_pullR, spMap_pt, ← hπtr m, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 2
    apply jet_ext
    intro j
    show jetTruncR R' (Fin n) m (jetMapA n (m + 1) (zR (m + 1) j)) = jetMapA n m (zR m j)
    rw [jetMapA_zR, jetMapA_zR]
    rfl
  · apply pushR_inj G
    rw [pushR_spMap, pushR_pullR, spMap_pt, pushR_one, ← pt_eps C (JetR R' (Fin n) 0)]
    congr 1
    have e : ((jetZeroR R' (Fin n) m).restrictScalars R).comp (jetMapA n m) = (jetMapA n 0).comp (jetZeroR R (Fin n) m) := by
      apply jet_ext
      intro j
      show jetZeroR R' (Fin n) m (jetMapA n m (zR m j)) = jetMapA n 0 (zR 0 j)
      rw [jetMapA_zR, jetMapA_zR]
      rfl
    rw [← AlgHom.comp_assoc, e, AlgHom.comp_assoc, hπ0, ← AlgHom.comp_assoc]
    congr 1
    exact AlgHom.ext fun r => (jetMapA n 0).commutes r
  · intro A _ _ aug m hJ y hy
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hz : spMap (aug.restrictScalars R) ≫ pushR G y = pt C ((Algebra.ofId R R').comp (eps C)) := by
      rw [← pushR_spMap, hy, pushR_one, pt_eps]
    obtain ⟨h, hh⟩ := exists_pt C (pushR G y) (le_preimage_of_nil C (aug.restrictScalars R) (aug_surj aug)
      (fun a ha => elt_nil _ (nil_of_pow _ hJ) a ha) _ _ hz)
    have hha : (aug.restrictScalars R).comp h = (Algebra.ofId R R').comp (eps C) :=
      pt_injective C (by rw [← spMap_pt, ← hh, hz])
    obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := isUnivRing_bc (eps C) m (π m) (huniv m) (hπa m) A aug hJ h hha
    have key : ∀ ψ' : JetR R' (Fin n) m →ₐ[R'] A,
        y = spMap ψ' ≫ pullR G (pt C ((jetMapA n m).comp (π m))) ↔
          h = (ψ'.restrictScalars R).comp ((jetMapA n m).comp (π m)) := by
      intro ψ'
      constructor
      · intro e
        apply pt_injective C
        rw [← hh, e, pushR_spMap, pushR_pullR, spMap_pt]
      · intro e
        apply pushR_inj G
        rw [hh, e, pushR_spMap, pushR_pullR, spMap_pt]
    exact ⟨ψ, ⟨h1, (key ψ).mpr h2⟩, fun ψ₂ hψ₂ => hu ψ₂ ⟨hψ₂.1, (key ψ₂).mp hψ₂.2⟩⟩
  · have e1 : pushR G (tvec (x := fun m => pullR G (pt C ((jetMapA n m).comp (π m)))) (algebraMap R R' ∘ c)) =
        pt C (((dualLift (algebraMap R R' ∘ c)).restrictScalars R).comp ((jetMapA n 1).comp (π 1))) := by
      show pushR G (spMap _ ≫ _) = _
      rw [pushR_spMap, pushR_pullR, spMap_pt]
    have e2 : spMap (dualMapA R R') ≫ tvec (x := x) c = pt C ((dualMapA R R').comp ((dualLift c).comp (π 1))) := by
      show spMap _ ≫ spMap _ ≫ x 1 = _
      rw [hπ 1, spMap_pt, spMap_pt]
    have e3 : (dualMapA R R').comp ((dualLift c).comp (π 1)) =
        ((dualLift (algebraMap R R' ∘ c)).restrictScalars R).comp ((jetMapA n 1).comp (π 1)) := by
      rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
      congr 1
      apply jet_ext
      intro j
      show dualMapA R R' (dualLift c (zR 1 j)) = dualLift (algebraMap R R' ∘ c) (jetMapA n 1 (zR 1 j))
      rw [jetMapA_zR, dualLift_zR, dualLift_zR, dualMapA_inr]
      rfl
    rw [← pushR_left, e1, ← e3, ← e2]
    rfl

theorem exists_isStandardSmooth_section {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p] (s : X ⟶ Y) (hs : s ≫ p = 𝟙 X)
    (x : X) (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V) (e : V ≤ p ⁻¹ᵁ U),
      x ∈ U ∧ U ≤ W ∧ U ≤ s ⁻¹ᵁ V ∧ (p.appLE U V e).hom.IsStandardSmooth := by
  obtain ⟨U, hU, V, hV, hxV, e, h⟩ := Smooth.exists_isStandardSmooth p (s x)
  have hps : ∀ y : X, p (s y) = y := fun y => by rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hxU : x ∈ U := by have := e hxV; rwa [← hps x]
  obtain ⟨r, hr, hxr⟩ := hU.exists_basicOpen_le (V := W ⊓ s ⁻¹ᵁ V) ⟨x, hx, hxV⟩ hxU
  have := hV.isLocalization_basicOpen (p.appLE U V e r)
  have := hU.isLocalization_basicOpen r
  refine ⟨X.basicOpen r, hU.basicOpen r, Y.basicOpen (p.appLE U V e r), hV.basicOpen _, by simp [Scheme.Hom.appLE],
    hxr, hr.trans inf_le_left, fun y hy => ?_, ?_⟩
  · have h1 : s y ∈ V := (hr hy).2
    have h2 : s y ∈ p ⁻¹ᵁ X.basicOpen r := by
      show p (s y) ∈ X.basicOpen r
      rwa [hps]
    show s y ∈ Y.basicOpen (p.appLE U V e r)
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro h1 h2
  · rw [hU.appLE_eq_away_map p hV]
    exact RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ h

theorem unit_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem exists_chart_pullback {X : Scheme.{0}} (G : Over X) [GrpObj G] {U : X.Opens} (hU : IsAffineOpen U)
    {V : G.left.Opens} (hV : IsAffineOpen V) (e : V ≤ G.hom ⁻¹ᵁ U) (hs : U ≤ (η[G]).left ⁻¹ᵁ V)
    (h : (G.hom.appLE U V e).hom.IsStandardSmooth) (G₀ : Over (Spec (CommRingCat.of Γ(X, U)))) [GrpObj G₀]
    (φ : G₀.left ⟶ G.left) (hφ : IsGrpPullback G₀ G hU.fromSpec φ) :
    ∃ C : Chart G₀, (alg0 C).IsStandardSmooth := by
  haveI : IsOpenImmersion φ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have hr : V ≤ φ.opensRange := by
    intro y hy
    have h1 : G.hom y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact e hy
    have h2 : y ∈ Set.range (pullback.fst G.hom hU.fromSpec) := by rwa [Scheme.Pullback.range_fst]
    obtain ⟨z, rfl⟩ := h2
    exact ⟨hφ.1.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, hφ.1.isoPullback_inv_fst]⟩
  let C : Chart G₀ := ⟨φ ⁻¹ᵁ V, hV.preimage_of_isOpenImmersion φ hr, fun y _ => by
    show φ ((η[G₀]).left y) ∈ V
    rw [← Scheme.Hom.comp_apply, unit_comp_of_isGrpPullback hφ, Scheme.Hom.comp_apply]
    exact hs (hU.range_fromSpec.subset (Set.mem_range_self _))⟩
  refine ⟨C, ?_⟩
  have key : CommRingCat.ofHom (alg0 C) = G.hom.appLE U V e ≫ φ.appLE V (φ ⁻¹ᵁ V) le_rfl := by
    apply Spec.map_injective
    rw [← cancel_mono hU.fromSpec, ← fromSpec_over C, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec G.hom hU hV e, ← Category.assoc (Spec.map _),
      IsAffineOpen.SpecMap_appLE_fromSpec φ hV C.hU le_rfl, Category.assoc, hφ.1.w]
  haveI := φ.isIso_app V hr
  have k2 : alg0 C = (φ.app V).hom.comp (G.hom.appLE U V e).hom := by
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg CommRingCat.Hom.hom key
  rw [k2]
  exact RingHom.isStandardSmooth_respectsIso.1 _ (asIso (φ.app V)).commRingCatIsoToRingEquiv h

end GlobalTheory.LieChart

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor MonObj
open scoped CategoryTheory.Obj

theorem exists_affine_lieBasis_baseChange (X : Scheme.{0}) (G : Over X) [GrpObj G] [Smooth G.hom] (x : X)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ U ≤ W ∧
      ∃ (n : ℕ) (v₀ : Fin n → (Sp (DualNumber Γ(X, U)) ⟶ G.left)),
        ∀ (R' : Type) [CommRing R'] (f : Γ(X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left),
          IsGrpPullback G' G (spMap f ≫ hU.fromSpec) φ →
            ∃ v' : Fin n → (epsR R' ⟶ G'),
              (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' := by
  obtain ⟨U, hU, V, hV, e, hxU, hUW, hs, h⟩ :=
    LieChart.exists_isStandardSmooth_section G.hom (η[G]).left (Over.w η[G]) x W hx
  let i : Spec (CommRingCat.of Γ(X, U)) ⟶ X := hU.fromSpec
  let G₀ : Over (Spec (CommRingCat.of Γ(X, U))) := (Over.pullback i).obj G
  have hφ₀ : IsGrpPullback G₀ G i (pullback.fst G.hom i) := isGrpPullback_pullback G i
  obtain ⟨C, hC⟩ := LieChart.exists_chart_pullback G hU hV e hs h G₀ _ hφ₀
  obtain ⟨n, y, hy⟩ := LieChart.univChart_of_chart G₀ C hC
  refine ⟨U, hU, hxU, hUW, n,
    fun j => (ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := y) (Pi.single j 1)).left ≫ pullback.fst G.hom i, ?_⟩
  intro R' _ f G' _ φ hφ
  let _ := f.toAlgebra
  obtain ⟨y', hy', e'⟩ := LieChart.univChart_baseChange_of_chart (R' := R') G₀ C n y hy
  obtain ⟨a, ha, haφ⟩ := grpPullback_iso hφ
    ((isGrpPullback_pullback G₀ (ReciprocityTheory.ChartRestriction.G.Chart.fB Γ(X, U) R')).comp hφ₀)
  refine ⟨fun j => ReciprocityTheory.ChartRestriction.G.Chart.tvec (x := y') (Pi.single j 1) ≫ a.inv, fun j => ?_, ?_⟩
  · have s : (algebraMap Γ(X, U) R' ∘ Pi.single j (1 : Γ(X, U)) : Fin n → R') = Pi.single j 1 := by
      funext i; by_cases hij : i = j <;> simp [hij, Pi.single_apply]
    have := e' (Pi.single j 1)
    rw [s] at this
    rw [← haφ, ← Category.assoc, ← Over.comp_left, Category.assoc, a.inv_hom_id, Category.comp_id,
      ← Category.assoc, this, Category.assoc]
  · refine ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_iso a ?_
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ReciprocityTheory.ChartRestriction.G.Chart.basis_of_chart hy'

end GlobalTheory
