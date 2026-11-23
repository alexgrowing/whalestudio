import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam.CarriesAt

section Tri

variable {ι : Type} {m : ι → ℕ} {K : Type} [Field K]

theorem par_of_tri {h : Mat m K} (hd : ∀ τ i, h τ i i ≠ 0) (hl : ∀ τ i k, i < k → h τ i k = 0) : Par m ⊤ h := fun τ => by
  have hdet : (h τ).det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular (h τ) fun i j hij => hl τ i j hij]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd τ i
  exact ⟨fun _ _ => trivial, hdet, trivial, fun i j _ hij => hl τ i j hij⟩

theorem Par.diag_ne {O : Subring K} {h : Mat m K} (hp : Par m O h) (τ : ι) (i : Fin (m τ)) : h τ i i ≠ 0 := by
  have := hp.det_ne τ
  rw [Matrix.det_of_lowerTriangular (h τ) fun a b hab => (hp τ).2.2.2 a b a.2 hab] at this
  exact Finset.prod_ne_zero_iff.1 this i (Finset.mem_univ i)

end Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_cast {R : Type} [CommRing R] {φ : c.F →+* R} {x x' : Sp R ⟶ Z.X} (h : x = x') (g : EigFrame Z φ x) :
    ∃ g' : EigFrame Z φ x', ∀ τ i, g'.v τ i = g.v τ i := by
  subst h
  exact ⟨g, fun _ _ => rfl⟩

theorem spMap_dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (dualMap (ψ.comp ρ)) = spMap (dualMap ψ) ≫ spMap (dualMap ρ) := by
  have e : dualMap (ψ.comp ρ) = (dualMap ψ).comp (dualMap ρ) := by
    ext r <;> simp [dualMap]
  rw [e]
  simp [spMap, Spec.map_comp]

theorem coord_of_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {g : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''} {A : Mat Dw.mult R''}
    (hx : x' = spMap ρ ≫ x) (hφ : φ' = ρ.comp φ) (hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i)
    (h : f.Coord (ψ.comp ρ) g A) : f'.Coord ψ g A := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, hx, ← Category.assoc]
    congr 1
    simp [spMap, Spec.map_comp]
  · rw [h2, hφ, RingHom.comp_assoc]
  · have e : (fun k => spMap (dualMap ψ) ≫ f'.v τ k) = fun k => spMap (dualMap (ψ.comp ρ)) ≫ f.v τ k := by
      funext k
      rw [hv, spMap_dualMap_comp, Category.assoc]
    rw [e]
    exact h3 τ i

theorem algebraMap_eq_comp_specializes {X : Scheme.{0}} [IsIntegral X] {y y' : X} (h : y' ⤳ y) :
    algebraMap (X.presheaf.stalk y) X.functionField =
      (algebraMap (X.presheaf.stalk y') X.functionField).comp (X.presheaf.stalkSpecializes h).hom :=
  (congrArg CommRingCat.Hom.hom
    (TopCat.Presheaf.stalkSpecializes_comp X.presheaf (genericPoint_specializes y') h)).symm

theorem exists_adapted {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {S : Fr (ratOf C.Y) Dw.mult Dw.mult}
    {A₀ : Mat Dw.mult C.Y.Fn} (hA₀ : A₀ ∈ S.S (genericPoint C.Y.X))
    (hTied : ∀ y : C.Y.X, ∀ A ∈ S.S y, ∃ (φ : c.F →+* C.Y.X.presheaf.stalk y)
      (f : EigFrame Z φ (stalkPt C.Y y ≫ C.π ≫ genι Z)),
      f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 (A₀ * A⁻¹))
    {K : Type} [Field K] {φ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z φ x) {y y' : C.Y.X} (hsp : y' ⤳ y)
    (ψ' : C.Y.X.presheaf.stalk y' →+* K) {φ₁ : c.F →+* C.Y.X.presheaf.stalk y}
    (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) {T : Mat Dw.mult C.Y.Fn} {h : Mat Dw.mult K}
    (hT1 : f.Coord (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 T)
    (hT : Par Dw.mult ⊤ T)
    (hh1 : f.Coord (ψ'.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) g h) :
    ∃ A ∈ S.S y', ∃ (φ₂ : c.F →+* C.Y.X.presheaf.stalk y') (f₁ : EigFrame Z φ₂ (stalkPt C.Y y' ≫ C.π ≫ genι Z)),
      f₁.Coord (algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord ψ' g h := by
  set ρ := (C.Y.X.presheaf.stalkSpecializes hsp).hom with hρdef
  set alg := algebraMap (C.Y.X.presheaf.stalk y') C.Y.X.functionField with halg
  have hρ : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y y' := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hinj : Function.Injective alg := IsFractionRing.injective _ _

  have hfS : f.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f inferInstance
  obtain ⟨f₀, hf₀⟩ := hfS (C.Y.X.presheaf.stalk y') ρ
  have hx' : spMap ρ ≫ stalkPt C.Y y ≫ C.π ≫ genι Z = stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [← Category.assoc, hρ]
  obtain ⟨f', hf'⟩ := exists_cast hx' f₀
  have hv : ∀ τ i, f'.v τ i = spMap (dualMap ρ) ≫ f.v τ i := fun τ i => (hf' τ i).trans (hf₀ τ i)
  have hT1' : f'.Coord alg C.f0 T :=
    coord_of_bc hx'.symm rfl hv (algebraMap_eq_comp_specializes hsp ▸ hT1)
  have hh1' : f'.Coord ψ' g h := coord_of_bc hx'.symm rfl hv hh1

  obtain ⟨A', hA'⟩ := S.nonempty y'
  obtain ⟨φ'', f'', hf''⟩ := hTied y' A' hA'
  obtain rfl : φ'' = ρ.comp φ₁ := RingHom.ext fun a => hinj (by
    have e1 := RingHom.congr_fun hf''.2.1 a
    have e2 := RingHom.congr_fun hT1'.2.1 a
    exact e1.symm.trans e2)
  have hS'' : f''.Stable := EigStable.stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f'' inferInstance
  have hid : stalkPt C.Y y' ≫ C.π ≫ genι Z = spMap (RingHom.id _) ≫ stalkPt C.Y y' ≫ C.π ≫ genι Z := by
    rw [show spMap (RingHom.id (C.Y.X.presheaf.stalk y')) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  obtain ⟨⟨G, hG, -⟩, hGu⟩ := (GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ (ρ.comp φ₁) _ (RingHom.id _) inferInstance hS''
    hid (RingHom.id_comp _).symm).1 f'
  have hGd := hGu G hG
  have hcomp : f''.Coord alg C.f0 (T * G.map alg) := by
    have := CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ f'' _ _ _ f' _ _ _ C.f0 (RingHom.id _) alg G T inferInstance hG hT1'
    rwa [RingHom.comp_id] at this
  have heq : A₀ * A'⁻¹ = T * G.map alg :=
    (((GlobalTheory.ShFam.EigCoord.coord_spec E H Dw l Xo c O β Z _ _ _ f'' _ _ _ alg inferInstance hS'' hf''.1 hf''.2.1).1 C.f0).1).unique hf'' hcomp
  have hAA : T⁻¹ * A₀ * A'⁻¹ = G.map alg := by
    rw [mul_assoc, heq, ← mul_assoc, Mat.inv_mul hT.det_ne, one_mul]
  have hPg : Par Dw.mult ((ratOf C.Y).O (genericPoint C.Y.X)).toSubring (A₀ * A'⁻¹) :=
    (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hA₀
  have hlow : Par Dw.mult ⊤ (G.map alg) := by
    rw [← hAA, mul_assoc]
    exact hT.inv.mul (hPg.mono le_rfl le_top)
  have hpar : Par Dw.mult ((ratOf C.Y).O y').toSubring (T⁻¹ * A₀ * A'⁻¹) := fun τ => by
    rw [hAA]
    have hdet : (G.map alg τ).det = alg (G τ).det := (alg.map_det (G τ)).symm
    obtain ⟨u, hu⟩ := hGd τ
    refine ⟨fun i j => mem_O_ratOf.2 ⟨G τ i j, rfl⟩, hlow.det_ne τ, ?_, fun i j hi hij => (hlow τ).2.2.2 i j hi hij⟩
    refine mem_O_ratOf.2 ⟨(u⁻¹ : (C.Y.X.presheaf.stalk y')ˣ), ?_⟩
    rw [hdet, ← hu]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨T⁻¹ * A₀, (Fr.mem_iff hA').2 hpar, ρ.comp φ₁, f', ?_, hh1'⟩
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hA₀
  rw [Mat.mul_inv_rev, Mat.inv_inv hT.det_ne, ← mul_assoc, Mat.mul_inv hA₀d, one_mul]
  exact hT1'

theorem carries_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (S : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₀ : Mat Dw.mult C.Y.Fn) (K : Type) [Field K] (φ : c.F →+* K) (x : Sp K ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp K ⟶ C.Y.X), Tied e C.Y C.π C.f0 S A₀ → (C.Carries p g ↔ ∃ A ∈ S.S (p (IsLocalRing.closedPoint K)), ∃ (φ₁ : c.F →+* C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) (f₁ : EigFrame Z φ₁ (stalkPt C.Y (p (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z)) (h : Mat Dw.mult K), f₁.Coord (algebraMap (C.Y.X.presheaf.stalk (p (IsLocalRing.closedPoint K))) C.Y.X.functionField) C.f0 (A₀ * A⁻¹) ∧ f₁.Coord (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom g h ∧ Par Dw.mult ⊤ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C S A₀ K _ φ x g p hT
  obtain ⟨hA₀, hTied⟩ := hT
  constructor
  · rintro ⟨y, ψ, φ₁, f, t, t', hp, hf, hg⟩
    obtain ⟨T, hT1, hT2, hT3⟩ := (f.tri_iff _ C.f0 t).1 hf
    obtain ⟨h, hh1, hh2, hh3⟩ := (f.tri_iff _ g t').1 hg
    have hsp : p (IsLocalRing.closedPoint K) ⤳ y := by
      have : p (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by
        rw [hp]
        exact ⟨spMap ψ (IsLocalRing.closedPoint K), rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have hψ : ψ = (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
      refine EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 ?_)
      have e1 := spMap_stalkClosedPointTo p
      have e2 : spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom ≫ C.Y.X.fromSpecStalk y = C.Y.X.fromSpecStalk _ :=
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
      have e3 : spMap ((Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom.comp (C.Y.X.presheaf.stalkSpecializes hsp).hom) =
          spMap (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom ≫ spMap (C.Y.X.presheaf.stalkSpecializes hsp).hom := by
        simp [spMap, Spec.map_comp]
      rw [e3, Category.assoc, e2, e1]
      exact hp.symm
    obtain ⟨A, hA, φ₂, f₁, c1, c2⟩ := exists_adapted C hA₀ hTied g hsp _ f hT1
      (par_of_tri (fun τ i => by rw [hT2]; exact Units.ne_zero _) hT3) (hψ ▸ hh1)
    exact ⟨A, hA, φ₂, f₁, h, c1, c2, par_of_tri (fun τ i => by rw [hh2]; exact Units.ne_zero _) hh3⟩
  · rintro ⟨A, hA, φ₁, f₁, h, h1, h2, h3⟩
    have hgen := Fr.mem_genericPoint hA
    have hP : Par Dw.mult ⊤ (A₀ * A⁻¹) := ((Fr.mem_iff hgen).1 hA₀).mono le_rfl le_top
    refine ⟨_, (Scheme.stalkClosedPointTo (R := CommRingCat.of K) p).hom, φ₁, f₁,
      fun τ i => Units.mk0 _ (Par.diag_ne hP τ i), fun τ i => Units.mk0 _ (Par.diag_ne h3 τ i),
      (spMap_stalkClosedPointTo p).symm, (f₁.tri_iff _ C.f0 _).2 ⟨_, h1, fun _ _ => rfl, fun τ i k hik => (hP τ).2.2.2 i k i.2 hik⟩,
      (f₁.tri_iff _ g _).2 ⟨h, h2, fun _ _ => rfl, fun τ i k hik => (h3 τ).2.2.2 i k i.2 hik⟩⟩

end GlobalTheory.ShFam.CarriesAt
