import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusPointEqOneOfAxes

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_sectionHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (a : T.left ⟶ S) (ha : a = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') →* (Over.mk a ⟶ G), (∀ x, (ρ x).left = x.left ≫ φ) ∧ Function.Surjective ρ := by
  subst ha
  refine ⟨pushHom h T, fun _ => rfl, fun c => ?_⟩
  exact ⟨Over.homMk (h.1.lift c.left T.hom (Over.w c)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem eSec_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    eSec G' ≫ φ = (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_fac_residue (V K : Type) [CommRing V] [IsLocalRing V] [Field K] (r : Sp K ⟶ Sp V)
    (hr : Set.range r = {IsLocalRing.closedPoint V}) :
    ∃ s : Sp K ⟶ Sp (IsLocalRing.ResidueField V), s ≫ spMap (IsLocalRing.residue V) = r := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective r
  have h : PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint V := by
    have : (Spec.map ψ) (IsLocalRing.closedPoint K) ∈ Set.range (Spec.map ψ) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  let ψ' : V →+* K := ψ.hom
  have : IsLocalHom ψ' := (IsLocalRing.isLocalHom_iff_comap_closedPoint ψ').2 h
  refine ⟨spMap (IsLocalRing.ResidueField.lift ψ'), ?_⟩
  rw [← Spec.map_comp]
  congr 1

theorem Core.Test.exists_isGt_fibre {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (K : Type) [Field K] (r : Sp K ⟶ Sp τ.V) (hr : Set.range r = {IsLocalRing.closedPoint τ.V}) :
    ∃ (G₁ : Over (Sp K)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (E : SplitExt (Sp K)) (φ : G₁.left ⟶ τ.H.left),
      E.IsGt G₁ ∧ IsGrpPullback G₁ τ.H r φ := by
  obtain ⟨s, rfl⟩ := exists_fac_residue τ.V K r hr
  obtain ⟨S, hS⟩ := τ.split
  obtain ⟨E, -, -, -, -, hE⟩ := gtBaseChange _ _ s S _ hS
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact ⟨_, _, Functor.isCommMonObj_obj, E, _, hE,
    (isGrpPullback_pullback _ s).comp (isGrpPullback_pullback τ.H _)⟩

theorem Core.Test.eSec_comp_f {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) :
    (eSec τ.H ≫ τ.f : Sp τ.V ⟶ C.G.toScheme) = τ.y₀ ≫ C.e := by
  have := C.proper
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  have : IsDominant (Out.jK τ.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective τ.V _)]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated C.GG.hom ?_ (Out.jK τ.V) ?_
  · have h₁ : (eSec τ.H ≫ τ.H.hom : Sp τ.V ⟶ Sp τ.V) = 𝟙 _ := Over.w η[τ.H]
    have h₂ : C.e ≫ C.GG.hom = 𝟙 _ := C.e_sec
    rw [Category.assoc, Category.assoc, τ.f_over, h₂, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.y₀) h₁).trans (Category.id_comp _))
  · have h₁ := @eSec_comp_of_isGrpPullback _ _ _ _ (_) (_) _ _ τ.φ_cart
    have h₂ := eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (Out.jK τ.V))
    rw [← reassoc_of% τ.yK_fac, C.e_zero]
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.a) h₁) |>.trans (Category.assoc _ _ _))
    rw [τ.φ_f]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) h₂.symm).trans (Category.assoc _ _ _))

theorem Core.fibLaw_of_testCart : ∀ C : Core, C.TestCart → C.FibLaw := by
  intro C hC p _ y y' τ τ' K _ _ r r' hr hr' hy c d c' d' hc hd
  obtain ⟨G₁, _, _, E₁, φ₁, g₁, h₁⟩ := τ.exists_isGt_fibre K r hr
  obtain ⟨G₂, _, _, E₂, φ₂, g₂, h₂⟩ := τ'.exists_isGt_fibre K r' hr'
  have P₁ := h₁.1.paste_horiz (hC p y τ)
  have P₂ := h₂.1.paste_horiz (hC p y' τ')
  let i : G₁ ⟶ G₂ := Over.homMk (P₂.lift (φ₁ ≫ τ.f) G₁.hom (by rw [P₁.w, hy])) (P₂.lift_snd _ _ _)
  have hi : i.left ≫ φ₂ ≫ τ'.f = φ₁ ≫ τ.f := P₂.lift_fst _ _ _
  have u₁ : η[G₁].left ≫ φ₁ ≫ τ.f = (r ≫ τ.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) (eSec_comp_of_isGrpPullback h₁)).trans
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) τ.eSec_comp_f)))
  have u₂ : η[G₂].left ≫ φ₂ ≫ τ'.f = (r' ≫ τ'.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ'.f) (eSec_comp_of_isGrpPullback h₂)).trans
      ((Category.assoc _ _ _).trans (congrArg (r' ≫ ·) τ'.eSec_comp_f)))
  have hone : η[G₁] ≫ i = η[G₂] := by
    apply Over.OverMorphism.ext
    apply P₂.hom_ext
    · rw [Over.comp_left, Category.assoc, hi, u₁, u₂]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.e) hy).trans (Category.assoc _ _ _))
    · rw [Over.w, Over.w]
  have := isMonHom_of_isGt_of_one K E₁ E₂ G₁ G₂ g₁ g₂ i hone
  obtain ⟨ρ₁, l₁, s₁⟩ := exists_sectionHom h₁ (Over.mk (𝟙 _)) r (Category.id_comp _).symm
  obtain ⟨ρ₂, l₂, -⟩ := exists_sectionHom h₂ (Over.mk (𝟙 _)) r' (Category.id_comp _).symm
  have key : ∀ x, (ρ₁ x).left ≫ τ.f = (ρ₂ (x ≫ i)).left ≫ τ'.f := fun x => by
    rw [l₁, l₂, Over.comp_left, Category.assoc, Category.assoc, Category.assoc, hi]
  have inj : ∀ (x) (z : Over.mk r' ⟶ τ'.H), (ρ₁ x).left ≫ τ.f = z.left ≫ τ'.f → z = ρ₂ (x ≫ i) := fun x z hz => by
    apply Over.OverMorphism.ext
    apply (hC p y' τ').hom_ext
    · exact hz.symm.trans (key x)
    · rw [Over.w, Over.w]
  obtain ⟨c, rfl⟩ := s₁ c
  obtain ⟨d, rfl⟩ := s₁ d
  obtain rfl := inj c c' hc
  obtain rfl := inj d d' hd
  constructor
  · rw [← map_mul, ← map_mul, ← MonObj.mul_comp]
    exact key _
  · rw [← map_inv, ← map_inv, ← GrpObj.inv_comp]
    exact key _

end GlobalTheory.ZJ
