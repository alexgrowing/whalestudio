import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtLatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem htLat_le_omLat (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) : M.htLat N p ≤ M.omLat p := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
  refine Submodule.span_induction (p := fun e _ => w e ∈ regAt ξ p) ?_ ?_ ?_ ?_ he
  · rintro e ⟨v, hv, hev⟩
    obtain ⟨l, rfl⟩ := M₀.onto v hv
    have : e = j l := M.inj (Over.OverMorphism.ext (hev.trans (hj l).symm))
    rw [this, hw]
    exact ⟨_, rfl⟩
  · simp
  · intro a b _ _ ha hb
    simpa using add_mem ha hb
  · intro c a _ ha
    have : w (c • a) = (c : Ω) * w a := by
      rw [Subring.smul_def, map_smul, smul_eq_mul]
    rw [this]
    exact mul_mem c.2 ha

def triv (R : Type) [CommRing R] [IsDomain R] : BT.QFGroup R Unit where
  G := 𝟙_ _
  flat := inferInstanceAs (Flat (𝟙 _))
  quasiFinite := inferInstanceAs (LocallyQuasiFinite (𝟙 _))
  separated := inferInstanceAs (IsSeparated (𝟙 _))
  quasiCompact := inferInstanceAs (QuasiCompact (𝟙 _))
  finPres := inferInstanceAs (LocallyOfFinitePresentation (𝟙 _))
  pt := 1
  pt_inj _ _ _ _ _ := rfl
  pt_onto g hg := by
    refine ⟨(), IsLocalRing.closedPoint (FractionRing R), ?_⟩
    have h : ((1 : Unit →* (BT.genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))))) ()).left = (BT.genPt R).hom := by
      have := Over.w ((1 : Unit →* (BT.genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))))) ())
      simpa using this
    rw [h]
    apply PrimeSpectrum.ext
    refine Eq.trans ?_ (show g.asIdeal = ⊥ from hg).symm
    change Ideal.comap (algebraMap R (FractionRing R)) (IsLocalRing.maximalIdeal (FractionRing R)) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)]
  gen_reduced := by
    have : IsIso (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (IsIso (𝟙 _))
    have : IsReduced (BT.genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
    exact isReduced_of_isOpenImmersion (pullback.snd _ (BT.genPt R).hom)

theorem triv_torsion {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ)
    (h : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ G), g ^ N = 1 → g = 1) :
    (triv R).IsTorsionAlong G x N (1 : Over.mk x ⟶ G).left := by
  have key : ∀ (Y : Over (Spec (CommRingCat.of R))) (y : Y ⟶ (triv R).G),
      y.left ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (Y.hom ≫ x) ⟶ G).left := by
    intro Y y
    have hy : y.left = Y.hom := (Category.comp_id _).symm.trans (Over.w y)
    have := MonObj.comp_one (M := G) (Over.homMk Y.hom rfl : Over.mk (Y.hom ≫ x) ⟶ Over.mk x)
    rw [hy]
    exact congrArg (fun q => q.left) this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Over.w (1 : Over.mk x ⟶ G)).trans (Category.id_comp _).symm
  · intro Y y z y₀ z₀ hy hz
    rw [key] at hy hz ⊢
    rw [Over.OverMorphism.ext hy, Over.OverMorphism.ext hz, _root_.mul_one]
  · intro Y y z _
    exact toUnit_unique _ _
  · intro Y g
    constructor
    · intro hg
      exact ⟨toUnit _, by rw [key, h Y g hg]⟩
    · rintro ⟨y, hy⟩
      rw [key] at hy
      rw [← Over.OverMorphism.ext hy, one_pow]

theorem ga_torsion {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (hN : IsUnit (N : R))
    (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x) ⟶ LieInh.gaObj X) (hg : g ^ N = 1) : g = 1 := by
  let φ : (Over.mk (Y.hom ≫ x) ⟶ LieInh.gaObj X) →* Multiplicative Γ(Y.left, ⊤) :=
    ⟨⟨LieInh.gaEquiv _, LieInh.gaEquiv_one⟩, LieInh.gaEquiv_mul⟩
  apply (LieInh.gaEquiv _).injective
  change φ g = φ 1
  have h1 : φ g ^ N = 1 := by rw [← map_pow, hg, map_one]
  have h2 : (N : Γ(Y.left, ⊤)) * (φ g).toAdd = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [nsmul_eq_mul] using this
  have h3 : IsUnit (N : Γ(Y.left, ⊤)) := by
    have := hN.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ Y.hom.appTop).hom
    simpa using this
  rw [map_one]
  exact h3.mul_right_eq_zero.1 h2

theorem ga_isHTFormOver {R : Type} [CommRing R] [IsDomain R] (x : Spec (CommRingCat.of R) ⟶ X) (k : R →+* Ω)
    (hk : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (N : ℕ) (hN : IsUnit (N : R)) :
    (LieInh.gaLie ξ).IsHTFormOver N x k LinearMap.id := by
  have hs : Subsingleton (R ⧸ Ideal.span {(N : R)}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hN)
  have hs' : Subsingleton (DualNumber (R ⧸ Ideal.span {(N : R)})) :=
    ⟨fun a b => TrivSqZeroExt.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  have he : IsEmpty (Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)})))) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum _))
  refine ⟨inferInstance, Unit, inferInstance, triv R, _, R, inferInstance, inferInstance, LieInh.gaLie x, k, 1,
    LinearMap.id, triv_torsion x N (ga_torsion x N hN), fun e => ?_, ⟨1, fun t => ?_, fun e => ?_⟩, fun _ => rfl⟩
  · symm
    refine (LieInh.map_gaPt (dualMap k) _ (Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ) ?_ _).trans ?_
    · rw [← hk, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · have : dualMap k (TrivSqZeroExt.inr e) = TrivSqZeroExt.inr (k e) := by ext <;> simp [dualMap]
      rw [this]
      rfl
  · simp [BT.valAt]
  · exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _,
      Subsingleton.elim _ _⟩

theorem ga_id_mem_htLat (p : Cpt ξ) [IsDomain (X.presheaf.stalk p.1)] (N : ℕ)
    (hN : IsUnit (N : X.presheaf.stalk p.1)) :
    (LinearMap.id : Module.Dual Ω Ω) ∈ (LieInh.gaLie ξ).htLat N p := by
  refine Submodule.subset_span (ga_isHTFormOver (R := X.presheaf.stalk p.1) _ _ ?_ N hN)
  change Spec.map (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = _
  rw [Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ

theorem ga_htLat_ne_bot [IsIntegral X] (p : Cpt ξ) (N : ℕ) (hN : IsUnit (N : X.presheaf.stalk p.1)) :
    (LieInh.gaLie ξ).htLat N p ≠ ⊥ := fun h => by
  have := ga_id_mem_htLat p N hN
  rw [h, Submodule.mem_bot] at this
  exact one_ne_zero (LinearMap.congr_fun this (1 : Ω))

theorem isHT_add_nsmul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {x : Spec (CommRingCat.of R) ⟶ X} (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L]
    (M : LieModel G x L) (N : ℕ) (χ : T →* Rˣ) (w w' : Module.Dual R L) (h : Γ.IsHT i M N χ w) :
    Γ.IsHT i M N χ (w + (N : R) • w') := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, sub_add_cancel_left, neg_mem_iff]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end GlobalTheory.CompanionTheory.Ar.HtLatModel
