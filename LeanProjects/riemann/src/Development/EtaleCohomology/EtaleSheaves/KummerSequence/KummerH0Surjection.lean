import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSeqPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf
open CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder.KummerH0Surjection

theorem resMap_comp_homotopy (R : Type) [CommRing R] {F G L : Shv R} (f : F ⟶ G) (g : G ⟶ L) :
    Nonempty (Homotopy (resMap R (f ≫ g)) (resMap R f ≫ resMap R g)) := by
  refine ⟨?_⟩
  have H : Homotopy (InjectiveResolution.desc (f ≫ g) (injectiveResolution L) (injectiveResolution F))
      (InjectiveResolution.desc f (injectiveResolution G) (injectiveResolution F) ≫
        InjectiveResolution.desc g (injectiveResolution L) (injectiveResolution G)) :=
    InjectiveResolution.descHomotopy (f ≫ g) _ _ (by simp) (by simp)
  exact (H.extend ComplexShape.embeddingUpNat).trans
    (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _))

theorem post_comp (R : Type) [CommRing R] (K : Cx R) {F G L : Shv R} (f : F ⟶ G) (g : G ⟶ L) (n : ℤ)
    (x : HK R K F n) : HK.post R K (f ≫ g) n x = HK.post R K g n (HK.post R K f n x) := by
  obtain ⟨H⟩ := resMap_comp_homotopy R f g
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨a.1.comp (Cochain.ofHomotopy H) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub, Cochain.ofHom_comp]

def kumM (q : ℕ) : (kumSC q).X₃ ⟶ Gm := cokernel.desc (kernel.ι (powGm q)) (powGm q) (kernel.condition _)

instance kumM_mono (q : ℕ) : Mono (kumM q) :=
  inferInstanceAs (Mono (Abelian.factorThruCoimage (powGm q)))

theorem sec_injective {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have h1 : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have h2 : Mono (φ.hom.app (op U)) := (NatTrans.mono_iff_mono_app _).mp h1 (op U)
  exact (ModuleCat.mono_iff_injective _).mp h2

def LeafKumSecSurj : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Function.Surjective (Sec.map (kumM q) (U := U))

def LeafKumBij : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], IsUnit (q : B) →
  Function.Bijective (HK.post ℤ ((chains ℤ).obj (sp B)) (kumM q) 0)

theorem LeafKumBij_of (hS : LeafKumSecSurj) : LeafKumBij := by
  intro hy q _ B _ hq
  have hA10 : A10 := hy.2.2.2.2.2.2.2.2.1
  refine hA10 ℤ (sp B) (kumM q) ?_ 0
  intro U ⟨x⟩
  refine ⟨sec_injective _ U, hS q U ?_⟩
  have x' : U ⟶ Spec (CommRingCat.of B) := x
  have h1 : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of B), ⊤)) := by
    have := hq.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
    simpa using this
  simpa using h1.map x'.appTop.hom

def unitsToSec (U : Scheme.{0}) : Additive (Γ(U, ⊤))ˣ →+ Sec Gm U where
  toFun x := ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom ⟨x⟩
  map_zero' := by
    have := map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    exact this
  map_add' x y := by
    have := map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
      (⟨x⟩ : ULift (Additive (Γ(U, ⊤))ˣ)) ⟨y⟩
    exact this

theorem pow_unitsToSec (q : ℕ) (U : Scheme.{0}) (x : Additive (Γ(U, ⊤))ˣ) :
    Sec.map (powGm q) (unitsToSec U x) = unitsToSec U (q • x) := by
  have h := toSheafify_naturality Scheme.etaleTopology (Functor.whiskerLeft Scheme.Γ (powNat q))
  have h2 := congrArg (fun η => (η.app (op U)).hom (⟨x⟩ : ULift (Additive (Γ(U, ⊤))ˣ))) h
  exact h2.symm

def EtaleDegreeZeroCohomologyNaturallyIsoToSections : Prop := Hyps → ∃ e : ∀ (F : Shv ℤ) (X : Scheme.{0}), Sec F X ≃+ H ℤ (sch.obj X) F 0,
  ∀ {F G : Shv ℤ} (φ : F ⟶ G) (X : Scheme.{0}) (s : Sec F X),
    HK.post ℤ ((chains ℤ).obj (sch.obj X)) φ 0 (e F X s) = e G X (Sec.map φ s)

def LeafGmSecSurj : Prop := ∀ (B : Type) [CommRing B],
  Function.Surjective (unitsToSec (Spec (CommRingCat.of B)))

def EtaleUnitsDegreeZeroCohomologySurjectiveFromRingUnits : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B],
  ∃ u : Additive Bˣ →+ H ℤ (sp B) Gm 0, Function.Surjective u ∧
    ∀ x : Additive Bˣ, HK.post ℤ ((chains ℤ).obj (sp B)) (powGm q) 0 (u x) = u (q • x)

theorem etale_units_degree_zero_cohomology_of_natural_iso_and_surjective (hN : EtaleDegreeZeroCohomologyNaturallyIsoToSections) (hS : LeafGmSecSurj) : EtaleUnitsDegreeZeroCohomologySurjectiveFromRingUnits := by
  intro hy q _ B _
  obtain ⟨e, he⟩ := hN hy
  let ψ : Bˣ →* (Γ(Spec (CommRingCat.of B), ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro v
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.toMonoidHom v, ?_⟩
    ext
    simp [ψ]
  let u : Additive Bˣ →+ H ℤ (sp B) Gm 0 :=
    ((e Gm (Spec (CommRingCat.of B))).toAddMonoidHom.comp (unitsToSec _)).comp (MonoidHom.toAdditive ψ)
  refine ⟨u, ?_, ?_⟩
  · intro y
    obtain ⟨s, rfl⟩ := (e Gm (Spec (CommRingCat.of B))).surjective y
    obtain ⟨v, rfl⟩ := hS B s
    obtain ⟨w, hw⟩ := hψ (Additive.toMul v)
    exact ⟨Additive.ofMul w, by simp [u, hw]⟩
  · intro x
    simp only [u, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [he, pow_unitsToSec, ← map_nsmul (MonoidHom.toAdditive ψ)]

theorem kumSC_g_kumM (q : ℕ) : (kumSC q).g ≫ kumM q = powGm q := cokernel.π_desc _ _ _

theorem etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective (hS : LeafKumSecSurj) (hN : EtaleDegreeZeroCohomologyNaturallyIsoToSections) (hG : LeafGmSecSurj) :
    LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := by
  intro hy q _ B _ hq
  obtain ⟨u, hus, hu⟩ := etale_units_degree_zero_cohomology_of_natural_iso_and_surjective hN hG hy q B
  let e := AddEquiv.ofBijective (HK.post ℤ ((chains ℤ).obj (sp B)) (kumM q) 0) (LeafKumBij_of hS hy q B hq)
  refine ⟨e.symm.toAddMonoidHom.comp u, e.symm.surjective.comp hus, ?_⟩
  intro x
  refine ⟨u x, ?_⟩
  apply e.injective
  show HK.post ℤ ((chains ℤ).obj (sp B)) (kumM q) 0 (HK.post ℤ ((chains ℤ).obj (sp B)) (kumSC q).g 0 (u x)) =
    e (e.symm (u (q • x)))
  rw [AddEquiv.apply_symm_apply, ← hu]
  have h := post_comp ℤ ((chains ℤ).obj (sp B)) (kumSC q).g (kumM q) 0 (u x)
  have h2 : HK.post ℤ ((chains ℤ).obj (sp B)) ((kumSC q).g ≫ kumM q) 0 (u x) =
      HK.post ℤ ((chains ℤ).obj (sp B)) (powGm q) 0 (u x) := by
    erw [kumSC_g_kumM]; rfl
  exact h.symm.trans h2

end LateralTheory.E.H2CurveOrder.KummerH0Surjection
