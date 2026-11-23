import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.ThmASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GeneratorSchemeProperties
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGrpObjSplitExtensionOfGenerators
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfDisjointCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitFiniteHenselianOfLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharBundlePrimitive
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusModel

open GlobalTheory.AdicColimit

section BaseChange

variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem exists_isGt (hG : GlobalFnsSt) (E : SplitExt S) :
    ∃ (H : Over S) (_ : GrpObj H), IsCommMonObj H ∧ E.IsGt H := by
  letI := E.free
  letI := E.finite
  have hN : ∀ k, (E.O (E.basis k)).L.IsLB := fun k => (E.O (E.basis k)).isLB
  obtain ⟨G, q, u, hu⟩ := exists_generatorScheme E.B.left _ (fun k => (E.O (E.basis k)).L) hN
  obtain ⟨h₁, h₂, h₃, -, -⟩ :=
    generatorScheme_properties E.B.left _ (fun k => (E.O (E.basis k)).L) hN G q u hu
  obtain ⟨inst, hc, d, -⟩ := exists_grpObj_gtDatum_of_generators hG S E G q u hu h₁ inferInstance h₃
  exact ⟨Over.mk (q ≫ E.B.hom), inst, hc, ⟨d⟩⟩

def polPull [IsAffine S] (P : PolAV S) : PolAV S' :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have hw := (isGen_iff _).1 (PolBaseChange.lbIso_refl hL').choose_spec
  { A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top S) (fun _ => trivial) P.ample
    ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }

theorem torsion_pullback (B : Over S) [GrpObj B] (N : ℕ) (h₁ : IsFinite (𝟙 B ^ N).left) (h₂ : Flat (𝟙 B ^ N).left) :
    IsFinite (torsion ((Over.pullback f).obj B) N).hom ∧ Flat (torsion ((Over.pullback f).obj B) N).hom := by
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁ h₂
  have H := MulEtaleDvr.isPullback_torsion ((Over.pullback f).obj B) N
  rw [← MulEtaleDvr.pullback_map_mulN] at H
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) H
      (MorphismProperty.overPullbackMap (P := @IsFinite) f _ h₁),
    MorphismProperty.of_isPullback (P := @Flat) H (MorphismProperty.overPullbackMap (P := @Flat) f _ h₂)⟩

variable {H : Over S} [GrpObj H]

theorem exists_pushEquiv (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ π : (T ⟶ (Over.pullback f).obj H) ≃* (Over.mk s ⟶ H), ∀ x, (π x).left = x.left ≫ pullback.fst H.hom f := by
  subst hs
  have h := isGrpPullback_pullback H f
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun y => ?_⟩, fun x => rfl⟩
  exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

def actPull [IsCommMonObj H] {O : Type} [Ring O] (ρ : RingAct H O) : RingAct ((Over.pullback f).obj H) O where
  act a := (Over.pullback f).map (ρ.act a)
  hom a := by have := ρ.hom a; infer_instance
  map_one := by rw [ρ.map_one, CategoryTheory.Functor.map_id]
  map_mul a b := by rw [ρ.map_mul, CategoryTheory.Functor.map_comp]
  map_add a b := by
    rw [ρ.map_add]
    exact map_mul (Over.pullback f).homMonoidHom (ρ.act a) (ρ.act b)

end BaseChange

theorem exists_model (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]
    {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hO : U.OLinear O ιD ιA ιG)
    {S' : Scheme.{0}} (f : S' ⟶ Spec (CommRingCat.of R)) :
    ∃ (Gt : Over S') (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt O)
      (J : ∀ (T : Over S') (s : T.left ⟶ Spec (CommRingCat.of R)), s = T.hom ≫ f → IsAdicColimit I (Over.mk s) →
        ((T ⟶ Gt) ≃* (Over.mk s ⟶ G))),
      (GtBaseChange.extBC f (splitExt D.toPre)).IsGt Gt ∧
      (∀ T T' s s' hs hs' hT hT' (k : T' ⟶ T) (x : T ⟶ Gt),
        (J T' s' hs' hT' (k ≫ x)).left = k.left ≫ (J T s hs hT x).left) ∧
      ∀ T s hs hT (x : T ⟶ Gt) (a : O), J T s hs hT (x ≫ ρ.act a) = J T s hs hT x ≫ ιG.act a := by
  obtain ⟨H, _, _, hH⟩ := exists_isGt hG (splitExt D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hG hH
  obtain ⟨ρ, hρ⟩ := exists_ringAct hG ιD (Φ := Φ) hΦ
  obtain ⟨J, hJ⟩ := exists_mulEquiv U hG (Φ := Φ) hΦ
  choose π hπ using exists_pushEquiv f (H := H)
  obtain ⟨d⟩ := hH
  refine ⟨(Over.pullback f).obj H, inferInstance, inferInstance, actPull f ρ,
    fun T s hs hT => (π T s hs).trans (J _ hT), GtBaseChange.isGt_extBC f _ H d, ?_, ?_⟩
  · intro T T' s s' hs hs' hT hT' k x
    let k₀ : Over.mk s' ⟶ Over.mk s := Over.homMk k.left (by
      change k.left ≫ s = s'
      rw [hs, hs', Over.w_assoc])
    have e : π T' s' hs' (k ≫ x) = k₀ ≫ π T s hs x := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc]; rfl)
    have := (hJ _ hT' (k₀ ≫ π T s hs x) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).pull k₀ (hΦ.1 _ _ k₀ _))
    rw [← e] at this
    exact congrArg (·.left) this
  · intro T s hs hT x a
    have e : π T s hs (x ≫ (actPull f ρ).act a) = π T s hs x ≫ ρ.act a := Over.OverMorphism.ext (by
      rw [hπ, Over.comp_left, Over.comp_left, hπ, Category.assoc, Category.assoc]
      exact congrArg (x.left ≫ ·) (pullback.lift_fst _ _ _))
    have := (hJ _ hT (π T s hs x ≫ ρ.act a) _).2 (((hJ _ hT (π T s hs x) _).1 rfl).smul hG hO a (hρ a _ _))
    rw [← e] at this
    exact this

theorem isAdicColimit_of_pow {R A : Type} [CommRing R] [CommRing A] (I : Ideal R) (φ : R →+* A) (n : ℕ)
    (h : ∀ a ∈ I ^ n, φ a = 0) : IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  refine isAdicColimit_of_factor n (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift (I ^ (n + 1)) φ
    fun a ha => h a (Ideal.pow_le_pow_right (Nat.le_succ n) ha)))) ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  rfl

theorem isAdicColimit_of_finite_flat {R O : Type} [CommRing R] [CommRing O] [IsLocalRing O] (I : Ideal R)
    (f : R →+* O) (hO : IsAdicComplete (I.map f) O) (hm : ∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ I.map f)
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] :
    IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
  have := henselianLocalRing_of_le_radical (I.map f) hm
  refine isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing isAdicColimit_of_disjoint_cover
    R I O A _ ?_
  rw [← Ideal.map_map]
  exact GlobalTheory.FlatComplete.isAdicComplete_of_finite_flat O _ hO A

theorem main : Laws → Laws4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (O : Type) [CommRing O] [IsLocalRing O] (f : V →+* O), IsLocalHom f → IsAdicComplete ((maximalIdeal V).map f) O → (∀ a ∈ maximalIdeal O, ∃ n : ℕ, a ^ n ∈ (maximalIdeal V).map f) → ∃ (Ex : SplitExt (Spec (CommRingCat.of O))) (B : PolAV (Spec (CommRingCat.of O))) (_ : B.A = Ex.B) (_ : HEq B.grp Ex.grpB) (Gt : Over (Spec (CommRingCat.of O))) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (ρ : RingAct Gt (𝓞 E)) (J : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → (specO O A ⟶ Gt) → (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G)), Ex.IsGt Gt ∧ (∀ N : ℕ, 1 ≤ N → IsFinite (torsion Ex.B N).hom ∧ Flat (torsion Ex.B N).hom) ∧ (∀ (A A' : Type) [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A'] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)) (hA' : ((Module.Finite O A' ∧ Module.Free O A') ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A' (f a) = 0)) (φ : A →ₐ[O] A') (x : specO O A ⟶ Gt), (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left) ∧ ∀ (A : Type) [CommRing A] [Algebra O A] (hA : ((Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0)), (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧ (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ t.act.act a) ∧ Function.Injective (J A hA) ∧ ((∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) → Function.Surjective (J A hA)) ∧ ∀ (I : Ideal A) (g : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G), IsNilpotent I → Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g.left = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (1 : Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f))) ⟶ t.G).left → ∃ x, J A hA x = g := by
  intro hL _ E _ _ _ H V _ _ _ _ t P O _ _ f _ hO hm
  letI := H.starRing
  obtain ⟨Gt, _, _, ρ, J, h₁, h₂, h₃⟩ := exists_model hL.globalFns P.U.toUnifPre P.lin (spMap f)
  have hs : ∀ (A : Type) [CommRing A] [Algebra O A],
      Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)) = (specO O A).hom ≫ spMap f := fun A _ _ => by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]; rfl
  have hc : ∀ (A : Type) [CommRing A] [Algebra O A], ((Module.Finite O A ∧ Module.Free O A) ∨
      ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0) →
      IsAdicColimit (maximalIdeal V) (Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp f)))) := by
    rintro A _ _ (⟨_, _⟩ | ⟨n, hn⟩)
    exacts [isAdicColimit_of_finite_flat _ f hO hm A, isAdicColimit_of_pow _ _ n hn]
  refine ⟨GtBaseChange.extBC (spMap f) (splitExt P.D.toPre), polPull (spMap f) P.D.toPre.P, rfl, HEq.rfl,
    Gt, inferInstance, inferInstance, ρ, fun A _ _ hA => J (specO O A) _ (hs A) (hc A hA), h₁, fun N hN => ?_,
    fun A A' _ _ _ _ hA hA' φ x => h₂ _ _ _ _ _ _ _ _ (ptMap φ) x,
    fun A _ _ hA => ⟨map_mul _, h₃ _ _ _ _, MulEquiv.injective _, fun _ => MulEquiv.surjective _,
      fun _ g _ _ => MulEquiv.surjective _ g⟩⟩
  obtain ⟨a, b, -⟩ := hL.mulN _ P.D.toPre.P N hN
  exact torsion_pullback (spMap f) P.D.toPre.P.A N a b

end GlobalTheory.TorusModel
