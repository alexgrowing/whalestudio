import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.InvertibleSheaf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh

noncomputable section

universe u

section VectorBundle

variable {X : Scheme.{u}}

def IsFreeBasisOn (P : PMod X) (U : X.Opens) {n : ℕ} (s : Fin n → P.obj (op U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : Fin n → ringOn X V => ∑ i, r i • resM P h (s i))

def IsVectorBundle (E : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (s : Fin n → ((preMod X).obj E).obj (op U)), IsFreeBasisOn ((preMod X).obj E) U s

theorem isFreeBasisOn_of_isBasisOn {P : PMod X} {U : X.Opens} {s : P.obj (op U)}
    (hs : IsBasisOn P U s) : IsFreeBasisOn P U (fun _ : Fin 1 => s) := by
  intro V h
  have e : (fun r : Fin 1 → ringOn X V => ∑ i, r i • resM P h ((fun _ : Fin 1 => s) i)) =
      (fun c : ringOn X V => c • resM P h s) ∘ (fun r : Fin 1 → ringOn X V => r 0) := by
    funext r
    simp
  rw [e]
  exact (hs V h).comp (Equiv.funUnique (Fin 1) (ringOn X V)).bijective

theorem IsInvertibleSheaf.isVectorBundle {E : X.Modules} (hE : IsInvertibleSheaf E) :
    IsVectorBundle E := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hE x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  exact ⟨V, hV, hxV, 1, fun _ => resM _ (homOfLE hVU).le s,
    isFreeBasisOn_of_isBasisOn (hs.restrict _)⟩

theorem isVectorBundle_unit (X : Scheme.{u}) : IsVectorBundle (𝟙_ X.Modules) :=
  IsInvertibleSheaf.isVectorBundle isInvertibleSheaf_unit

end VectorBundle

section OverZ

def toSpecZ (X : Scheme.{0}) : X ⟶ Spec (.of ℤ) := specZIsTerminal.from X

theorem specZ_hom_ext {X : Scheme.{0}} (f g : X ⟶ Spec (.of ℤ)) : f = g :=
  specZIsTerminal.hom_ext f g

def IsFiniteTypeOverZ (X : Scheme.{0}) : Prop :=
  LocallyOfFiniteType (toSpecZ X) ∧ QuasiCompact (toSpecZ X)

def invOpen (X : Scheme.{0}) (m : ℕ) : X.Opens :=
  toSpecZ X ⁻¹ᵁ (PrimeSpectrum.basicOpen (m : ℤ) : (Spec (.of ℤ)).Opens)

theorem invOpen_one (X : Scheme.{0}) : invOpen X 1 = ⊤ := by
  simp only [invOpen, Nat.cast_one, PrimeSpectrum.basicOpen_one]
  rfl

theorem invOpen_mul (X : Scheme.{0}) (a b : ℕ) :
    invOpen X (a * b) = invOpen X a ⊓ invOpen X b := by
  simp only [invOpen, Nat.cast_mul, PrimeSpectrum.basicOpen_mul]
  rfl

instance (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)

abbrev ZLoc (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})

def zLocToRat (p : Nat.Primes) : ZLoc p →+* ℚ :=
  IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (g := algebraMap ℤ ℚ) (by
    rintro ⟨y, hy⟩
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    apply hy
    have : y = 0 := by simpa using h0
    rw [this]
    exact Ideal.zero_mem _)

def atP (X : Scheme.{0}) (p : Nat.Primes) : Scheme.{0} :=
  pullback (toSpecZ X) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZLoc p))))

def atPTo (X : Scheme.{0}) (p : Nat.Primes) : atP X p ⟶ X := pullback.fst _ _

def genFib (X : Scheme.{0}) : Scheme.{0} :=
  pullback (toSpecZ X) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))

def genTo (X : Scheme.{0}) : genFib X ⟶ X := pullback.fst _ _

def genToAtP (X : Scheme.{0}) (p : Nat.Primes) : genFib X ⟶ atP X p :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (CommRingCat.ofHom (zLocToRat p))) (𝟙 _)
    (specZ_hom_ext _ _) (specZ_hom_ext _ _)

theorem genToAtP_atPTo (X : Scheme.{0}) (p : Nat.Primes) :
    genToAtP X p ≫ atPTo X p = genTo X :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end OverZ

section Pullbacks

variable {A B C D : Scheme.{u}}

def pbSquare (q : A ⟶ B) (j : B ⟶ D) (k : A ⟶ C) (r : C ⟶ D) (h : q ≫ j = k ≫ r)
    (M : D.Modules) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback j).obj M) ≅
      (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback r).obj M) :=
  (Scheme.Modules.pullbackComp q j).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M ≪≫
    ((Scheme.Modules.pullbackComp k r).app M).symm

def pbSection (f : A ⟶ B) (M : B.Modules) (t : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤) t

end Pullbacks

section Generic

variable {X : Scheme.{u}} [IrreducibleSpace X]

structure GenericStalkIso (E E' : X.Modules) where

  toAddEquiv : E.presheaf.stalk (genericPoint X) ≃+ E'.presheaf.stalk (genericPoint X)

  map_smul_germ : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (r : Γ(X, U)) (s : Γ(E, U))
    (t : Γ(E', U)), toAddEquiv (E.presheaf.germ U _ hU s) = E'.presheaf.germ U _ hU t →
      toAddEquiv (E.presheaf.germ U _ hU (r • s)) = E'.presheaf.germ U _ hU (r • t)

def germImage (E : X.Modules) (x : X) : Set (E.presheaf.stalk (genericPoint X)) :=
  {v | ∃ (U : X.Opens) (_ : x ∈ U) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
    E.presheaf.germ U _ hU s = v}

end Generic

section Opens

def primeProd (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)

def genOpen (X : Scheme.{0}) (m : ℕ) : (genFib X).Opens := genTo X ⁻¹ᵁ invOpen X m

def genRes (X : Scheme.{0}) (m : ℕ) : (genOpen X m).toScheme ⟶ (invOpen X m).toScheme :=
  genTo X ∣_ invOpen X m

def atPOpen (X : Scheme.{0}) (p : Nat.Primes) (m : ℕ) : (atP X p).Opens :=
  atPTo X p ⁻¹ᵁ invOpen X m

def atPRes (X : Scheme.{0}) (p : Nat.Primes) (m : ℕ) :
    (atPOpen X p m).toScheme ⟶ (invOpen X m).toScheme :=
  atPTo X p ∣_ invOpen X m

def subOpen (X : Scheme.{0}) (a m' : ℕ) : (invOpen X a).toScheme.Opens :=
  (invOpen X a).ι ⁻¹ᵁ invOpen X (a * m')

def subRes (X : Scheme.{0}) (a m' : ℕ) :
    (genRes X a ⁻¹ᵁ subOpen X a m').toScheme ⟶ (subOpen X a m').toScheme :=
  genRes X a ∣_ subOpen X a m'

theorem subRes_square (X : Scheme.{0}) (a m' : ℕ) :
    subRes X a m' ≫ (subOpen X a m').ι = (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ genRes X a :=
  morphismRestrict_ι _ _

theorem glue_square (X : Scheme.{0}) (m : ℕ) (p : Nat.Primes) :
    genRes X m ≫ (invOpen X m).ι = ((genOpen X m).ι ≫ genToAtP X p) ≫ atPTo X p := by
  have h := morphismRestrict_ι (genTo X) (invOpen X m)
  rw [Category.assoc, genToAtP_atPTo]
  exact h

end Opens

section Generic

variable {X : Scheme.{u}} [IrreducibleSpace X]

theorem germ_smul_eq {E : X.Modules} {U : X.Opens} (hU : genericPoint X ∈ U) (r : Γ(X, U))
    {s t : Γ(E, U)} (h : E.presheaf.germ U _ hU s = E.presheaf.germ U _ hU t) :
    E.presheaf.germ U _ hU (r • s) = E.presheaf.germ U _ hU (r • t) := by
  obtain ⟨W, hW, i, j, hst⟩ := TopCat.Presheaf.germ_eq E.presheaf _ hU hU s t h
  rw [show j = i from Subsingleton.elim _ _] at hst
  rw [← E.presheaf.germ_res_apply i _ hW, ← E.presheaf.germ_res_apply i _ hW,
    Scheme.Modules.map_smul, Scheme.Modules.map_smul, hst]

def GenericStalkIso.refl (E : X.Modules) : GenericStalkIso E E where
  toAddEquiv := AddEquiv.refl _
  map_smul_germ _ hU r _ _ h := germ_smul_eq hU r h

end Generic

section Unit

variable {X Y : Scheme.{u}}

instance final_opensMap (f : X ⟶ Y) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

set_option backward.isDefEq.respectTransparency.types false in

theorem isIso_pullbackObjUnitToUnit (f : X ⟶ Y)
    [(SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _
      _).bijective.of_comp_iff', ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert! (SheafOfModules.bijective_pushforwardSections f.toRingCatSheafHom M).comp
    (SheafOfModules.unitHomEquiv _).bijective
  ext g : 1
  dsimp
  rw [SheafOfModules.pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (isIso_pullbackObjUnitToUnit f)

end Unit

section SchemeStatements

def BundlesAgree.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsNormalScheme X] [IsLocallyNoetherian X] (E E' : X.Modules),
    IsVectorBundle E → IsVectorBundle E' → ∀ φ : GenericStalkIso E E',
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      φ.toAddEquiv '' germImage E x = germImage E' x) →
    ∃! e : E ≅ E', ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      φ.toAddEquiv (E.presheaf.germ U _ hU s) =
        E'.presheaf.germ U _ hU (Scheme.Modules.Hom.app e.hom U s)

def SpreadBundle.Statement : Prop :=
  ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (p : Nat.Primes) (E : (atP X p).Modules),
    IsVectorBundle E → ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ m' : ℕ, m ∣ m' → ¬ (p : ℕ) ∣ m' →
      ∃ E' : (invOpen X m').toScheme.Modules, IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (atPRes X p m')).obj E' ≅
          (Scheme.Modules.pullback (atPOpen X p m').ι).obj E)

def SpreadIso.Statement : Prop :=
  ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (a : ℕ), 0 < a →
    ∀ (F G : (invOpen X a).toScheme.Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ ψ : (Scheme.Modules.pullback (genRes X a)).obj F ≅
      (Scheme.Modules.pullback (genRes X a)).obj G,
    ∃ m' : ℕ, 0 < m' ∧ ∃ f : (Scheme.Modules.pullback (subOpen X a m').ι).obj F ≅
        (Scheme.Modules.pullback (subOpen X a m').ι).obj G,
      (Scheme.Modules.pullback (subRes X a m')).map f.hom =
        (pbSquare _ _ _ _ (subRes_square X a m') F).hom ≫
          (Scheme.Modules.pullback (genRes X a ⁻¹ᵁ subOpen X a m').ι).map ψ.hom ≫
            (pbSquare _ _ _ _ (subRes_square X a m') G).inv

def PrimeOpensCover.Statement : Prop :=
  ∀ (X : Scheme.{0}) (S : Finset Nat.Primes) (mp : Nat.Primes → ℕ),
    (∀ p ∈ S, ¬ (p : ℕ) ∣ mp p) → (∀ p ∈ S, ∀ q ∈ S, q ≠ p → (q : ℕ) ∣ mp p) →
    ((invOpen X (primeProd S) ⊔ ⨆ p ∈ S, invOpen X (mp p)) = ⊤) ∧
    ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      invOpen X (mp p) ⊓ invOpen X (mp q) ≤ invOpen X (primeProd S) ∧
      invOpen X (mp p) ⊓ invOpen X (mp q) ≤ invOpen X (primeProd S * mp p)

structure GlueBundles.Data (X : Scheme.{0}) (S : Finset Nat.Primes) where

  E₀ : (invOpen X (primeProd S)).toScheme.Modules
  isVB₀ : IsVectorBundle E₀

  E : ∀ p : S, (atP X p).Modules
  isVB : ∀ p : S, IsVectorBundle (E p)

  γ : ∀ p : S, (Scheme.Modules.pullback ((genOpen X (primeProd S)).ι ≫ genToAtP X p)).obj (E p) ≅
    (Scheme.Modules.pullback (genRes X (primeProd S))).obj E₀

def GlueBundles.Statement : Prop :=
  ∀ (X : Scheme.{0}), IsFiniteTypeOverZ X → ∀ (S : Finset Nat.Primes) (D : GlueBundles.Data X S),
    ∃ E : X.Modules, IsVectorBundle E ∧
      ∃ (α : (Scheme.Modules.pullback (invOpen X (primeProd S)).ι).obj E ≅ D.E₀)
        (β : ∀ p : S, (Scheme.Modules.pullback (atPTo X p)).obj E ≅ D.E p),
        ∀ p : S, (pbSquare _ _ _ _ (glue_square X (primeProd S) p) E).hom ≫
            (Scheme.Modules.pullback ((genOpen X (primeProd S)).ι ≫ genToAtP X p)).map (β p).hom ≫
              (D.γ p).hom =
          (Scheme.Modules.pullback (genRes X (primeProd S))).map α.hom

def ClearDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X], Flat (toSpecZ X) →
    ∀ (L : X.Modules), IsVectorBundle L →
    ∀ s : Γ((Scheme.Modules.pullback (genTo X)).obj L, genTo X ⁻¹ᵁ ⊤),
    ∃ N : ℕ, 0 < N ∧ ∃ t : Γ(L, ⊤), pbSection (genTo X) L t = N • s

end SchemeStatements

section AlgebraStatements

def Dominates (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    (V : Subring K) : Prop :=
  ∃ h : ∀ a : A, algebraMap A K a ∈ V,
    ∀ a : A, (⟨_, h a⟩ : V) ∈ nonunits V ↔ a ∈ IsLocalRing.maximalIdeal A

def DominatingDVR.Statement : Prop :=
  (∀ (A K : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra A K] [IsFractionRing A K], ¬ IsField A →
      ∃ V : Subring K, IsDiscreteValuationRing V ∧ Dominates A V) ∧
  (∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z), z ≠ genericPoint Z →
      ∃ V : Subring Z.functionField, IsDiscreteValuationRing V ∧ Dominates (Z.presheaf.stalk z) V)

def blowUpChart (A K : Type*) [CommRing A] [Field K] [Algebra A K] {n : ℕ} (x : Fin n → A)
    (i : Fin n) : Subalgebra A K :=
  Algebra.adjoin A (Set.range fun j => algebraMap A K (x j) / algebraMap A K (x i))

def BlowUpChart.Statement : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] (n : ℕ) (x : Fin n → A),
    Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A → (∃ i, x i ≠ 0) →
    ∃ i, x i ≠ 0 ∧ ¬ IsUnit (algebraMap A (blowUpChart A K x i) (x i)) ∧
      ∀ P : Ideal (blowUpChart A K x i), P.IsPrime → algebraMap A _ (x i) ∈ P →
        P.comap (algebraMap A (blowUpChart A K x i)) = IsLocalRing.maximalIdeal A

def KrullAkizuki.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
    [IsScalarTower R K L], ringKrullDim R = 1 →
    (∀ S : Subalgebra R L, IsNoetherianRing S ∧ ringKrullDim S ≤ 1) ∧
      IsDedekindDomain (integralClosure R K)

def locIn (A K : Type*) [CommRing A] [Field K] [Algebra A K] (p : Ideal A) : Set K :=
  {y | ∃ a s : A, s ∉ p ∧ algebraMap A K s * y = algebraMap A K a}

def HeightOneIntersection.Statement : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K],
    Set.range (algebraMap A K) = ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p

def locSub {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V] (M : Submodule A V)
    (p : Ideal A) : Set V :=
  {v | ∃ s : A, s ∉ p ∧ s • v ∈ M}

def LatticesAgree.Statement : Prop :=
  ∀ (A K V : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module A V] [IsScalarTower A K V] (M N : Submodule A V),
    Module.Finite A M → Module.Projective A M → Module.Finite A N → Module.Projective A N →
    Submodule.span K (M : Set V) = ⊤ → Submodule.span K (N : Set V) = ⊤ →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → locSub M p = locSub N p) → M = N

def FiniteIntegralClosure.Statement : Prop :=
  (∀ (A K L : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L], Module.Finite A (integralClosure A L)) ∧
  (∀ (X : Scheme.{0}) [IsIntegral X], IsFiniteTypeOverZ X →
    ∀ (L : Type) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
      (U : X.Opens), IsAffineOpen U → ∀ hU : Nonempty U,
      letI : Algebra Γ(X, U) L :=
        ((algebraMap X.functionField L).comp (@algebraMap Γ(X, U) X.functionField _ _ (by
          haveI := hU; infer_instance))).toAlgebra
      Module.Finite Γ(X, U) (integralClosure Γ(X, U) L))

end AlgebraStatements

section NumberStatements

open GroundTheory.Heights₂.Heights.NumbersDVR in

def SectionNef.Statement : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (ι : κ → Type) [∀ k, Fintype (ι k)] (F : Type)
    [Field F] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ringKrullDim (MRing ι F ⧸ P) = ((1 + Fintype.card κ : ℕ) : WithBot ℕ∞) →
    ∀ a : κ → ℕ,
      ((∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ P) ∨
        (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W →
          ∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ W)) →
      0 ≤ intNum F P ![fun k => (a k : ℤ)]

def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (⌊B⌋₊ + 1)), Real.log p / p ≤ Real.log B + C

def cp (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def SumCp.Statement : Prop :=
  ∀ d : ℤ, d ≠ 0 → ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ B) →
    ∑ p ∈ S, (cp p + 2 * (padicValInt p d : ℝ)) * Real.log p ≤ C * Real.log B

end NumberStatements

section Inhabitants

abbrev specInt : Scheme.{0} := Spec (.of ℤ)

theorem toSpecZ_specInt : toSpecZ specInt = 𝟙 _ := specZ_hom_ext _ _

theorem isFiniteTypeOverZ_specInt : IsFiniteTypeOverZ specInt := by
  unfold IsFiniteTypeOverZ
  rw [toSpecZ_specInt]
  exact ⟨inferInstance, inferInstance⟩

theorem flat_toSpecZ_specInt : Flat (toSpecZ specInt) := by
  rw [toSpecZ_specInt]
  infer_instance

theorem isNormalScheme_specInt : IsNormalScheme specInt where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have : x.asIdeal.IsPrime := x.isPrime
    let k : Algebra ℤ (specInt.presheaf.stalk x) := StructureSheaf.stalkAlgebra ℤ x
    have : IsLocalization.AtPrime (specInt.presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk ℤ x
    exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
      x.asIdeal.primeCompl_le_nonZeroDivisors

def prime2 : Nat.Primes := ⟨2, Nat.prime_two⟩
def prime3 : Nat.Primes := ⟨3, Nat.prime_three⟩

def primePt (p : Nat.Primes) : PrimeSpectrum ℤ := ⟨Ideal.span {((p : ℕ) : ℤ)}, inferInstance⟩

def closedPt (p : Nat.Primes) : specInt := primePt p

theorem closedPt_two_ne_generic : closedPt prime2 ≠ genericPoint specInt := by
  intro h
  have hs : genericPoint specInt ⤳ closedPt prime3 := genericPoint_specializes _
  rw [← h] at hs
  have hle : primePt prime2 ≤ primePt prime3 :=
    (PrimeSpectrum.le_iff_specializes (primePt prime2) (primePt prime3)).mpr hs
  have h2 : ((2 : ℕ) : ℤ) ∈ Ideal.span {((3 : ℕ) : ℤ)} :=
    ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hle) (Ideal.subset_span rfl)
  rw [Ideal.mem_span_singleton] at h2
  norm_num at h2

theorem DominatingDVR.hyps :
    (IsDomain ℤ_[2] ∧ IsLocalRing ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ IsFractionRing ℤ_[2] ℚ_[2] ∧
      ¬ IsField ℤ_[2]) ∧
    (IsIntegral specInt ∧ IsLocallyNoetherian specInt ∧ closedPt prime2 ≠ genericPoint specInt) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.not_isField ℤ_[2]⟩,
    ⟨inferInstance, inferInstance, closedPt_two_ne_generic⟩⟩

theorem BlowUpChart.hyps :
    IsNoetherianRing ℤ_[2] ∧ IsFractionRing ℤ_[2] ℚ_[2] ∧
    Ideal.span (Set.range ![(2 : ℤ_[2])]) = IsLocalRing.maximalIdeal ℤ_[2] ∧
    ∃ i, ![(2 : ℤ_[2])] i ≠ 0 := by
  refine ⟨inferInstance, inferInstance, ?_, ⟨0, by simp⟩⟩
  rw [PadicInt.maximalIdeal_eq_span_p]
  simp

theorem KrullAkizuki.hyps :
    IsNoetherianRing ℤ ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ ∧
      ringKrullDim ℤ = 1 :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField⟩

theorem HeightOneIntersection.hyps :
    IsNoetherianRing ℤ ∧ IsIntegrallyClosed ℤ ∧ IsFractionRing ℤ ℚ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

abbrev intLattice : Submodule ℤ ℚ := Submodule.span ℤ {1}

theorem LatticesAgree.hyps :
    IsIntegrallyClosed ℤ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ ∧
    Module.Finite ℤ intLattice ∧ Module.Projective ℤ intLattice ∧
    Submodule.span ℚ (intLattice : Set ℚ) = ⊤ ∧
    (∀ p : Ideal ℤ, p.IsPrime → p.height = 1 → locSub intLattice p = locSub intLattice p) := by
  have : Module.Finite ℤ intLattice := inferInstance
  have : Module.Free ℤ intLattice := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    fun _ _ _ => rfl⟩
  rw [Submodule.span_span_of_tower]
  refine eq_top_iff.mpr fun y _ => ?_
  simpa only [smul_eq_mul, mul_one] using Submodule.smul_mem (Submodule.span ℚ {(1 : ℚ)}) y
    (Submodule.subset_span (Set.mem_singleton 1))

open GroundTheory.Heights₂.Heights.NumbersDVR MvPolynomial in

theorem SectionNef.hyps :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
    ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
      ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
    ((∃ s : MRing (fun _ : Unit => Fin 2) ℚ, IsMultiHomog s (fun _ => 1) ∧ s ∉ (⊥ : Ideal _)) ∨
      (∀ W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ), IsMultiProjPrime W → ⊥ ≤ W →
        ∃ s : MRing (fun _ : Unit => Fin 2) ℚ, IsMultiHomog s (fun _ => 1) ∧ s ∉ W)) := by
  refine ⟨isMultiProjPrime_bot, ?_, Or.inl ⟨X ⟨(), 0⟩, ?_, ?_⟩⟩
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField
        (Field.toIsField ℚ)]
    have hc : Nat.card ((_ : Unit) × Fin 2) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp
    rw [hc, Fintype.card_unit]
    rfl
  · have h := isWeightedHomogeneous_X ℚ (blockWeight (fun _ : Unit => Fin 2)) ⟨(), 0⟩
    have e : blockWeight (fun _ : Unit => Fin 2) ⟨(), 0⟩ = fun _ => 1 := by
      funext k
      simp [blockWeight]
    rw [e] at h
    exact h
  · rw [Ideal.mem_bot]
    exact X_ne_zero _

theorem SumCp.hyps : (1 : ℤ) ≠ 0 ∧ (2 : ℝ) ≤ 3 ∧ ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime ∧ (p : ℝ) ≤ 3 := by
  refine ⟨one_ne_zero, by norm_num, ?_⟩
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact ⟨Nat.prime_two, by norm_num⟩
  · exact ⟨Nat.prime_three, by norm_num⟩

theorem FiniteIntegralClosure.hyps :
    (Algebra.FiniteType ℤ ℤ ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ) ∧
    (IsIntegral specInt ∧ IsFiniteTypeOverZ specInt ∧
      FiniteDimensional specInt.functionField specInt.functionField ∧
      IsAffineOpen (⊤ : specInt.Opens) ∧ Nonempty (⊤ : specInt.Opens)) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    ⟨inferInstance, isFiniteTypeOverZ_specInt, inferInstance, isAffineOpen_top _,
      ⟨⟨closedPt prime2, trivial⟩⟩⟩⟩

theorem BundlesAgree.hyps :
    IsIntegral specInt ∧ IsNormalScheme specInt ∧ IsLocallyNoetherian specInt ∧
    IsVectorBundle (𝟙_ specInt.Modules) ∧
    ∀ x : specInt, ringKrullDim (specInt.presheaf.stalk x) = 1 →
      (GenericStalkIso.refl (𝟙_ specInt.Modules)).toAddEquiv '' germImage (𝟙_ specInt.Modules) x =
        germImage (𝟙_ specInt.Modules) x :=
  ⟨inferInstance, isNormalScheme_specInt, inferInstance, isVectorBundle_unit _,
    fun _ _ => Set.image_id _⟩

theorem SpreadBundle.hyps :
    IsFiniteTypeOverZ specInt ∧ IsVectorBundle (𝟙_ (atP specInt prime2).Modules) :=
  ⟨isFiniteTypeOverZ_specInt, isVectorBundle_unit _⟩

theorem SpreadIso.hyps :
    IsFiniteTypeOverZ specInt ∧ 0 < 2 ∧ IsVectorBundle (𝟙_ (invOpen specInt 2).toScheme.Modules) ∧
    Nonempty ((Scheme.Modules.pullback (genRes specInt 2)).obj (𝟙_ (invOpen specInt 2).toScheme.Modules) ≅
      (Scheme.Modules.pullback (genRes specInt 2)).obj (𝟙_ (invOpen specInt 2).toScheme.Modules)) :=
  ⟨isFiniteTypeOverZ_specInt, two_pos, isVectorBundle_unit _, ⟨Iso.refl _⟩⟩

theorem PrimeOpensCover.hyps :
    (∀ p ∈ ({prime2, prime3} : Finset Nat.Primes), ¬ (p : ℕ) ∣ 5 - (p : ℕ)) ∧
    (∀ p ∈ ({prime2, prime3} : Finset Nat.Primes), ∀ q ∈ ({prime2, prime3} : Finset Nat.Primes),
      q ≠ p → (q : ℕ) ∣ 5 - (p : ℕ)) := by
  have h23 : prime2 ≠ prime3 := by
    intro h
    have := congrArg Subtype.val h
    simp [prime2, prime3] at this
  constructor
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> simp [prime2, prime3]
  · intro p hp q hq hqp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hqp
    · simp [prime2, prime3]
    · simp [prime2, prime3]
    · exact absurd rfl hqp

def GlueBundles.dataSpecInt : GlueBundles.Data specInt {prime2} where
  E₀ := SheafOfModules.unit _
  isVB₀ := isVectorBundle_unit _
  E _ := SheafOfModules.unit _
  isVB _ := isVectorBundle_unit _
  γ _ := pullbackUnitIso _ ≪≫ (pullbackUnitIso _).symm

theorem GlueBundles.hyps : IsFiniteTypeOverZ specInt := isFiniteTypeOverZ_specInt

theorem ClearDenominators.hyps :
    CompactSpace specInt ∧ QuasiSeparatedSpace specInt ∧ Flat (toSpecZ specInt) ∧
      IsVectorBundle (𝟙_ specInt.Modules) :=
  ⟨inferInstance, inferInstance, flat_toSpecZ_specInt, isVectorBundle_unit _⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
