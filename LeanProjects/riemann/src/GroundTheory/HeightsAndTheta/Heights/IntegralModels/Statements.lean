import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

section VectorBundle

universe u

variable {X : Scheme.{u}}

def IsBasisOn (M : X.Modules) (U : X.Opens) {n : ℕ} (s : Fin n → Γ(M, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective
    (fun r : Fin n → Γ(X, V) => ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom (s i))

def IsVectorBundle (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (s : Fin n → Γ(M, U)), IsBasisOn M U s

variable (X) in

def structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

theorem isVectorBundle_structureModule : IsVectorBundle (structureModule X) := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨U, hU, hxU, 1, fun _ => (1 : Γ(X, U)), ?_⟩
  intro V h
  change Function.Bijective (fun r : Fin 1 → Γ(X, V) =>
    ∑ i, r i * (X.presheaf.map (homOfLE h).op).hom 1)
  simp only [map_one, mul_one, Fin.sum_univ_one]
  exact (Equiv.funUnique (Fin 1) Γ(X, V)).bijective

end VectorBundle

section OverZ

abbrev SpecZ : Scheme.{0} := Spec (CommRingCat.of ℤ)

variable {X : Scheme.{0}}

def invOpen (f : X ⟶ SpecZ) (m : ℤ) : X.Opens :=
  f ⁻¹ᵁ PrimeSpectrum.basicOpen (m : CommRingCat.of ℤ)

lemma mem_invOpen (f : X ⟶ SpecZ) (m : ℤ) (x : X) :
    x ∈ invOpen f m ↔ (m : ℤ) ∉ (f.base x).asIdeal := Iff.rfl

lemma invOpen_mul_le_left (f : X ⟶ SpecZ) (a b : ℤ) : invOpen f (a * b) ≤ invOpen f a := by
  intro x hx
  rw [mem_invOpen] at hx ⊢
  exact fun h => hx (Ideal.mul_mem_right _ _ h)

instance isPrime_span_prime (p : Nat.Primes) : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).2 (Nat.prime_iff_prime_int.mp p.2)

abbrev ZLoc (p : Nat.Primes) : Type := Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})

abbrev baseChange (f : X ⟶ SpecZ) (R : Type) [CommRing R] : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (Int.castRingHom R)))

abbrev baseChangeMap (f : X ⟶ SpecZ) (R : Type) [CommRing R] : baseChange f R ⟶ X :=
  pullback.fst _ _

lemma range_baseChangeMap_subset (f : X ⟶ SpecZ) (R : Type) [CommRing R] (m : ℤ)
    (hm : IsUnit (m : R)) :
    Set.range (baseChangeMap f R) ⊆ Set.range (invOpen f m).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (m : ℤ) ∉ (f.base ((pullback.fst _ _ : baseChange f R ⟶ X).base y)).asIdeal
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  intro hz
  have hz' : (m : R) ∈
      ((pullback.snd f (Spec.map (CommRingCat.ofHom (Int.castRingHom R)))).base y).asIdeal := hz
  exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ hz' hm)

def toInvOpen (f : X ⟶ SpecZ) (R : Type) [CommRing R] (m : ℤ) (hm : IsUnit (m : R)) :
    baseChange f R ⟶ (invOpen f m : Scheme.{0}) :=
  IsOpenImmersion.lift (invOpen f m).ι (baseChangeMap f R) (range_baseChangeMap_subset f R m hm)

@[reassoc (attr := simp)]
lemma toInvOpen_ι (f : X ⟶ SpecZ) (R : Type) [CommRing R] (m : ℤ)
    (hm : IsUnit (m : R)) : toInvOpen f R m hm ≫ (invOpen f m).ι = baseChangeMap f R :=
  IsOpenImmersion.lift_fac _ _ _

end OverZ

section Maps

variable {X : Scheme.{0}}

lemma isUnit_intCast_zLoc (p : Nat.Primes) (m : ℤ) (hm : ¬ ((p : ℕ) : ℤ) ∣ m) :
    IsUnit (m : ZLoc p) := by
  have := IsLocalization.map_units (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (ZLoc p)
    ⟨m, fun h => hm (Ideal.mem_span_singleton.mp h)⟩
  rwa [eq_intCast] at this

lemma isUnit_intCast_rat (m : ℤ) (hm : m ≠ 0) : IsUnit (m : ℚ) := by
  rw [isUnit_iff_ne_zero]
  exact_mod_cast hm

def zLocToRat (p : Nat.Primes) : ZLoc p →+* ℚ :=
  IsLocalization.lift (M := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl) (g := Int.castRingHom ℚ)
    (fun s => by
      have hs : (s : ℤ) ≠ 0 := fun h => s.2 (h ▸ Ideal.zero_mem _)
      simpa using hs)

def ratToLoc (f : X ⟶ SpecZ) (p : Nat.Primes) : baseChange f ℚ ⟶ baseChange f (ZLoc p) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (zLocToRat p))) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ : ℤ →+* ℚ => pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ))
      (RingHom.ext_int _ _))

@[reassoc (attr := simp)]
lemma ratToLoc_baseChangeMap (f : X ⟶ SpecZ) (p : Nat.Primes) :
    ratToLoc f p ≫ baseChangeMap f (ZLoc p) = baseChangeMap f ℚ :=
  pullback.lift_fst _ _ _

end Maps

section Pullback

universe u

variable {T Y Z : Scheme.{u}}

def pullbackCompIso {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k) {E : Z.Modules}
    {F : Y.Modules} (γ : (Scheme.Modules.pullback h).obj E ≅ F) :
    (Scheme.Modules.pullback k).obj E ≅ (Scheme.Modules.pullback g).obj F :=
  ((Scheme.Modules.pullbackCongr e).app E).symm ≪≫ ((Scheme.Modules.pullbackComp g h).app E).symm ≪≫
    (Scheme.Modules.pullback g).mapIso γ

def pullSection (c : T ⟶ Z) (L : Z.Modules) :
    Γ(L, ⊤) →+ Γ((Scheme.Modules.pullback c).obj L, c ⁻¹ᵁ ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤).hom

end Pullback

section Normal

universe u

def IsNormalScheme (X : Scheme.{u}) : Prop := ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

instance stalkModule {X : Scheme.{u}} (E : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (E.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) E.val x

def genericImage {X : Scheme.{u}} [IrreducibleSpace X] (E : X.Modules) (x : X) :
    AddSubgroup (E.presheaf.stalk (genericPoint X)) :=
  (E.presheaf.stalkSpecializes (genericPoint_specializes x)).hom.range

end Normal

section Localised

variable {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]

def localizedIn (p : Ideal A) [p.IsPrime] (M : Submodule A V) : Submodule A V where
  carrier := {v | ∃ s : A, s ∉ p ∧ s • v ∈ M}
  add_mem' := by
    rintro v w ⟨s, hs, hsv⟩ ⟨t, ht, htw⟩
    refine ⟨s * t, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim hs ht, ?_⟩
    rw [smul_add]
    exact M.add_mem (by rw [mul_comm, mul_smul]; exact M.smul_mem t hsv)
      (by rw [mul_smul]; exact M.smul_mem s htw)
  zero_mem' := ⟨1, fun h => (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩
  smul_mem' := by
    rintro a v ⟨s, hs, hsv⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem a hsv⟩

end Localised

section More

variable {X : Scheme.{0}}

@[reassoc (attr := simp)]
lemma toInvOpen_homOfLE (f : X ⟶ SpecZ) (R : Type) [CommRing R] {m m' : ℤ} (hm : IsUnit (m : R))
    (hm' : IsUnit (m' : R)) (h : invOpen f m ≤ invOpen f m') :
    toInvOpen f R m hm ≫ X.homOfLE h = toInvOpen f R m' hm' := by
  rw [← cancel_mono (invOpen f m').ι]
  simp [Scheme.homOfLE_ι]

def pullbackIsoAlong {T Y Z : Scheme.{0}} {g : T ⟶ Y} {h : Y ⟶ Z} {k : T ⟶ Z} (e : g ≫ h = k)
    {F G : Z.Modules} (ψ : (Scheme.Modules.pullback h).obj F ≅ (Scheme.Modules.pullback h).obj G) :
    (Scheme.Modules.pullback k).obj F ≅ (Scheme.Modules.pullback k).obj G :=
  pullbackCompIso e (Iso.refl _) ≪≫ (Scheme.Modules.pullback g).mapIso ψ ≪≫
    (pullbackCompIso e (Iso.refl _)).symm

def primeProd (S : Finset Nat.Primes) : ℤ := ∏ p ∈ S, ((p : ℕ) : ℤ)

lemma primeProd_ne_zero (S : Finset Nat.Primes) : primeProd S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => by exact_mod_cast p.2.ne_zero

def Dominates (A : Type*) [CommRing A] [IsLocalRing A] {K : Type*} [Field K] [Algebra A K]
    (V : Subring K) : Prop :=
  ∃ hA : ∀ a : A, algebraMap A K a ∈ V,
    ∀ a : A, ¬ IsUnit (⟨algebraMap A K a, hA a⟩ : V) ↔ a ∈ IsLocalRing.maximalIdeal A

def blowUpChart {A : Type*} [CommRing A] (K : Type*) [Field K] [Algebra A K] {n : ℕ}
    (x : Fin n → A) (i : Fin n) : Subalgebra A K :=
  Algebra.adjoin A (Set.range fun j => algebraMap A K (x j) / algebraMap A K (x i))

def primeWeight (p : ℕ) : ℝ := if p = 2 then 2 else 1 / ((p : ℝ) - 1)

def genericSpecMap (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] : Spec (CommRingCat.of L) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)) ≫ Z.fromSpecStalk (genericPoint Z)

end More

open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo

structure IsRegularSection {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) (b : K → ℤ) (f g : MRing ι F) : Prop where
  degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  regular : ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W →
    ∃ u v : MRing ι F, u ∉ W ∧ u * f - v * g ∈ P

theorem isRegularSection_form {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    {P : Ideal (MRing ι F)} (hP : P.IsPrime) {a : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsRegularSection P (fun k => (a k : ℤ)) s 1 where
  degrees := ⟨a, 0, hs, MvPolynomial.isWeightedHomogeneous_one _ _, by funext k; simp⟩
  num_not_mem := hsP
  den_not_mem := fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h)
  regular := fun W hW _ => ⟨1, s, fun h => hW.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩

def SameRationalSpan {E : Type*} [AddCommGroup E] (L L' : AddSubgroup E) : Prop :=
  (∀ v ∈ L, ∃ N : ℕ, 0 < N ∧ N • v ∈ L') ∧ ∀ v ∈ L', ∃ N : ℕ, 0 < N ∧ N • v ∈ L

def DominatingDVR.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A], ¬ IsField A →
    ∀ (K : Type) [Field K] [Algebra A K] [IsFractionRing A K],
      ∃ V : Subring K, IsDiscreteValuationRing V ∧ Dominates A V

def DominatingDVRScheme.Statement : Prop :=
  ∀ (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (z : Z), z ≠ genericPoint Z →
    ∃ V : Subring Z.functionField, IsDiscreteValuationRing V ∧ Dominates (Z.presheaf.stalk z) V

def BlowUpChart.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (n : ℕ) (x : Fin n → A),
    Ideal.span (Set.range x) = IsLocalRing.maximalIdeal A → (∃ j, x j ≠ 0) →
      ∃ i, x i ≠ 0 ∧ ¬ IsUnit (algebraMap A (blowUpChart K x i) (x i)) ∧
        ∃ Q : Ideal (blowUpChart K x i), Q.IsPrime ∧ algebraMap A _ (x i) ∈ Q ∧
          Q.comap (algebraMap A (blowUpChart K x i)) = IsLocalRing.maximalIdeal A

def KrullAkizuki.Statement : Prop :=
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra R L]
      [IsScalarTower R K L] (S : Subalgebra R L), IsNoetherianRing S ∧ ringKrullDim S ≤ 1) ∧
  (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R], ringKrullDim R = 1 →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K],
      IsDedekindDomain (integralClosure R K))

def HeightOneIntersection.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K],
    Subalgebra.toSubmodule (⊥ : Subalgebra A K) =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        localizedIn p.asIdeal (Subalgebra.toSubmodule (⊥ : Subalgebra A K))

def LatticesAgree.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module A V]
    [IsScalarTower A K V] (M N : Submodule A V),
    Module.Finite A M → Module.Projective A M → Module.Finite A N → Module.Projective A N →
    Submodule.span K (M : Set V) = ⊤ → Submodule.span K (N : Set V) = ⊤ →
    (∀ p : PrimeSpectrum A, p.asIdeal.height = 1 → localizedIn p.asIdeal M = localizedIn p.asIdeal N) →
    M = N

def BundlesAgree.Statement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], IsNormalScheme X →
    ∀ (E E' : X.Modules), IsVectorBundle E → IsVectorBundle E' →
    ∀ φ : E.presheaf.stalk (genericPoint X) ≃ₗ[X.presheaf.stalk (genericPoint X)]
      E'.presheaf.stalk (genericPoint X),
    (∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
      (genericImage E x).map φ.toAddMonoidHom = genericImage E' x) →
    ∃! ψ : E ≅ E', ∀ v, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
      (Scheme.Modules.Hom.mapPresheaf ψ.hom)).hom v = φ v

def SpreadBundle.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules), IsVectorBundle E →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, m ∣ n → ∀ hn : ¬ ((p : ℕ) : ℤ) ∣ (n : ℤ),
      ∃ E' : (invOpen f n : Scheme.{0}).Modules, IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toInvOpen f (ZLoc p) n
          (isUnit_intCast_zLoc p n hn))).obj E' ≅ E)

def SpreadIso.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ α : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ (m' : ℕ) (hm' : 0 < m') (ψ : (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a m'))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a m'))).obj G),
      pullbackIsoAlong (toInvOpen_homOfLE f ℚ
        (isUnit_intCast_rat ((a : ℤ) * m') (by positivity))
        (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) (invOpen_mul_le_left f a m')) ψ = α

def PrimeOpensCover.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (S : Finset Nat.Primes) (mp : Nat.Primes → ℤ),
    (∀ p ∈ S, ¬ ((p : ℕ) : ℤ) ∣ mp p) → (∀ p ∈ S, ∀ q ∈ S, q ≠ p → ((q : ℕ) : ℤ) ∣ mp p) →
    (invOpen f (primeProd S) ⊔ ⨆ p ∈ S, invOpen f (mp p) = ⊤) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
        invOpen f (mp p) ⊓ invOpen f (mp q) ≤ invOpen f (primeProd S) ∧
        invOpen f (mp p) ⊓ invOpen f (mp q) ≤ invOpen f (primeProd S * mp p)

def GlueBundles.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (S : Finset Nat.Primes) (E₀ : (invOpen f (primeProd S) : Scheme.{0}).Modules)
    (Ep : ∀ p : S, (baseChange f (ZLoc p)).Modules),
    IsVectorBundle E₀ → (∀ p, IsVectorBundle (Ep p)) →
    ∀ β : ∀ p : S, (Scheme.Modules.pullback (ratToLoc f p)).obj (Ep p) ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ (primeProd S)
        (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj E₀,
    ∃ E : X.Modules, IsVectorBundle E ∧
      ∃ (γ₀ : (Scheme.Modules.pullback (invOpen f (primeProd S)).ι).obj E ≅ E₀)
        (γ : ∀ p : S, (Scheme.Modules.pullback (baseChangeMap f (ZLoc p))).obj E ≅ Ep p),
        ∀ p : S, pullbackCompIso (toInvOpen_ι f ℚ (primeProd S)
            (isUnit_intCast_rat _ (primeProd_ne_zero S))) γ₀ =
          pullbackCompIso (ratToLoc_baseChangeMap f p) (γ p) ≪≫ β p

def ChartGlue.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (τ : Type) [Finite τ] (x : τ → Ω) (r : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (S : Finset Nat.Primes)
    (o₀ : Type) [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    (o : S → Type) [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E),
    (∀ p i, x i ≠ 0 → SameRationalSpan (B₀.lat i) ((Bp p).lat i)) →
    ∃ B : ChartBundle ℤ x r E, ∀ i, x i ≠ 0 →
      (∀ v, v ∈ B₀.lat i ↔ ∃ n : ℕ, primeProd S ^ n • v ∈ B.lat i) ∧
      ∀ (p : S) (v : E), v ∈ (Bp p).lat i ↔
        ∃ s : ℤ, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s ∧ s • v ∈ B.lat i

def ChartBundlesAgree.Statement : Prop :=
  ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (τ : Type) (x : τ → Ω) (r : ℕ)
    (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ), x i ≠ 0 →
    IsNoetherianRing (chartRing o x i) → IsIntegrallyClosed (chartRing o x i) →
    (∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i) →
    (∀ v ∈ B'.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B.lat i) →
    (∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) ↔
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) →
    B.lat i = B'.lat i

def ClearDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [Flat f] [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules), IsVectorBundle L →
    ∀ s : Γ((Scheme.Modules.pullback (baseChangeMap f ℚ)).obj L, baseChangeMap f ℚ ⁻¹ᵁ ⊤),
      ∃ N : ℕ, 0 < N ∧ ∃ t : Γ(L, ⊤), pullSection (baseChangeMap f ℚ) L t = N • s

def SectionNef.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (F : Type) [Field F] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ringKrullDim (MRing ι F ⧸ P) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b : K → ℤ) (f g : MRing ι F), IsRegularSection P b f g → 0 ≤ intNum F P ![b]

def SectionNefGenerated.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (F : Type) [Field F] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ringKrullDim (MRing ι F ⧸ P) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ b : K → ℤ, (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → P ≤ W →
      ∃ f g : MRing ι F, IsRegularSection P b f g ∧
        ∃ u v : MRing ι F, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) →
      0 ≤ intNum F P ![b]

theorem SectionNefGenerated.of_sectionNef (h : SectionNef.Statement) :
    SectionNefGenerated.Statement := by
  intro K _ _ ι _ F _ P hP hd b hb
  obtain ⟨f, g, hs, -⟩ := hb P hP le_rfl
  exact h K ι F P hP hd b f g hs

def MertensUpper.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B →
    ∑ p ∈ (Finset.Iic ⌊B⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log B + C

def SumCp.Statement : Prop :=
  ∀ d : ℤ, d ≠ 0 → ∃ C : ℝ, ∀ B : ℝ, 2 ≤ B → ∀ S : Finset ℕ,
    (∀ p ∈ S, p.Prime ∧ ((p : ℝ) ≤ B ∨ (p : ℤ) ∣ d)) →
    ∑ p ∈ S, (primeWeight p + 2 * padicValInt p d) * Real.log p ≤ C * Real.log B

def FiniteIntegralClosure.Statement : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L],
    Module.Finite A (integralClosure A L)

def FiniteNormalization.Statement : Prop :=
  ∀ (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Type) [Field L] [Algebra Z.functionField L] [FiniteDimensional Z.functionField L],
    IsFinite (genericSpecMap Z L).fromNormalization

section Transport

universe u

variable {X Y : Scheme.{u}}

lemma app_map_apply {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ≤ U) (x : Γ(M, U)) :
    (φ.app V).hom ((M.presheaf.map (homOfLE i).op).hom x) =
      (N.presheaf.map (homOfLE i).op).hom ((φ.app U).hom x) := by
  have := congr(($(φ.mapPresheaf.naturality (homOfLE i).op)).hom x)
  simpa using this

theorem IsBasisOn.of_iso {M N : X.Modules} (e : M ≅ N) {U : X.Opens} {n : ℕ}
    {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) :
    IsBasisOn N U (fun i => (e.hom.app U).hom (s i)) := by
  intro V h
  have key : (fun r : Fin n → Γ(X, V) =>
      ∑ i, r i • (N.presheaf.map (homOfLE h).op).hom ((e.hom.app U).hom (s i))) =
      (e.hom.app V).hom ∘ (fun r => ∑ i, r i • (M.presheaf.map (homOfLE h).op).hom (s i)) := by
    funext r
    simp only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, app_map_apply]
  rw [key]
  have : IsIso (e.hom.app V) := inferInstance
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app V)).comp (hs V h)

theorem IsVectorBundle.of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsVectorBundle M) :
    IsVectorBundle N := by
  intro x
  obtain ⟨U, hU, hx, n, s, hs⟩ := hM x
  exact ⟨U, hU, hx, n, _, hs.of_iso e⟩

instance final_opensMap (f : X ⟶ Y) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

set_option backward.isDefEq.respectTransparency.types false in

def pullbackStructureIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (structureModule Y) ≅ structureModule X :=
  haveI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)

end Transport

section Inhabitants

theorem DominatingDVR.hypotheses_inhabited :
    IsDomain ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ IsLocalRing ℤ_[2] ∧ ¬ IsField ℤ_[2] ∧
      IsFractionRing ℤ_[2] ℚ_[2] :=
  ⟨inferInstance, inferInstance, inferInstance, IsDiscreteValuationRing.not_isField _,
    inferInstance⟩

theorem DominatingDVRScheme.hypotheses_inhabited :
    IsIntegral SpecZ ∧ IsLocallyNoetherian SpecZ ∧ ∃ z : SpecZ, z ≠ genericPoint SpecZ := by
  refine ⟨inferInstance, inferInstance, ⟨⟨Ideal.span {(2 : ℤ)}, isPrime_span_prime ⟨2, Nat.prime_two⟩⟩, ?_⟩⟩
  rw [genericPoint_eq_bot_of_affine]
  intro h
  have := congrArg PrimeSpectrum.asIdeal h
  simp only [PrimeSpectrum.asIdeal_bot, Ideal.span_singleton_eq_bot] at this
  norm_num at this

theorem BlowUpChart.hypotheses_inhabited :
    Ideal.span (Set.range ![(2 : ℤ_[2])]) = IsLocalRing.maximalIdeal ℤ_[2] ∧
      ∃ j, ![(2 : ℤ_[2])] j ≠ 0 := by
  refine ⟨?_, ⟨0, by simp⟩⟩
  rw [PadicInt.maximalIdeal_eq_span_p]
  simp

theorem KrullAkizuki.hypotheses_inhabited :
    IsNoetherianRing ℤ ∧ ringKrullDim ℤ = 1 ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧
      IsScalarTower ℤ ℚ ℚ :=
  ⟨inferInstance, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, inferInstance,
    inferInstance, inferInstance⟩

theorem HeightOneIntersection.hypotheses_inhabited :
    IsNoetherianRing ℤ ∧ IsIntegrallyClosed ℤ ∧ IsFractionRing ℤ ℚ :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem LatticesAgree.hypotheses_inhabited :
    Module.Finite ℤ (Submodule.span ℤ {(1 : ℚ)}) ∧
      Module.Projective ℤ (Submodule.span ℤ {(1 : ℚ)}) ∧
      Submodule.span ℚ ((Submodule.span ℤ {(1 : ℚ)} : Submodule ℤ ℚ) : Set ℚ) = ⊤ := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [eq_top_iff]
  intro v _
  have h1 : (1 : ℚ) ∈ Submodule.span ℚ ((Submodule.span ℤ {(1 : ℚ)} : Submodule ℤ ℚ) : Set ℚ) :=
    Submodule.subset_span (Submodule.subset_span rfl)
  have h2 := Submodule.smul_mem _ v h1
  rwa [smul_eq_mul, mul_one] at h2

theorem isNormalScheme_specZ : IsNormalScheme SpecZ := by
  intro x
  have hx : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let _ : Algebra ℤ (SpecZ.presheaf.stalk x) := StructureSheaf.stalkAlgebra (CommRingCat.of ℤ) x
  have : IsLocalization.AtPrime (SpecZ.presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of ℤ) x
  exact isIntegrallyClosed_of_isLocalization _ x.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

theorem BundlesAgree.hypotheses_inhabited :
    IsIntegral SpecZ ∧ IsLocallyNoetherian SpecZ ∧ IsNormalScheme SpecZ ∧
      IsVectorBundle (structureModule SpecZ) ∧
      ∀ x : SpecZ, ringKrullDim (SpecZ.presheaf.stalk x) = 1 →
        (genericImage (structureModule SpecZ) x).map
          (LinearEquiv.refl (SpecZ.presheaf.stalk (genericPoint SpecZ))
            ((structureModule SpecZ).presheaf.stalk (genericPoint SpecZ))).toAddMonoidHom =
          genericImage (structureModule SpecZ) x :=
  ⟨inferInstance, inferInstance, isNormalScheme_specZ, isVectorBundle_structureModule,
    fun _ _ => AddSubgroup.map_id _⟩

theorem SpreadBundle.hypotheses_inhabited :
    IsVectorBundle (structureModule (baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩))) :=
  isVectorBundle_structureModule

theorem SpreadIso.hypotheses_inhabited :
    IsVectorBundle (structureModule (invOpen (𝟙 SpecZ) (1 : ℕ) : Scheme.{0})) ∧
      Nonempty ((Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (1 : ℕ)
        (isUnit_intCast_rat 1 one_ne_zero))).obj (structureModule _) ≅
        (Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (1 : ℕ)
        (isUnit_intCast_rat 1 one_ne_zero))).obj (structureModule _)) :=
  ⟨isVectorBundle_structureModule, ⟨Iso.refl _⟩⟩

theorem PrimeOpensCover.hypotheses_inhabited :
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      ¬ ((p : ℕ) : ℤ) ∣ (if (p : ℕ) = 2 then 3 else 2)) ∧
    (∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      ∀ q ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes), q ≠ p →
        ((q : ℕ) : ℤ) ∣ (if (p : ℕ) = 2 then 3 else 2)) := by
  have mem : ∀ p ∈ ({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes),
      (p : ℕ) = 2 ∨ (p : ℕ) = 3 := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Or.inl rfl
    · rw [Finset.mem_singleton.mp hp]
      exact Or.inr rfl
  refine ⟨fun p hp => ?_, fun p hp q hq hne => ?_⟩
  · rcases mem p hp with h | h <;> rw [h] <;> norm_num
  · have hne' : (q : ℕ) ≠ p := fun h => hne (Subtype.ext h)
    rcases mem p hp with h | h <;> rcases mem q hq with h' | h'
    · exact absurd (h'.trans h.symm) hne'
    · rw [h, h']
      norm_num
    · rw [h, h']
      norm_num
    · exact absurd (h'.trans h.symm) hne'

theorem GlueBundles.hypotheses_inhabited :
    let S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
    IsVectorBundle (structureModule (invOpen (𝟙 SpecZ) (primeProd S) : Scheme.{0})) ∧
      (∀ p : S, IsVectorBundle (structureModule (baseChange (𝟙 SpecZ) (ZLoc p)))) ∧
      ∀ p : S, Nonempty ((Scheme.Modules.pullback (ratToLoc (𝟙 SpecZ) p)).obj
        (structureModule (baseChange (𝟙 SpecZ) (ZLoc p))) ≅
        (Scheme.Modules.pullback (toInvOpen (𝟙 SpecZ) ℚ (primeProd S)
          (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj (structureModule _)) :=
  ⟨isVectorBundle_structureModule, fun _ => isVectorBundle_structureModule,
    fun _ => ⟨pullbackStructureIso _ ≪≫ (pullbackStructureIso _).symm⟩⟩

theorem ClearDenominators.hypotheses_inhabited :
    Flat (𝟙 SpecZ) ∧ CompactSpace SpecZ ∧ QuasiSeparatedSpace SpecZ ∧
      IsVectorBundle (structureModule SpecZ) :=
  ⟨inferInstance, inferInstance, inferInstance, isVectorBundle_structureModule⟩

lemma projectiveLine_dim :
    ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
      ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MRing (fun _ : Unit => Fin 2) ℚ)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field ℚ]
  have hc : Nat.card ((_ : Unit) × Fin 2) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hc, Fintype.card_unit]
  norm_num

lemma isMultiHomog_X_zero :
    IsMultiHomog (MvPolynomial.X ⟨(), 0⟩ : MRing (fun _ : Unit => Fin 2) ℚ) (fun _ => 1) := by
  have := MvPolynomial.isWeightedHomogeneous_X ℚ (blockWeight (fun _ : Unit => Fin 2)) ⟨(), 0⟩
  have h : blockWeight (fun _ : Unit => Fin 2) ⟨(), 0⟩ = fun _ => 1 := by
    funext k
    simp [blockWeight]
  unfold IsMultiHomog
  rw [← h]
  exact this

theorem SectionNef.hypotheses_inhabited :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
      ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
        ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
      IsRegularSection (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) (fun _ => ((1 : ℕ) : ℤ))
        (MvPolynomial.X ⟨(), 0⟩) 1 := by
  refine ⟨isMultiProjPrime_bot, projectiveLine_dim, isRegularSection_form Ideal.isPrime_bot
    isMultiHomog_X_zero ?_⟩
  rw [Ideal.mem_bot]
  exact MvPolynomial.X_ne_zero _

theorem SectionNefGenerated.hypotheses_inhabited :
    IsMultiProjPrime (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) ∧
      ringKrullDim (MRing (fun _ : Unit => Fin 2) ℚ ⧸ (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ))) =
        ((1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
      ∀ W : Ideal (MRing (fun _ : Unit => Fin 2) ℚ), IsMultiProjPrime W → ⊥ ≤ W →
        ∃ f g : MRing (fun _ : Unit => Fin 2) ℚ,
          IsRegularSection (⊥ : Ideal (MRing (fun _ : Unit => Fin 2) ℚ)) (fun _ => ((1 : ℕ) : ℤ)) f g ∧
          ∃ u v : MRing (fun _ : Unit => Fin 2) ℚ, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ (⊥ : Ideal _) := by
  refine ⟨isMultiProjPrime_bot, projectiveLine_dim, fun W hW _ => ?_⟩
  obtain ⟨i, hi⟩ := hW.relevant ()
  have hdeg : IsMultiHomog (MvPolynomial.X ⟨(), i⟩ : MRing (fun _ : Unit => Fin 2) ℚ) (fun _ => 1) := by
    have := MvPolynomial.isWeightedHomogeneous_X ℚ (blockWeight (fun _ : Unit => Fin 2)) ⟨(), i⟩
    have h : blockWeight (fun _ : Unit => Fin 2) ⟨(), i⟩ = fun _ => 1 := by
      funext k
      simp [blockWeight]
    unfold IsMultiHomog
    rw [← h]
    exact this
  refine ⟨MvPolynomial.X ⟨(), i⟩, 1, isRegularSection_form Ideal.isPrime_bot hdeg ?_, 1,
    MvPolynomial.X ⟨(), i⟩, fun h => hW.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), hi, ?_⟩
  · rw [Ideal.mem_bot]
    exact MvPolynomial.X_ne_zero _
  · simp

theorem MertensUpper.hypotheses_inhabited : (2 : ℝ) ≤ 2 := le_rfl

theorem SumCp.hypotheses_inhabited :
    (6 : ℤ) ≠ 0 ∧ (2 : ℝ) ≤ 2 ∧
      ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime ∧ ((p : ℝ) ≤ 2 ∨ (p : ℤ) ∣ 6) := by
  refine ⟨by norm_num, le_rfl, ?_⟩
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact ⟨Nat.prime_two, Or.inl (by norm_num)⟩
  · rw [Finset.mem_singleton.mp hp]
    exact ⟨Nat.prime_three, Or.inr (by norm_num)⟩

theorem FiniteIntegralClosure.hypotheses_inhabited :
    IsDomain ℤ ∧ Algebra.FiniteType ℤ ℤ ∧ IsFractionRing ℤ ℚ ∧
      FiniteDimensional ℚ (CyclotomicField 3 ℚ) ∧ IsScalarTower ℤ ℚ (CyclotomicField 3 ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem FiniteNormalization.hypotheses_inhabited :
    IsIntegral SpecZ ∧ LocallyOfFiniteType (𝟙 SpecZ) ∧ QuasiCompact (𝟙 SpecZ) ∧
      FiniteDimensional SpecZ.functionField SpecZ.functionField :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

abbrev onePoint : Unit → ℚ := fun _ => 1

lemma chartRing_onePoint (o : Type) [CommRing o] [Algebra o ℚ] :
    chartRing o onePoint () = ⊥ := by
  have h : Set.range (fun j : Unit => onePoint j / onePoint ()) = {1} := by
    ext y
    simp [onePoint, eq_comm]
  rw [chartRing, h]
  exact Algebra.adjoin_singleton_one _ _

lemma chartRing_onePoint_normal :
    IsNoetherianRing (chartRing ℤ onePoint ()) ∧ IsIntegrallyClosed (chartRing ℤ onePoint ()) := by
  have e : ℤ ≃+* chartRing ℤ onePoint () :=
    (Algebra.botEquivOfInjective (R := ℤ) (A := ℚ) Int.cast_injective).symm.toRingEquiv.trans
      (Subalgebra.equivOfEq _ _ (chartRing_onePoint ℤ).symm).toRingEquiv
  exact ⟨isNoetherianRing_of_ringEquiv ℤ e, (IsIntegrallyClosed.of_equiv e)⟩

theorem ChartBundlesAgree.hypotheses_inhabited :
    IsNoetherianRing (chartRing ℤ onePoint ()) ∧ IsIntegrallyClosed (chartRing ℤ onePoint ()) ∧
      ∀ v ∈ (scaledTrivBundle ℤ onePoint 1 (one_ne_zero (α := ℚ))).lat (),
        ∃ s : chartRing ℤ onePoint (), s ≠ 0 ∧
          (s : ℚ) • v ∈ (scaledTrivBundle ℤ onePoint 1 (one_ne_zero (α := ℚ))).lat () :=
  ⟨chartRing_onePoint_normal.1, chartRing_onePoint_normal.2,
    fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩

lemma sameRationalSpan_onePoint (o o' : Type) [CommRing o] [CommRing o'] [Algebra o ℚ] [Algebra o' ℚ]
    (h : ∀ a : o, ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o ℚ a = z)
    (h' : ∀ a : o', ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o' ℚ a = z) :
    SameRationalSpan ((scaledTrivBundle o onePoint 1 (one_ne_zero (α := ℚ))).lat ())
      ((scaledTrivBundle o' onePoint 1 (one_ne_zero (α := ℚ))).lat ()) := by
  have key : ∀ (o o' : Type) [CommRing o] [CommRing o'] [Algebra o ℚ] [Algebra o' ℚ],
      (∀ a : o, ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * algebraMap o ℚ a = z) →
      ∀ v ∈ (scaledTrivBundle o onePoint 1 (one_ne_zero (α := ℚ))).lat (), ∃ N : ℕ, 0 < N ∧
        N • v ∈ (scaledTrivBundle o' onePoint 1 (one_ne_zero (α := ℚ))).lat () := by
    intro o o' _ _ _ _ h v hv
    have hv' : v ∈ scaledTrivLat o onePoint 1 1 () := hv
    obtain ⟨a, ha, hva⟩ := mem_scaledTrivLat.1 hv' 0
    rw [chartRing_onePoint o] at ha
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 ha
    obtain ⟨N, hN, z, hz⟩ := h c
    refine ⟨N, hN, (mem_scaledTrivLat (R := o')).2 fun q => ⟨(z : ℚ), ?_, ?_⟩⟩
    · exact intCast_mem _ z
    · have hq : q = 0 := Subsingleton.elim _ _
      subst hq
      simp only [Pi.smul_apply, hva, one_mul, nsmul_eq_mul, hz]
  exact ⟨key o o' h, key o' o h'⟩

def awayToRat (m : ℤ) (hm : m ≠ 0) : Localization.Away m →+* ℚ :=
  IsLocalization.Away.lift m (g := Int.castRingHom ℚ) (isUnit_intCast_rat m hm)

lemma exists_multiple_int (M : Submonoid ℤ) (hM : (0 : ℤ) ∉ M) (o : Type) [CommRing o]
    [Algebra ℤ o] [IsLocalization M o] (φ : o →+* ℚ) (a : o) :
    ∃ N : ℕ, 0 < N ∧ ∃ z : ℤ, (N : ℚ) * φ a = z := by
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj M a
  have hs0 : (s : ℤ) ≠ 0 := fun h => hM (h ▸ s.2)
  have hφ : φ a * ((s : ℤ) : ℚ) = z := by
    have := congrArg φ hs
    simpa only [map_mul, eq_intCast (algebraMap ℤ o), map_intCast] using this
  refine ⟨(s : ℤ).natAbs, Int.natAbs_pos.2 hs0, (Int.sign (s : ℤ)) * z, ?_⟩
  have hab : (((s : ℤ).natAbs : ℕ) : ℤ) = Int.sign (s : ℤ) * (s : ℤ) := by
    rw [Int.sign_mul_self]
  rw [show (((s : ℤ).natAbs : ℕ) : ℚ) = ((((s : ℤ).natAbs : ℕ) : ℤ) : ℚ) from
    (Int.cast_natCast _).symm, hab, Int.cast_mul, Int.cast_mul, ← hφ]
  ring

theorem ChartGlue.hypotheses_inhabited (S : Finset Nat.Primes) (p : Nat.Primes)
    [Algebra (Localization.Away (primeProd S)) ℚ] [Algebra (ZLoc p) ℚ] :
    SameRationalSpan
      ((scaledTrivBundle (Localization.Away (primeProd S)) onePoint 1 (one_ne_zero (α := ℚ))).lat ())
      ((scaledTrivBundle (ZLoc p) onePoint 1 (one_ne_zero (α := ℚ))).lat ()) := by
  refine sameRationalSpan_onePoint _ _ (fun a => ?_) (fun a => ?_)
  · refine exists_multiple_int (Submonoid.powers (primeProd S)) ?_ _ (algebraMap _ ℚ) a
    rintro ⟨n, hn⟩
    exact pow_ne_zero n (primeProd_ne_zero S) hn
  · exact exists_multiple_int (Ideal.span {((p : ℕ) : ℤ)}).primeCompl
      (fun h => h (Ideal.zero_mem _)) _ (algebraMap _ ℚ) a

theorem ChartGlue.applies (h : ChartGlue.Statement) :
    Nonempty (ChartBundle ℤ onePoint 1 (Fin 1 → ℚ)) := by
  let S : Finset Nat.Primes := {⟨2, Nat.prime_two⟩}
  let _ : Algebra (Localization.Away (primeProd S)) ℚ :=
    (awayToRat (primeProd S) (primeProd_ne_zero S)).toAlgebra
  let _ : ∀ p : S, Algebra (ZLoc p) ℚ := fun p => (zLocToRat p).toAlgebra
  obtain ⟨B, -⟩ := h ℚ Unit onePoint 1 (Fin 1 → ℚ) S (Localization.Away (primeProd S))
    (fun p => ZLoc p) (scaledTrivBundle _ onePoint 1 one_ne_zero)
    (fun p => scaledTrivBundle _ onePoint 1 one_ne_zero)
    (fun p i _ => ChartGlue.hypotheses_inhabited S p)
  exact ⟨B⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Model
