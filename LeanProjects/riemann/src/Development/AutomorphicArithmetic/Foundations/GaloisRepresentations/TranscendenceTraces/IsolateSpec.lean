import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtDegConst

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces

theorem pt_comp {Ω : Type} [Field Ω] {X Y : Scheme.{0}} (x : gp Ω ⟶ X) (f : X ⟶ Y) : pt (x ≫ f) = f (pt x) :=
  Scheme.Hom.comp_apply _ _ _

theorem pt_eq {Ω : Type} [Field Ω] {X : Scheme.{0}} (x : gp Ω ⟶ X) (t : gp Ω) : x t = pt x := by
  simp only [pt]
  exact congrArg x (Subsingleton.elim _ _)

theorem fib_bijOn {V U Z S : Scheme.{0}} {v : V ⟶ Z} {r : V ⟶ U} {p : Z ⟶ S} {u : U ⟶ S} (h : IsPullback v r p u)
    {Ω : Type} [Field Ω] (x : gp Ω ⟶ U) : Set.BijOn (fun z => z ≫ v) (fib r x) (fib p (x ≫ u)) := by
  refine ⟨fun z hz => ?_, fun z hz z' hz' he => ?_, fun y hy => ?_⟩
  · simp only [fib, Set.mem_setOf_eq] at hz ⊢
    rw [Category.assoc, h.w, ← Category.assoc, hz]
  · simp only [fib, Set.mem_setOf_eq] at hz hz'
    exact h.hom_ext he (hz.trans hz'.symm)
  · simp only [fib, Set.mem_setOf_eq] at hy
    exact ⟨h.lift y x hy, by simp [fib], by simp⟩

theorem Sq.To.isPullback {Z S : Scheme.{0}} {p : Z ⟶ S} {A B : Sq p} (t : A.To B) : IsPullback t.k A.r B.r t.g :=
  IsPullback.of_right (by rw [t.hv, t.hu]; exact A.pb) t.hr B.pb

theorem Sq.finite {Z S : Scheme.{0}} {p : Z ⟶ S} [IsFinite p] (A : Sq p) : IsFinite A.r :=
  MorphismProperty.of_isPullback A.pb ‹_›

section Sec
variable {R : Type} [CommRing R] {F G : Shv R}

theorem map_res (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := congrArg (fun h => h.hom x) (φ.hom.naturality g.op)

theorem res_res {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res k (Sec.res g x) = Sec.res (k ≫ g) x := by
  unfold Sec.res
  rw [op_comp, F.obj.map_comp]
  rfl

theorem res_id {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := congrArg (fun h => h.hom x) (F.obj.map_id (op U))

end Sec

def Chart : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (A : Type) [CommRing A] (u : Spec (CommRingCat.of A) ⟶ S),
  ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (v : Spec (CommRingCat.of B) ⟶ Z), Module.Finite A B ∧
    IsPullback v (Spec.map (CommRingCat.ofHom (algebraMap A B))) p u

def IsolateSpec : Prop := ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B] (z : Spec (CommRingCat.of B)),
  ∃ (A : Sq (Spec.map (CommRingCat.ofHom (algebraMap R B)))) (W : Set A.V) (v : A.V),
    Etale A.u ∧ IsClopen W ∧ v ∈ W ∧ A.v v = z ∧ ∀ v' ∈ W, A.r v' = A.r v → v' = v

def FibFin : Prop := ∀ {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] (Ω : Type) [Field Ω] (x : gp Ω ⟶ U), (fib r x).Finite

def PtEx : Prop := ∀ (X : Scheme.{0}) (s : X), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : gp Ω ⟶ X), pt x = s

def PtCommon : Prop := ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (z : gp Ω ⟶ X) (z' : gp Ω' ⟶ X), pt z = pt z' →
  ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (a : gp L ⟶ gp Ω) (a' : gp L ⟶ gp Ω'), a ≫ z = a' ≫ z'

def PtLift : Prop := ∀ {V U : Scheme.{0}} (r : V ⟶ U) [IsIntegralHom r] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U)
  (v : V), r v = pt x → ∃ z : gp Ω ⟶ V, z ≫ r = x ∧ pt z = v

def PtOne : Prop := ∀ {V : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : V ⟶ gp Ω) [IsFinite r] (L : Type) [Field L]
  (a : gp L ⟶ gp Ω) (z z' : gp L ⟶ V), z ≫ r = a → z' ≫ r = a → pt z = pt z' → z = z'

def WtExt : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  ∀ (Ω L : Type) [Field Ω] [IsAlgClosed Ω] [Field L] [IsAlgClosed L] (z : gp Ω ⟶ Z) (a : gp L ⟶ gp Ω), w L (a ≫ z) = w Ω z

def Isolate : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (z : Z), ∃ (A : Sq p) (W : Set A.V) (v : A.V),
  Etale A.u ∧ IsClopen W ∧ v ∈ W ∧ A.v v = z ∧ ∀ v' ∈ W, A.r v' = A.r v → v' = v

def GenBasic : Prop := (∀ S : Scheme.{0}, Dense {s : S | GenPt s}) ∧
  (∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (s : U), GenPt (j s) ↔ GenPt s) ∧
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S), GenPt s ↔ s = genericPoint S

def ImageFin : Prop := ∀ {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B) [IsSeparated bY] [LocallyOfFiniteType bY] (ι : Type)
  [Fintype ι] (Z : ι → Scheme.{0}) (p : ∀ a, Z a ⟶ S) (f : ∀ a, Z a ⟶ Y), (∀ a, IsFinite (p a)) → (∀ a, f a ≫ bY = p a ≫ bS) →
  ∃ (G : Scheme.{0}) (pG : G ⟶ S) (fG : G ⟶ Y) (h : ∀ a, Z a ⟶ G), IsFinite pG ∧ (∀ a, IsFinite (h a)) ∧
    (∀ a, h a ≫ pG = p a) ∧ (∀ a, h a ≫ fG = f a) ∧
    ∀ (T : Scheme.{0}) (x y : T ⟶ G), x ≫ pG = y ≫ pG → x ≫ fG = y ≫ fG → x = y

def ImageOne : Prop := ∀ {Z P S : Scheme.{0}} (k : Z ⟶ P) (b : P ⟶ S) [IsSeparated b] [LocallyOfFiniteType b] [IsFinite (k ≫ b)],
  IsFinite (k.imageι ≫ b) ∧ IsFinite k.toImage

def SHSec : Prop := ∀ (T C : Type) [CommRing T] [CommRing C] [Algebra T C] [Algebra.Etale T C] [Module.FaithfullyFlat T C],
  SH T → Nonempty (C →ₐ[T] T)

def FinSec : Prop := ∀ (O B C : Type) [CommRing O] [CommRing B] [CommRing C] [Algebra O B] [Module.Finite O B] [Algebra B C]
  [Algebra.Etale B C] [Module.FaithfullyFlat B C], SH O → Nonempty (C →ₐ[B] B)

def IndDesc : Prop := ∀ (A O B C : Type) [CommRing A] [CommRing O] [CommRing B] [CommRing C] [Algebra A O] [Algebra A B]
  [Algebra B C] [Algebra.FinitePresentation B C], IndEt A O → Nonempty (C →ₐ[B] B ⊗[A] O) →
  ∃ (E : Type) (_ : CommRing E) (_ : Algebra A E), Algebra.Etale A E ∧ Nonempty (E →ₐ[A] O) ∧ Nonempty (C →ₐ[B] B ⊗[A] E)

def RingSplit : Prop := ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Module.Finite A B] [Algebra B C]
  [Algebra.Etale B C] [Module.FaithfullyFlat B C] (P : PrimeSpectrum A),
  ∃ (E : Type) (_ : CommRing E) (_ : Algebra A E), Algebra.Etale A E ∧ P ∈ Set.range (PrimeSpectrum.comap (algebraMap A E)) ∧
    Nonempty (C →ₐ[B] B ⊗[A] E)

def LocFinAff : Prop := ∀ {W V U : Scheme.{0}} [IsAffine U] (π : W ⟶ V) (r : V ⟶ U) [Etale π] [Surjective π] [IsFinite r] (x : U),
  ∃ (U' : Scheme.{0}) (g : U' ⟶ U), IsAffine U' ∧ Etale g ∧ x ∈ Set.range g ∧
    ∃ s : pullback r g ⟶ W, s ≫ π = pullback.fst r g

def LocFinGeo : Prop := ∀ {W V U : Scheme.{0}} (π : W ⟶ V) (r : V ⟶ U) [Etale π] [Surjective π] [IsFinite r],
  Loc U fun U' g => ∃ s : pullback r g ⟶ W, s ≫ π = pullback.fst r g

def CoverOne : Prop := ∀ (R : Type) [CommRing R] {F G : Shv R} (f : F ⟶ G) (V : Scheme.{0}) (b : Sec G V),
  (Loc V fun W k => ∃ a : Sec F W, Sec.map f a = Sec.res k b) →
  ∃ (W : Scheme.{0}) (π : W ⟶ V) (a : Sec F W), Etale π ∧ Surjective π ∧ Sec.map f a = Sec.res π b

def LocFinSec : Prop := ∀ (R : Type) [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r]
  (b : Sec G V), (Loc V fun W k => ∃ a : Sec F W, Sec.map f a = Sec.res k b) →
  Loc U fun U' g => ∀ (V' : Scheme.{0}) (k : V' ⟶ V) (r' : V' ⟶ U'), k ≫ r = r' ≫ g → ∃ a : Sec F V', Sec.map f a = Sec.res k b

def WtCrit : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z),
  (∀ (A : Sq p) (φ : A.V → ℤ), IsLocallyConstant φ → ∀ u : A.U, ∃ (N : Set A.U) (c : ℤ), IsOpen N ∧ u ∈ N ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ A.U), pt x ∈ N → ∑ᶠ z ∈ fib A.r x, w Ω (z ≫ A.v) * φ (pt z) = c) →
  IsWt p w

def WtLocal : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z),
  (∀ s : S, ∃ A : Sq p, IsOpenImmersion A.u ∧ s ∈ Set.range A.u ∧ IsWt A.r (w.comap A.v)) → IsWt p w

def WtClopen : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z),
  (∀ (A : Sq p) (W : Set A.V), IsClopen W → ∃ ψ : A.U → ℤ, IsLocallyConstant ψ ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ A.U), ψ (pt x) = ∑ᶠ z ∈ fib A.r x ∩ {z | pt z ∈ W}, w Ω (z ≫ A.v)) →
  IsWt p w

def WtVanish : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w → ∀ D : Set S, Dense D →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Z), pt (z ≫ p) ∈ D → w Ω z = 0) → w = Wt.const Z 0

def MultBC : Prop := ∀ {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S) (g : S' ⟶ S), IsPullback v p' p g →
  mult p' = (mult p).comap v

def MultOpen : Prop := ∀ {W Z S : Scheme.{0}} (j : W ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ S), mult (j ≫ p) = (mult p).comap j

def MultEt : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [Etale p], mult p = Wt.const Z 1

def ArtSum : Prop := ∀ (Ω B : Type) [Field Ω] [IsAlgClosed Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B],
  ∑ᶠ P : PrimeSpectrum B, (Module.length (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal)).toNat =
    Module.finrank Ω B

def MultSec : Prop := ∀ {V : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : V ⟶ gp Ω) (z : gp Ω ⟶ V), z ≫ r = 𝟙 _ →
  mult r Ω z = ((Module.length (V.presheaf.stalk (pt z)) (V.presheaf.stalk (pt z))).toNat : ℤ)

def StalkSum : Prop := ∀ {V : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : V ⟶ gp Ω) [IsFinite r],
  ∑ᶠ v : V, (Module.length (V.presheaf.stalk v) (V.presheaf.stalk v)).toNat = r.finrank (IsLocalRing.closedPoint Ω)

def MultSumPt : Prop := ∀ {V : Scheme.{0}} (Ω : Type) [Field Ω] [IsAlgClosed Ω] (r : V ⟶ gp Ω) [IsFinite r],
  (mult r).push r Ω (𝟙 _) = (r.finrank (IsLocalRing.closedPoint Ω) : ℤ)

def MultPt : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (Ω Ω' : Type) [Field Ω] [IsAlgClosed Ω] [Field Ω']
  [IsAlgClosed Ω'] (z : gp Ω ⟶ Z) (z' : gp Ω' ⟶ Z), pt z = pt z' → mult p Ω z = mult p Ω' z'

def InvTrans : Prop := ∀ (A B G Ω : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B]
  [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Field Ω] (φ φ' : B →+* Ω),
  φ.comp (algebraMap A B) = φ'.comp (algebraMap A B) → ∃ g : G, ∀ b, φ' b = φ (g • b)

def GalTrans : Prop := ∀ (A L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
  [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
  [Normal (FractionRing A) L] [Field Ω] (φ φ' : integralClosure A L →+* Ω),
  φ.comp (algebraMap A _) = φ'.comp (algebraMap A _) →
  ∃ g : integralClosure A L ≃ₐ[A] integralClosure A L, ∀ b, φ' b = φ (g b)

def SplitField : Prop := ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [Module.Finite A B],
  ∃ (L : Type) (_ : Field L) (_ : Algebra A L) (_ : Algebra (FractionRing A) L) (_ : IsScalarTower A (FractionRing A) L),
    FiniteDimensional (FractionRing A) L ∧ Normal (FractionRing A) L ∧ Finite (B →ₐ[A] integralClosure A L) ∧
    ∀ (Ω : Type) [Field Ω] (φ : integralClosure A L →+* Ω) (z : B →+* Ω), Function.Injective (φ.comp (algebraMap A _)) →
      z.comp (algebraMap A B) = φ.comp (algebraMap A _) →
      ∃! σ : B →ₐ[A] integralClosure A L, φ.comp (σ : B →+* integralClosure A L) = z

def Sym {T Z S : Scheme.{0}} (π : T ⟶ S) {ι : Type} (σ : ι → (T ⟶ Z)) (m : ι → ℤ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : gp Ω ⟶ T), x ≫ π = x' ≫ π →
    ∃ e : ι ≃ ι, ∀ j, x ≫ σ j = x' ≫ σ (e j) ∧ m (e j) = m j

def Counts {T Z S : Scheme.{0}} (p : Z ⟶ S) (π : T ⟶ S) {ι : Type} (σ : ι → (T ⟶ Z)) (m : ι → ℤ) (w : Wt Z) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ T) (z : gp Ω ⟶ Z), z ≫ p = x ≫ π → w Ω z = ∑ᶠ j ∈ {j | x ≫ σ j = z}, m j

def CountEx : Prop := ∀ {T Z S : Scheme.{0}} (p : Z ⟶ S) (π : T ⟶ S) {ι : Type} (σ : ι → (T ⟶ Z)) (m : ι → ℤ),
  Sym π σ m → ∃ w, Counts p π σ m w

def CountWt : Prop := ∀ {T Z S : Scheme.{0}} (p : Z ⟶ S) (π : T ⟶ S) [IsFinite p] [IsIntegralHom π] [Surjective π] {ι : Type}
  [Finite ι] (σ : ι → (T ⟶ Z)) (m : ι → ℤ) (w : Wt Z), (∀ j, σ j ≫ p = π) → Counts p π σ m w → IsWt p w

def SplitCover : Prop := ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
  [Module.Finite A B], ∃ (T : Scheme.{0}) (π : T ⟶ Spec (CommRingCat.of A)) (ι : Type) (σ : ι → (T ⟶ Spec (CommRingCat.of B)))
    (c : ι → Spec (CommRingCat.of B)), IsIntegralHom π ∧ Surjective π ∧ Finite ι ∧
    (∀ j, σ j ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = π) ∧
    (∀ (Ω : Type) [Field Ω] (x x' : gp Ω ⟶ T), x ≫ π = x' ≫ π → ∃ e : ι ≃ ι, ∀ j, x ≫ σ j = x' ≫ σ (e j) ∧ c (e j) = c j) ∧
    ∀ (Ω : Type) [Field Ω] (x : gp Ω ⟶ T) (z : gp Ω ⟶ Spec (CommRingCat.of B)),
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = x ≫ π → (pt (x ≫ π)).asIdeal = ⊥ →
      (∃! j, x ≫ σ j = z) ∧ ∀ j, x ≫ σ j = z → c j = pt z

def NormSpec : Prop := ∀ (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Algebra A B]
  [Module.Finite A B], ∃ w, IsNwt (Spec.map (CommRingCat.ofHom (algebraMap A B))) w

def NormAff : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (U : S.Opens), IsAffineOpen U → IsDomain Γ(S, U) →
  IsIntegrallyClosed Γ(S, U) → ∃ (A : Sq p) (w : Wt A.V), IsOpenImmersion A.u ∧ Set.range A.u = U ∧ IsNwt A.r w

def NwtOpen : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (A : Sq p) [IsOpenImmersion A.u],
  IsNwt p w → IsNwt A.r (w.comap A.v)

def NwtAgree : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (A B : Sq p) [IsOpenImmersion A.u] [IsOpenImmersion B.u]
  (w : Wt A.V) (w' : Wt B.V), IsNwt A.r w → IsNwt B.r w' → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ A.V)
  (z' : gp Ω ⟶ B.V), z ≫ A.v = z' ≫ B.v → w Ω z = w' Ω z'

def NwtGlue : Prop := ∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p],
  (∀ s : S, ∃ (A : Sq p) (w : Wt A.V), IsOpenImmersion A.u ∧ s ∈ Set.range A.u ∧ IsNwt A.r w) → ∃ w, IsNwt p w

def NmlInt : Prop := ∀ (S : Scheme.{0}) [IsIntegral S], Nml S → LocNml S

def NmlNoeth : Prop := ∀ (S : Scheme.{0}) [IsLocallyNoetherian S], Nml S → LocNml S

def PtInj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (b b' : Sec (tw q i) U),
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x b = Sec.res x b') → b = b'

def HasVal {q : ℕ} {i : ℤ} {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U) (φ : U → ℤ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ U), Sec.res x y = φ (pt x) • Sec.res x (twGen i ζ)

def SecFun : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U),
  ∃ φ, IsLocallyConstant φ ∧ HasVal ζ y φ

def FunSec : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (φ : U → ℤ), IsLocallyConstant φ →
  ∃ y : Sec (tw q i) U, HasVal ζ y φ

def SumNat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {Z S : Scheme.{0}} {p : Z ⟶ S} (w : Wt Z) {A B : Sq p} (t : A.To B)
  (a : Sec F B.V) (b : Sec F B.U), IsSum w B a b → IsSum w A (Sec.res t.k a) (Sec.res t.g b)

def SumExLoc : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  ∀ (A : Sq p), Nonempty (Prim q Γ(A.U, ⊤)) → ∀ a : Sec (tw q i) A.V, ∃ b, IsSum w A a b

def SumEx : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  IsUnit (q : Γ(S, ⊤)) → ∀ (A : Sq p) (a : Sec (tw q i) A.V), ∃ b, IsSum w A a b

structure Rep0 {Z S : Scheme.{0}} (p : Z ⟶ S) (Q : ℕ) (Φ : Shv (ZMod Q) ⥤ Shv (ZMod Q)) (e : ∀ G, Fam0 p G (Φ.obj G)) : Prop where
  nat : ∀ {G G' : Shv (ZMod Q)} (f : G ⟶ G') (A : Sq p) (a : Sec G A.V),
    Sec.map (Φ.map f) ((e G).app A a) = (e G').app A (Sec.map f a)
  univ : ∀ (G J : Shv (ZMod Q)) (t : Fam0 p G J), ∃! m : Φ.obj G ⟶ J, ∀ A a, Sec.map m ((e G).app A a) = t.app A a

def FL : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (F G : Shv (ZMod Q)) (t : Fam0 p F G),
  (∃ τ : Fam p (res _ F) (res _ G), τ.Over t) ∧
  ∀ τ τ' : Fam p (res _ F) (res _ G), τ.Over t → τ'.Over t → ∀ (A : Sq p) (m n k : ℤ), m + 1 = n → n + 1 = k →
    ∀ a : Sec ((res _ F).X n) A.V, Sec.map ((res _ F).d n k) a = 0 →
    ∃ y, Sec.map ((res _ G).d m n) y = (τ.deg n).app A a - (τ'.deg n).app A a

def PhiEx : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p], ∃ (Φ : Shv (ZMod Q) ⥤ Shv (ZMod Q)) (_ : Φ.Additive)
  (e : ∀ G, Fam0 p G (Φ.obj G)), Rep0 p Q Φ e ∧ ∀ T : ShortComplex (Shv (ZMod Q)), T.Exact → (T.map Φ).Exact

def Rp {R : Type} [CommRing R] {I : Cx R} {X : Scheme.{0}} {n : ℤ} (x : CohomologyClass ((chains R).obj (sch.obj X)) I n)
    (a : Sec (I.X n) X) : Prop :=
  ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n, CohomologyClass.mk α = x ∧ ev α.1 0 n (by simp) X (𝟙 X) = a

def RpBasic : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ),
  (∀ x : CohomologyClass ((chains R).obj (sch.obj X)) I n, ∃ a, Rp x a) ∧
  (∀ (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) a, Rp x a → Sec.map (I.d n (n + 1)) a = 0) ∧
  (∀ (x x' : CohomologyClass ((chains R).obj (sch.obj X)) I n) a a', Rp x a → Rp x' a' →
    (x = x' ↔ ∃ y, Sec.map (I.d (n - 1) n) y = a - a') ∧ (a = a' → x = x') ∧ Rp (x + x') (a + a') ∧ ∀ d : ℤ, Rp (d • x) (d • a)) ∧
  (∀ (Y : Scheme.{0}) (f : Y ⟶ X) (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) a, Rp x a →
    Rp (cpull ((chains R).map (sch.map f)) I n x) (Sec.res f a)) ∧
  ∀ (R' : Type) [CommRing R'] (J : Cx R') (ρ : SemiMap I J) (x : CohomologyClass ((chains R).obj (sch.obj X)) I n) a,
    Rp x a → Rp (ρ.op.app (sch.obj X) n x) (ρ.app X n a)

def RpOp : Prop := ∀ {Z S : Scheme.{0}} {p : Z ⟶ S} (R' R : Type) [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
  (τ : Fam p I J) (n : ℤ) (x : CohomologyClass ((chains R').obj (sch.obj Z)) I n) (a : Sec (I.X n) Z),
  Rp x a → Rp (τ.op n x) ((τ.deg n).app (Sq.self p) a)

def ImgBasic : Prop := ∀ {Z S : Scheme.{0}} {p : Z ⟶ S} (R' R : Type) [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
  (τ : Fam p I J) (n : ℤ),
  (∀ α : Cochain ((chains R').obj (sch.obj Z)) I n, ∃! β, τ.IsImage α β) ∧
  ∀ (m : ℤ), n + 1 = m → ∀ (α : Cochain ((chains R').obj (sch.obj Z)) I n) β, τ.IsImage α β → τ.IsImage (δ n m α) (δ n m β)

def Fam.Sums {Z S : Scheme.{0}} {p : Z ⟶ S} {q : ℕ} {i : ℤ} (τ : Fam p (res _ (tw q i)) (res _ (tw q i))) (w : Wt Z) : Prop :=
  ∀ (A : Sq p) (a : Sec (tw q i) A.V), ∃ b, (τ.deg 0).app A (Sec.map (resι _ _) a) = Sec.map (resι _ _) b ∧ IsSum w A a b

def OpEq : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (F G : Shv (ZMod Q)) (t : Fam0 p F G)
  (τ τ' : Fam p (res _ F) (res _ G)), τ.Over t → τ'.Over t → ∀ n, τ.op n = τ'.op n

def TrChar : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w : Wt Z), IsWt p w →
  IsUnit (q : Γ(S, ⊤)) → (trFam p w q i).Over (tr0 p w q i) ∧ (trFam p w q i).Sums w ∧
    ∀ τ : Fam p (res _ (tw q i)) (res _ (tw q i)), τ.Sums w → ∀ n, tr p w q n i = τ.op n

def FamBC : Prop := ∀ (q : ℕ) (i : ℤ) {Z' S' Z S : Scheme.{0}} (v : Z' ⟶ Z) (p' : Z' ⟶ S') (p : Z ⟶ S) (g : S' ⟶ S)
  (w : Wt Z), IsPullback v p' p g → ∀ τ : Fam p (res _ (tw q i)) (res _ (tw q i)), τ.Sums w →
  ∃ τ' : Fam p' (res _ (tw q i)) (res _ (tw q i)), τ'.Sums (w.comap v) ∧
    ∀ n a, (τ'.deg n).app (Sq.self p') (Sec.res v a) = Sec.res g ((τ.deg n).app (Sq.self p) a)

def FamComp : Prop := ∀ (q : ℕ) (i : ℤ) {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S) [IsFinite r] [IsFinite p] (w' : Wt W)
  (w : Wt Z) (τ' : Fam r (res _ (tw q i)) (res _ (tw q i))) (τ : Fam p (res _ (tw q i)) (res _ (tw q i))), τ'.Sums w' → τ.Sums w →
  ∃ σ : Fam (r ≫ p) (res _ (tw q i)) (res _ (tw q i)), σ.Sums (Wt.mul r w' w) ∧
    ∀ n a, (σ.deg n).app (Sq.self _) a = (τ.deg n).app (Sq.self p) ((τ'.deg n).app (Sq.self r) a)

def FamPush : Prop := ∀ (q : ℕ) (i : ℤ) {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) [IsFinite h] [IsFinite p] (w : Wt Z)
  (τ : Fam (h ≫ p) (res _ (tw q i)) (res _ (tw q i))), τ.Sums w →
  ∃ σ : Fam p (res _ (tw q i)) (res _ (tw q i)), σ.Sums (w.push h) ∧
    ∀ n a, (σ.deg n).app (Sq.self p) a = (τ.deg n).app (Sq.self _) (Sec.res h a)

def FamLin : Prop := ∀ (q : ℕ) (i : ℤ),
  (∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (w w' : Wt Z) (τ τ' : Fam p (res _ (tw q i)) (res _ (tw q i))),
    τ.Sums w → τ'.Sums w' → ∃ σ : Fam p (res _ (tw q i)) (res _ (tw q i)), σ.Sums (w.add w') ∧
      ∀ n A a, (σ.deg n).app A a = (τ.deg n).app A a + (τ'.deg n).app A a) ∧
  (∀ {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (d : ℤ) (w : Wt Z) (τ : Fam p (res _ (tw q i)) (res _ (tw q i))),
    τ.Sums w → ∃ σ : Fam p (res _ (tw q i)) (res _ (tw q i)), σ.Sums (w.smul d) ∧
      ∀ n A a, (σ.deg n).app A a = d • (τ.deg n).app A a) ∧
  ∀ (S : Scheme.{0}) (d : ℤ), ∃ σ : Fam (𝟙 S) (res _ (tw q i)) (res _ (tw q i)), σ.Sums (Wt.const S d) ∧
    ∀ n a, (σ.deg n).app (Sq.self _) a = d • a

def SumComp : Prop := ∀ {W V U : Scheme.{0}} (r : W ⟶ V) (p : V ⟶ U) [IsFinite r] [IsFinite p] (Ω : Type) [Field Ω]
  (x : gp Ω ⟶ U) (M : Type 1) [AddCommGroup M] (c : (gp Ω ⟶ W) → M),
  ∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z

def RedZero : Prop := ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ i : ℤ,
  ∃ f : ∀ U : Scheme.{0}, Sec (tw Q i) U →+ Sec (tw q i) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec (tw Q i) U), Sec.res g (f U a) = f V (Sec.res g a)) ∧
    ∀ (U : Scheme.{0}) (a : Sec (tw Q i) U), (redMap Q q i).app U 0 (Sec.map (resι _ _) a) = Sec.map (resι _ _) (f U a)

def FamSemi : Prop := ∀ {Z S : Scheme.{0}} {p : Z ⟶ S} (R₁ R₂ R₃ : Type) [CommRing R₁] [CommRing R₂] [CommRing R₃] {I : Cx R₁}
  {J : Cx R₂} {K : Cx R₃},
  (∀ (τ : Fam p I J) (ρ : SemiMap J K), ∃ σ : Fam p I K, ∀ n A a, (σ.deg n).app A a = ρ.app A.U n ((τ.deg n).app A a)) ∧
  ∀ (ρ : SemiMap I J) (τ : Fam p J K), ∃ σ : Fam p I K, ∀ n A a, (σ.deg n).app A a = (τ.deg n).app A (ρ.app A.V n a)

def TrRel : Prop := ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (ι : Type) [Fintype ι]
  (w : ι → Wt Z) (m : ι → ℤ), (∀ a, IsWt p (w a)) → IsUnit (q : Γ(S, ⊤)) → ∀ D : Set S, Dense D →
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Z), pt (z ≫ p) ∈ D → ∑ a, m a * w a Ω z = 0) →
  ∀ x, ∑ a, m a • tr p (w a) q n i x = 0

def CycComp : Prop := ∀ {S Y X : Scheme.{0}} (c : Corr S Y) (d : Corr Y X) (e : Corr S X) (a : e.Z ⟶ d.Z) (b : e.Z ⟶ c.Z),
  IsPullback a b d.p c.f → e.p = b ≫ c.p → e.f = a ≫ d.f → e.w = Wt.mul b (d.w.comap a) c.w →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ X),
    e.cyc Ω x y = ∑ᶠ t : gp Ω ⟶ Y, c.cyc Ω x t * d.cyc Ω t y

def TrIdQ : Prop := ∀ (l : ℕ) [Fact l.Prime] (n i : ℤ) (S : Scheme.{0}) (d : ℤ), IsUnit (l : Γ(S, ⊤)) →
  trHQ l (𝟙 S) (Wt.const S d) n i = (d : ℚ_[l]) • LinearMap.id

end UpperTheory.Gal.TranscendenceTraces

end
