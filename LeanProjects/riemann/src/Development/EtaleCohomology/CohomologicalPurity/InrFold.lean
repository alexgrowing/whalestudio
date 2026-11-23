import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

def dbl (P : Arrow Spc) : Spc := pushout P.hom P.hom

def dbl.inl (P : Arrow Spc) : P.right ⟶ dbl P := pushout.inl P.hom P.hom
def dbl.inr (P : Arrow Spc) : P.right ⟶ dbl P := pushout.inr P.hom P.hom
def dbl.fold (P : Arrow Spc) : dbl P ⟶ P.right := pushout.desc (𝟙 _) (𝟙 _) rfl

def dbl.map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl P' ⟶ dbl P :=
  pushout.map _ _ _ _ φ.right φ.right φ.left (Arrow.w φ).symm (Arrow.w φ).symm

theorem dbl.inr_fold (P : Arrow Spc) : dbl.inr P ≫ dbl.fold P = 𝟙 _ := pushout.inr_desc _ _ _

theorem dbl.inr_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inr P' ≫ dbl.map φ = φ.right ≫ dbl.inr P :=
  pushout.inr_desc _ _ _

def Hs (q : ℕ) (P : Arrow Spc) (n i : ℤ) : AddSubgroup (Ht q (dbl P) n i) := (pull _ (dbl.inr P) (tw q i) n).ker

def Hs.fgt (q : ℕ) (P : Arrow Spc) (n i : ℤ) : Hs q P n i →+ Ht q P.right n i :=
  (pull _ (dbl.inl P) (tw q i) n).comp (Hs q P n i).subtype

def Hs.pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) : Hs q P n i →+ Hs q P' n i :=
  ((GlobalTheory.EtC.pull _ (dbl.map φ) (tw q i) n).comp (Hs q P n i).subtype).codRestrict _ fun x => by
    change GlobalTheory.EtC.pull _ (dbl.inr P') _ n (GlobalTheory.EtC.pull _ (dbl.map φ) _ n x.1) = 0
    have hx : GlobalTheory.EtC.pull _ (dbl.inr P) (tw q i) n x.1 = 0 := x.2
    rw [← pull_comp, dbl.inr_map, pull_comp, hx, map_zero]

def Hs.proj (q : ℕ) (P : Arrow Spc) (n i : ℤ) (c : Ht q (dbl P) n i) : Hs q P n i :=
  ⟨c - GlobalTheory.EtC.pull _ (dbl.fold P) _ n (GlobalTheory.EtC.pull _ (dbl.inr P) _ n c), by
    change GlobalTheory.EtC.pull _ (dbl.inr P) _ n _ = 0
    rw [map_sub, ← pull_comp _ (dbl.inr P) (dbl.fold P), dbl.inr_fold, pull_id, sub_self]⟩

def Hs.act (q : ℕ) {P : Arrow Spc} {n m i j : ℤ} (a : Ht q P.right n i) (b : Hs q P m j) : Hs q P (n + m) (i + j) :=
  Hs.proj q P _ _ (cup q (GlobalTheory.EtC.pull _ (dbl.fold P) _ n a) b.1)

def opn {X : Scheme.{0}} (U : X.Opens) : Arrow Spc := Arrow.mk (sch.map U.ι)

def opnMap {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) : opn U' ⟶ opn U :=
  Arrow.homMk (sch.map (f.resLE U U' h)) (sch.map f) (by
    change sch.map _ ≫ sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])

def off (A : Type) [CommRing A] (I : Ideal A) : (Spec (CommRingCat.of A)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

def Exc (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) : Prop := ∀ n i, Function.Bijective (Hs.pull q φ n i)

def IsBd (δ : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), Ht q P.left n i →+ Hs q P (n + 1) i) : Prop :=
  (∀ (q : ℕ) (P : Arrow Spc), Mono P.hom → ∀ n i : ℤ,
    Function.Exact (Hs.fgt q P n i) (pull _ P.hom (tw q i) n) ∧
    Function.Exact (pull _ P.hom (tw q i) n) (δ q P n i) ∧
    Function.Exact (δ q P n i) (Hs.fgt q P (n + 1) i)) ∧
  (∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), Mono P'.hom → Mono P.hom → ∀ (n i : ℤ) (u : Ht q P.left n i),
    Hs.pull q φ _ _ (δ q P n i u) = δ q P' n i (pull _ φ.left _ _ u)) ∧
  ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ P : Arrow Spc, Mono P.hom → ∀ (n i : ℤ) (u : Ht Q P.left n i),
    (δ q P n i (red Q q _ n i u)).1 = red Q q _ (n + 1) i (δ Q P n i u).1

def Nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) : Prop :=
  φ.Etale ∧ Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)

def IndNbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) : Prop :=
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
    Nonempty (IsColimit (Cocone.mk _ t)) ∧ ∀ j, Nbhd (A := A) (s.app j).hom I ∧ s.app j ≫ t.app j = CommRingCat.ofHom φ

structure Hens where
  obj : ∀ (A : Type) [CommRing A], Ideal A → CommRingCat.{0}
  η : ∀ (A : Type) [CommRing A] (I : Ideal A), A →+* obj A I
  map : ∀ {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} (φ : A →+* B), I ≤ J.comap φ →
    obj A I →+* obj B J
  map_η : ∀ {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} (φ : A →+* B) (h : I ≤ J.comap φ),
    (map φ h).comp (η A I) = (η B J).comp φ
  map_id : ∀ (A : Type) [CommRing A] (I : Ideal A) (h : I ≤ I.comap (RingHom.id A)), map (RingHom.id A) h = RingHom.id _
  map_comp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {I : Ideal A} {J : Ideal B} {K : Ideal C}
    (φ : A →+* B) (ψ : B →+* C) (h : I ≤ J.comap φ) (h' : J ≤ K.comap ψ) (h'' : I ≤ K.comap (ψ.comp φ)),
    map (ψ.comp φ) h'' = (map ψ h').comp (map φ h)
  hens : ∀ (A : Type) [CommRing A] (I : Ideal A), HenselianRing (obj A I) (I.map (η A I))
  ind : ∀ (A : Type) [CommRing A] (I : Ideal A), IndNbhd (η A I) I

def Chart (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (φ : A →+* B) (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B),
    Nbhd φ I ∧ ψ.Etale ∧ I.map φ = Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) ∧
    ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ

def IsThom (d : ℕ) (th : ∀ (q : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A), Ideal.span (Set.range x) = I →
    Hs q (opn (off A I)) (2 * d) d) : Prop :=
  ∀ (q : ℕ) [NeZero q],
  (∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) I J x hx hy h, IsUnit (q : A) →
    Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B J) (off A I) h) _ _ (th q A I x hx) = th q B J (φ ∘ x) hy) ∧
  (∀ (A : Type) [CommRing A] I x (M : Matrix (Fin d) (Fin d) A) hx hy, IsUnit (q : A) → IsUnit M.det →
    th q A I (M.mulVec x) hy = th q A I x hx) ∧
  (∀ (R : Type) [CommRing R] I hx, IsUnit (q : R) → ∀ n i : ℤ, Function.Bijective fun a : Ht q (sp R) n i =>
    Hs.act q (P := opn (off (MvPolynomial (Fin d) R) I))
      (pull _ (spMap (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)) _ _ a) (th q _ I MvPolynomial.X hx)) ∧
  ∀ r : ℕ, r ∣ q → ∀ (A : Type) [CommRing A] I x hx, IsUnit (q : A) →
    (th r A I x hx).1 = red q r _ _ _ (th q A I x hx).1

def thom (d : ℕ) : ∀ (q : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A), Ideal.span (Set.range x) = I →
    Hs q (opn (off A I)) (2 * d) d := @pick _ ⟨fun _ _ _ _ _ _ => 0⟩ (IsThom d)

structure SP (d : ℕ) where
  (X Z S : Scheme.{0})
  p : X ⟶ S
  ι : Z ⟶ X
  e : ℕ
  U : X.Opens
  cl : IsClosedImmersion ι
  smX : SmoothOfRelativeDimension (e + d) p
  smZ : SmoothOfRelativeDimension e (ι ≫ p)
  hU : (U : Set X) = (Set.range ι)ᶜ

structure SP.Hom {d : ℕ} (P' P : SP d) where
  f : P'.X ⟶ P.X
  g : P'.Z ⟶ P.Z
  cart : IsPullback P'.ι g f P.ι
  le : P'.U ≤ f ⁻¹ᵁ P.U

def IsCl (d : ℕ) (c : ∀ (q : ℕ) (P : SP d), Hs q (opn P.U) (2 * d) d) : Prop :=
  ∀ (q : ℕ) [NeZero q],
  (∀ (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ (B : Type) [CommRing B] (I : Ideal B) (x : Fin d → B) hx
    (w : Spec (CommRingCat.of B) ⟶ P.X) (z : Spec (CommRingCat.of (B ⧸ I)) ⟶ P.Z) h, Etale w →
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) z w P.ι →
    Hs.pull q (opnMap w (off B I) P.U h) _ _ (c q P) = thom d q B I x hx) ∧
  (∀ (P' P : SP d) (φ : P'.Hom P), IsUnit (q : Γ(P.X, ⊤)) → Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (c q P) = c q P') ∧
  ∀ r : ℕ, r ∣ q → ∀ P : SP d, IsUnit (q : Γ(P.X, ⊤)) → (c r P).1 = red q r _ _ _ (c q P).1

def fcl (d : ℕ) : ∀ (q : ℕ) (P : SP d), Hs q (opn P.U) (2 * d) d := @pick _ ⟨fun _ _ => 0⟩ (IsCl d)

def abv {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) : Arrow Spc :=
  Arrow.mk (pullback.fst π (sch.map U.ι))

def abvMap {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) : abv U π ⟶ opn U :=
  Arrow.homMk (pullback.snd π (sch.map U.ι)) π pullback.condition.symm

structure Tube {d : ℕ} (P : SP d) where
  E : Spc
  π : E ⟶ sch.obj P.X
  ok : ∀ (q : ℕ) [NeZero q], IsUnit (q : Γ(P.X, ⊤)) →
    (∀ i, Eqv _ (pullback.fst π (sch.map P.ι)) (tw q i)) ∧ (∀ i, Eqv _ (pullback.snd π (sch.map P.ι)) (tw q i)) ∧
    Exc q (abvMap P.U π) ∧ ∀ n i : ℤ, Function.Bijective fun a : Ht q E n i =>
      Hs.act q (P := abv P.U π) a (Hs.pull q (abvMap P.U π) _ _ (fcl d q P))

end LateralTheory.CohomologicalPurity
