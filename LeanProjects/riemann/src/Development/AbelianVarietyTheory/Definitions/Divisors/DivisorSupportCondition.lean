import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockGLMap

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def A1 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (F : Shv R) (n : ℤ),
  Function.Bijective (HK.pull R f F n)

def A2 : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (F : Shv R), Eqv R (cechAug f) F

def A3 : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R),
  (∀ n, Eqv R (disc.map (f.app n)) F) → Eqv R f F

def A4 : Prop := ∀ (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
  (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (F : Shv R),
  Cover2 R f g → Cover2 R f' g' → Eqv R u F → Eqv R v F → Eqv R (pullback.map f g f' g' u v p hu hv) F → Eqv R p F

def A5 : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ), 0 < n → ∀ x : H R (sch.obj X) F n,
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), Etale f ∧ Surjective f ∧ pull R (sch.map f) F n x = 0

def DivisorNaturality : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)) ∧
  (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧
  (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def DivisorRingCompatibility : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc),
  (Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧
  (∀ {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)) ∧
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

def DivisorSupportCondition : Prop := ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g →
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), pull _ f _ _ a = 0 → pull _ g _ _ b = 0 → cup q a b = 0

def DivisorAdditivity : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M) ∧
  ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

def A7 : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1, ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))

def A8 : Prop := ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (E : Spc) (F : Shv S) (n : ℤ),
  Function.Bijective (restrH φ E F n)

def A9 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spc) (n : ℤ), n < 0 → Subsingleton (H R E F n)) ∧
  ∃ e : ∀ X : Scheme.{0}, Sec F X ≃+ H R (sch.obj X) F 0,
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (e X s) = e Y (Sec.res f s)) ∧
    ∀ (X : Scheme.{0}) (s : Sec F X), ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = e X s ∧
      ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def A10 : Prop := ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G),
  (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) →
  ∀ n, Function.Bijective (HK.post R ((chains R).obj E) φ n)

def A11 : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc,
  (∀ {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b)) ∧
  (Inv Q E → red Q q E _ _ (one Q E) = one q E ∧ ∀ L : E ⟶ ofCat (glCat 1), red Q q E _ _ (c1 Q L) = c1 q L) ∧
  (∀ (n i : ℤ) (a : Ht Q E n i), red Q Q E n i a = a) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht Q E n i), red q r E n i (red Q q E n i a) = red Q r E n i a

def B1 : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
  ∀ n i : ℤ,
  (∀ x : Ht q (sp c.pt) n i, IsUnit (q : c.pt) → ∃ j y, pull _ (spMap (c.ι.app j).hom) _ _ y = x) ∧
  ∀ j (y : Ht q (sp (D.obj j)) n i), IsUnit (q : D.obj j) → pull _ (spMap (c.ι.app j).hom) _ _ y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull _ (spMap (D.map f).hom) _ _ y = 0

def B2 : Prop := ∀ (R : Type) [CommRing R] (A : Type) [CommRing A], SH A → ∀ (F : Shv R) (n : ℤ), 0 < n →
  Subsingleton (H R (sp A) F n)

def B3 : Prop := ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f]
  [QuasiSeparated f], IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S), SH A →
    Eqv _ (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)) → Eqv _ (sch.map f) (tw q i)

def B4 : Prop := ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  Eqv _ (cechAug f) (tw q i)

def B5 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A], AIC A → IsUnit (q : A) → Acyc q (sp A)

def DivisorPicardCompatibility : Prop := ∀ (A : Type) [CommRing A], Nonempty (H ℤ (sp A) Gm 1 ≃+ Additive (CommRing.Pic A))

def B6h1 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ u : Aˣ, ∃ v, u = v ^ q) →
  (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → Subsingleton (Ht q (sp A) 1 1)

def B7 : Prop := ∀ (q : ℕ) [NeZero q] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], IsUnit (q : K) → ∀ (i : ℕ)
  (M : Rep (ZMod q) (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (ζ : Ω), IsPrimitiveRoot ζ q → ∀ b : Module.Basis Unit (ZMod q) M,
  (∀ (σ : Ω ≃ₐ[K] Ω) (a : ℕ), σ ζ = ζ ^ a → M.ρ σ (b ()) = ((a : ZMod q) ^ i) • b ()) → ∀ n : ℕ,
  Nonempty (Ht q (sp K) n i ≃+ GroundTheory.ProfCoh.cohomology M n)

def C1 : Prop := ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K]
  [Algebra.IsAlgebraic (RatFunc k) K], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp K) n i)

def C2 : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp B) n i)

def C3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ (B : Type) [CommRing B] [Algebra (Polynomial T) B] [Algebra.Etale (Polynomial T) B] [Algebra T B]
    [IsScalarTower T (Polynomial T) B] (i : ℤ),
  Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom) (tw q i)

def C4 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

def C5 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ,
  (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q)

def D1 : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → ∀ n i : ℤ,
  Function.Bijective fun a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ)) =>
    ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def D2 : Prop := ∀ (q : ℕ) [NeZero q] (k : ℕ), 0 < k →
  ∃ s : ∀ {E : Spc} {N : ℕ}, (E ⟶ ofCat (glCat N)) → Ht q E (2 * k) k,
    (∀ {E E' : Spc} {N} (f : E ⟶ E') (V : E' ⟶ ofCat (glCat N)), Inv q E' → pull _ f _ _ (s V) = s (f ≫ V)) ∧
    (∀ {E : Spc} {a b} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)), Inv q E → s (bsumOf V W) = s V + s W) ∧
    ∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → s L = cpow q (c1 q L) k

def D3 : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ),
  (∀ c : groupHomology.cycles (Rep.trivial R Γ R) m, ∃ z, IsSlant R X (groupHomology.iCycles (Rep.trivial R Γ R) m c) z) ∧
  ∀ (F : Shv R) (n : ℤ), IsSlantMap R Γ X F m n (slantR R Γ X F m n)

def E1 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Ideal.Quotient.mk I)) (tw q i)

def E2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) (tw q i)

def E3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i)

def E4 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ), Finite (Ht q (sch.obj X) n i)

def E6 : Prop := ∀ (q : ℕ) [NeZero q] {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)], IsUnit (q : Γ(S, ⊤)) →
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → ∀ n i : ℤ,
  (n < 2 * d - 1 → Function.Bijective (pull _ (sch.map U.ι) (tw q i) n)) ∧
  (n < 2 * d → Function.Injective (pull _ (sch.map U.ι) (tw q i) n))

def E8 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

end GlobalTheory.EtC

end
