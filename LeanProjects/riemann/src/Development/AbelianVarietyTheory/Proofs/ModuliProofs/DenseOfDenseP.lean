import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.NearBuild

variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']

abbrev loc (f : R) : R →+* Localization.Away f := algebraMap R (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (x : B →+* C) (y : A →+* B) :
    spMap (x.comp y) = spMap x ≫ spMap y := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)

def Good {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) : Prop :=
  s = spMap x ≫ spMap β ∧ t.Shape Mat κ ∧ t.HasTh (𝟙 _) (fun a => x (v a))

def Den (q₀ : Ideal R) : Prop := DenseP (objPrimes b Mat κ β v) ∧ q₀ ∈ objPrimes b Mat κ β v

def Concl : Prop :=
  ∃ t : TObj g (N' ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → TMap t' t (spMap x)

def NearC (q₀ : Ideal R) : Prop :=
  ∃ f : R, f ∉ q₀ ∧ Concl b Mat κ ((loc f).comp β) (fun a => loc f (v a))

def FibData (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) {Hh : Type} (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ)
    (d : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t →
    ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _))))
      (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)), t.Emb m (Over.mk (𝟙 _)) σ ∧
      ProjRep I (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) ∧
      CutBy I Q d (fun h a => x (p (hh h) a)) ∧
      ∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ N')).left (fun a => x (p h a))
end

def Fib {b : TBase o (N' ^ 2)} (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
    (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) {K : Type} [Field K] (x : R →+* K) {s : Sp K ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z.left) : Prop :=
  IsPullback φ t.A.hom Z.hom (spMap x) ∧
    (∃ σ, t.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t.A).left)
      (w : Ix g (N' ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t.A).left ≫ φ) w) ∧
    LBIso (lbPow t.L (m ^ 2)) (M.pull φ) ∧ ∀ h, (t.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) {Z : Over (Sp R)} (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec)
  (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z))

def Fam : Prop :=
  (∃ (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) R)) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R),
    ProjRep I Z.hom M th ∧ ∀ h, SecCoord M th (sc h).left (p h)) ∧ Flat Z.hom ∧
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
    Good b Mat κ β v x t → ∃ φ, Fib m M th sc x t φ

def AddOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (mu : Z' ⊗ Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z' ⊗ Z').left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ

def EndOk (ρ : R →+* R') {Z' : Over (Sp R')} (π : Z'.left ⟶ Z.left) (i : Option J) (F : Z' ⟶ Z') : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z'.left), Good b Mat κ β v (x.comp ρ) t → Fib m M th sc (x.comp ρ) t (φ ≫ π) →
    φ ≫ Z'.hom = t.A.hom ≫ spMap x →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ

def AddAt (mu : Z ⊗ Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    ∀ φ₂ : (t.A ⊗ t.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ mu.left = (μ[t.A]).left ≫ φ

def EndAt (i : Option J) (F : Z ⟶ Z) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s)
    (φ : t.A.left ⟶ Z.left), Good b Mat κ β v x t → Fib m M th sc x t φ →
    φ ≫ F.left = (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
end

def Lab (k : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) : Prop :=
  (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ k = 1) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 →
      ∃! c : Ix g k, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ Q i)
        (fun i => (c i).val) = y

def GLies {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver S ⟶ A)) (y : S' ⟶ S) {s : S' ⟶ Sp o} (t : TObj g (N' ^ 2) J b s)
    (ψ : t.A.left ⟶ A.left) : Prop :=
  IsGrpPullback t.A A y ψ ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ N').left ≫ ψ = y ≫ (Q i).left

section
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)

def GrpFam (m : ℕ) (A : Over (Sp R)) [GrpObj A] (M : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ M.IsLB ∧ Out.RelAmple A M ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso (lbPow t.L (m ^ 2)) (M.pull ψ)

def PolFam (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A))
    (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) : Prop :=
  IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧
    Out.RelAmple A L ∧ Lab N' A act Q ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t → ∃ ψ, GLies A act Q (spMap x) t ψ ∧ LBIso t.L (L.pull ψ)

variable {b Mat κ β v}

theorem good_comp (ρ : R →+* R') {K : Type} [Field K] (x : R' →+* K) {s : Sp K ⟶ Sp o} (t : TObj g (N' ^ 2) J b s) :
    Good b Mat κ (ρ.comp β) (fun a => ρ (v a)) x t ↔ Good b Mat κ β v (x.comp ρ) t := by
  simp only [Good, spMap_comp, Category.assoc, RingHom.comp_apply]

theorem mem_objPrimes {q : Ideal R} : q ∈ objPrimes b Mat κ β v ↔
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      RingHom.ker x = q ∧ Good b Mat κ β v x t := by
  constructor
  · rintro ⟨K, hF, hA, x, t, hk, hs, hth⟩
    exact ⟨K, hF, hA, x, _, t, hk, rfl, hs, hth⟩
  · rintro ⟨K, hF, hA, x, s, t, hk, ⟨rfl, hs, hth⟩⟩
    exact ⟨K, hF, hA, x, t, hk, hs, hth⟩

theorem isPrime_of_mem {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) : q.IsPrime := by
  obtain ⟨K, hF, -, x, -, rfl, -⟩ := h
  exact RingHom.ker_isPrime x

theorem exists_mem_loc {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) {f : R} (hf : f ∉ q) :
    ∃ q₁ ∈ objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a)), q₁.comap (loc f) = q := by
  obtain ⟨K, hF, hA, x, s, t, hk, hg⟩ := mem_objPrimes.1 h
  have hu : IsUnit (x f) := by
    refine isUnit_iff_ne_zero.2 fun h0 => hf ?_
    rw [← hk]
    exact h0
  let y : Localization.Away f →+* K := IsLocalization.Away.lift f hu
  have hy : y.comp (loc f) = x := IsLocalization.Away.lift_comp f hu
  refine ⟨RingHom.ker y, mem_objPrimes.2 ⟨K, hF, hA, y, s, t, rfl, ?_⟩, ?_⟩
  · rw [good_comp, hy]
    exact hg
  · rw [RingHom.comap_ker, hy, hk]

theorem densePrimes_localization (h : DenseP (objPrimes b Mat κ β v)) (f : R) :
    DenseP (objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a))) := by
  intro g hg
  obtain ⟨⟨a, c⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) g
  have hfa : f * a = 0 := by
    apply h
    intro p hp _
    by_cases hfp : f ∈ p
    · exact p.mul_mem_right a hfp
    · obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc hp hfp
      have hgq : g ∈ q₁ := hg q₁ hq₁ (isPrime_of_mem hq₁)
      have haq : algebraMap R (Localization.Away f) a ∈ q₁ := by
        rw [← hc]
        exact q₁.mul_mem_right _ hgq
      have : a ∈ p := by
        rw [← hcomap]
        exact haq
      exact p.mul_mem_left f this
  have hloc : algebraMap R (Localization.Away f) a = 0 := by
    have h1 := congrArg (algebraMap R (Localization.Away f)) hfa
    rw [map_mul, map_zero] at h1
    exact (IsLocalization.Away.algebraMap_isUnit f).mul_right_eq_zero.1 h1
  have hcu : IsUnit (algebraMap R (Localization.Away f) (c : R)) :=
    IsLocalization.map_units (Localization.Away f) c
  simp only at hc
  rw [hloc] at hc
  exact hcu.mul_left_eq_zero.1 hc

theorem Den.loc {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀) :
    ∃ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ ∧ q₁.comap (loc f) = q₀ := by
  obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc h.2 hf
  exact ⟨q₁, ⟨densePrimes_localization h.1 f, hq₁⟩, hcomap⟩

theorem FibData.comp {m : ℕ} {p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R} {Hh : Type} {hh : Hh → Ix g (N' ^ 2)}
    {Q : Polynomial ℚ} {d : ℕ} (h : FibData b Mat κ β v m p hh Q d) (ρ : R →+* R') :
    FibData b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (fun c a => ρ (p c a)) hh Q d := by
  intro K _ _ x s t hg
  exact h K (x.comp ρ) s t ((good_comp ρ x t).1 hg)

theorem dense_of_denseP {P : Set (Ideal R)} (h : DenseP P) : Dense {p : Sp R | p.asIdeal ∈ P} := by
  have hv : PrimeSpectrum.vanishingIdeal {p : PrimeSpectrum R | p.asIdeal ∈ P} = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    refine h a fun p hp hpr => ?_
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).1 ha ⟨p, hpr⟩ hp
  have hc : closure {p : PrimeSpectrum R | p.asIdeal ∈ P} = Set.univ := by
    rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hv]
    simp
  exact dense_iff_closure_eq.2 hc
end

end GlobalTheory.ZM.NearBuild
end
