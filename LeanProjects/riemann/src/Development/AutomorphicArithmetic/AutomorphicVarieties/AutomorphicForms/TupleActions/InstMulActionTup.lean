import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

noncomputable section

open NumberField CategoryTheory

namespace UpperTheory.V.Af.BA

open UpperTheory.V.Af.CohB

section Perm

variable (Γ : Type) [Group Γ]

def permC (X : Type) [MulAction Γ X] : Representation ℂ Γ (X →₀ ℂ) where
  toFun g := Finsupp.lmapDomain ℂ ℂ (fun x : X => g • x)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_smul]

abbrev PC (X : Type) [MulAction Γ X] : Rep.{0} ℂ Γ := Rep.of (permC Γ X)

variable {Γ}

@[simp] theorem permC_single {X : Type} [MulAction Γ X] (g : Γ) (x : X) (c : ℂ) :
    permC Γ X g (Finsupp.single x c) = Finsupp.single (g • x) c := by
  simp [permC]

def pmap {X Y : Type} [MulAction Γ X] [MulAction Γ Y] (f : X → Y) (hf : ∀ (g : Γ) x, f (g • x) = g • f x) :
    PC Γ X ⟶ PC Γ Y :=
  Rep.ofHom ⟨Finsupp.lmapDomain ℂ ℂ f, fun g => by ext x; simp [hf]⟩

@[simp] theorem pmap_single {X Y : Type} [MulAction Γ X] [MulAction Γ Y] (f : X → Y)
    (hf : ∀ (g : Γ) x, f (g • x) = g • f x) (x : X) (c : ℂ) :
    (pmap f hf).hom (Finsupp.single x c) = Finsupp.single (f x) c :=
  Finsupp.mapDomain_single

variable (Γ) in

def augC (X : Type) [MulAction Γ X] : PC Γ X ⟶ Rep.trivial ℂ Γ ℂ :=
  Rep.ofHom ⟨Finsupp.linearCombination ℂ (fun _ : X => (1 : ℂ)), fun g => by ext x; simp⟩

@[simp] theorem augC_single {X : Type} [MulAction Γ X] (x : X) (c : ℂ) :
    (augC Γ X).hom (Finsupp.single x c) = c := by
  change Finsupp.linearCombination ℂ (fun _ : X => (1 : ℂ)) (Finsupp.single x c) = c
  simp

theorem PC_ext {X : Type} [MulAction Γ X] {A : Rep.{0} ℂ Γ} {φ ψ : PC Γ X ⟶ A}
    (h : ∀ x, φ.hom (Finsupp.single x 1) = ψ.hom (Finsupp.single x 1)) : φ = ψ := by
  ext x
  exact h x

variable (Γ) in

def FinOrb (X : Type) [MulAction Γ X] : Prop := ∃ R : Set X, R.Finite ∧ ∀ x : X, ∃ g : Γ, g • x ∈ R

end Perm

structure Cx (Γ I : Type) [Group Γ] [MulAction Γ I] where
  S : ∀ n, Set (Fin n → I)
  comp : ∀ {m n : ℕ} (f : Fin m → Fin n) (t : Fin n → I), t ∈ S n → t ∘ f ∈ S m
  smul : ∀ {n : ℕ} (g : Γ) (t : Fin n → I), t ∈ S n → (fun j => g • t j) ∈ S n

instance (Γ I : Type) [Group Γ] [MulAction Γ I] : Inhabited (Cx Γ I) :=
  ⟨⟨fun _ => Set.univ, fun _ _ _ => trivial, fun _ _ _ => trivial⟩⟩

namespace Cx

variable {Γ I : Type} [Group Γ] [MulAction Γ I] (K : Cx Γ I)

def Tup (p : ℕ) : Type := {t : Fin (p + 1) → I // t ∈ K.S (p + 1)}

instance (p : ℕ) : MulAction Γ (K.Tup p) where
  smul g t := ⟨fun j => g • t.1 j, K.smul g t.1 t.2⟩
  one_smul t := Subtype.ext (funext fun j => one_smul _ (t.1 j))
  mul_smul g k t := Subtype.ext (funext fun j => mul_smul g k (t.1 j))

theorem smul_val {p : ℕ} (g : Γ) (t : K.Tup p) (j : Fin (p + 1)) : (g • t).1 j = g • t.1 j := rfl

def re {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (t : K.Tup q) : K.Tup p := ⟨t.1 ∘ f, K.comp f t.1 t.2⟩

theorem re_re {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (f' : Fin (q + 1) → Fin (r + 1)) (t : K.Tup r) :
    K.re f (K.re f' t) = K.re (f' ∘ f) t := rfl

def reC {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : PC Γ (K.Tup q) ⟶ PC Γ (K.Tup p) :=
  pmap (K.re f) (fun _ _ => rfl)

@[simp] theorem reC_single {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (t : K.Tup q) (c : ℂ) :
    (K.reC f).hom (Finsupp.single t c) = Finsupp.single (K.re f t) c := pmap_single _ _ _ _

theorem reC_comp {p q r : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (f' : Fin (q + 1) → Fin (r + 1)) :
    K.reC f' ≫ K.reC f = K.reC (f' ∘ f) :=
  PC_ext fun t => by
    change (K.reC f).hom ((K.reC f').hom _) = _
    rw [reC_single, reC_single, reC_single, re_re]

def d (p : ℕ) : PC Γ (K.Tup (p + 1)) ⟶ PC Γ (K.Tup p) :=
  ∑ i : Fin (p + 2), ((-1 : ℂ) ^ (i : ℕ)) • K.reC i.succAbove

def alt (p : ℕ) : PC Γ (K.Tup p) ⟶ PC Γ (K.Tup p) :=
  (((p + 1).factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin (p + 1)), (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • K.reC π

def ExactZ : Prop := ∀ m, KH.FaceExactTo K.Tup (fun _ i => K.re i.succAbove) m

def ExactC : Prop :=
  Function.Surjective (augC Γ (K.Tup 0)).hom ∧ Function.Exact (K.d 0).hom (augC Γ (K.Tup 0)).hom ∧
    ∀ p, Function.Exact (K.d (p + 1)).hom (K.d p).hom

end Cx

def ResOf : Prop :=
  ∀ (Γ : Type) [Group Γ] (X : ℕ → Rep.{0} ℂ Γ) (d : ∀ p, X (p + 1) ⟶ X p) (ε : X 0 ⟶ Rep.trivial ℂ Γ ℂ),
    (∀ p, Projective (X p)) → Function.Surjective ε.hom → Function.Exact (d 0).hom ε.hom →
    (∀ p, Function.Exact (d (p + 1)).hom (d p).hom) →
    ∃ P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ), (∀ p, Nonempty (P.complex.X p ≅ X p)) ∧
      ∀ e : ∀ p, X p ⟶ X p, e 0 ≫ ε = ε → (∀ p, e (p + 1) ≫ d p = d p ≫ e p) →
        ∃ e' : P.complex ⟶ P.complex, e' ≫ P.π = P.π ∧ ∀ p, e p = 0 → e'.f p = 0

def VanishOf : Prop :=
  ∀ (Γ : Type) [Group Γ] (P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ)) (e : P.complex ⟶ P.complex), e ≫ P.π = P.π →
    ∀ q, e.f q = 0 → ∀ A : Rep.{0} ℂ Γ, Module.rank ℂ (groupCohomology A q) = 0

def RankCohHom : Prop :=
  ∀ (Γ : Type) [Group Γ] (P : ProjectiveResolution (Rep.trivial ℂ Γ ℂ)) (q : ℕ) (X : Rep.{0} ℂ Γ),
    Nonempty (P.complex.X q ≅ X) → ∀ A : Rep.{0} ℂ Γ, Module.rank ℂ (groupCohomology A q) ≤ Module.rank ℂ (X ⟶ A)

def RankHomPerm : Prop :=
  ∀ (Γ X : Type) [Group Γ] [MulAction Γ X], FinOrb Γ X → ∃ c : ℕ, ∀ A : Rep.{0} ℂ Γ,
    Module.rank ℂ (PC Γ X ⟶ A) ≤ c * Module.rank ℂ A

def LiftEquiv : Prop :=
  ∀ (Γ X : Type) [Group Γ] [MulAction Γ X], (∀ x : X, Finite (MulAction.stabilizer Γ x)) →
    ∀ (A B : Rep.{0} ℂ Γ) (f : A ⟶ B), Function.Surjective f.hom → ∀ φ : X → B, (∀ (g : Γ) x, φ (g • x) = B.ρ g (φ x)) →
      ∃ ψ : X → A, (∀ (g : Γ) x, ψ (g • x) = A.ρ g (ψ x)) ∧ ∀ x, f.hom (ψ x) = φ x

def ProjPerm : Prop :=
  ∀ (Γ X : Type) [Group Γ] [MulAction Γ X], (∀ x : X, Finite (MulAction.stabilizer Γ x)) → Projective (PC Γ X)

def ExactBase : Prop :=
  ∀ (X Y Z : Type) (f : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ)) (g : (Y →₀ ℤ) →ₗ[ℤ] (Z →₀ ℤ)) (f' : (X →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
    (g' : (Y →₀ ℂ) →ₗ[ℂ] (Z →₀ ℂ)),
    (∀ x y, f' (Finsupp.single x 1) y = (f (Finsupp.single x 1) y : ℤ)) →
    (∀ y z, g' (Finsupp.single y 1) z = (g (Finsupp.single y 1) z : ℤ)) → Function.Exact f g → Function.Exact f' g'

def ExactCOf : Prop := ∀ (Γ I : Type) [Group Γ] [MulAction Γ I] (K : Cx Γ I), K.ExactZ → K.ExactC

def PermSplit : Prop :=
  ∀ (n : ℕ) (j : Fin (n + 1)), ∃ e : Fin (n + 1) × Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin (n + 1)), ∀ i τ,
    ((Equiv.Perm.sign (e (i, τ)) : ℤˣ) : ℤ) = (-1) ^ (i : ℕ) * (-1) ^ (j : ℕ) * ((Equiv.Perm.sign τ : ℤˣ) : ℤ) ∧
      ∀ k, e (i, τ) (j.succAbove k) = i.succAbove (τ k)

def AltChain : Prop :=
  ∀ (Γ I : Type) [Group Γ] [MulAction Γ I] (K : Cx Γ I) (p : ℕ), K.alt (p + 1) ≫ K.d p = K.d p ≫ K.alt p

def AltZero : Prop :=
  ∀ (Γ I : Type) [Group Γ] [MulAction Γ I] (K : Cx Γ I), K.alt 0 = 𝟙 _ ∧
    ∀ p, (∀ t : K.Tup p, ¬ Function.Injective t.1) → K.alt p = 0

def DimBdd : Prop :=
  ∀ (Γ I : Type) [Group Γ] [MulAction Γ I] (K : Cx Γ I), FinOrb Γ (K.Tup 1) →
    (∀ t : K.Tup 0, Finite (MulAction.stabilizer Γ t)) →
    (∀ p (t : K.Tup p), Finite (MulAction.stabilizer Γ t)) ∧
      ∃ D : ℕ, ∀ p, D ≤ p → ∀ t : K.Tup p, ¬ Function.Injective t.1

def BddOfDeg : Prop :=
  ∀ (Γ : Type) [Group Γ], (∀ q, ∃ c : ℕ, ∀ A : Rep.{0} ℂ Γ, Module.rank ℂ (groupCohomology A q) ≤ c * Module.rank ℂ A) →
    (∃ D : ℕ, ∀ q, D ≤ q → ∀ A : Rep.{0} ℂ Γ, Module.rank ℂ (groupCohomology A q) = 0) → Bdd Γ

def BddCx : Prop :=
  ∀ (Γ I : Type) [Group Γ] [MulAction Γ I] (K : Cx Γ I), K.ExactZ → (∀ p, FinOrb Γ (K.Tup p)) →
    (∀ t : K.Tup 0, Finite (MulAction.stabilizer Γ t)) → Bdd Γ

def BddSub : Prop := ∀ (G : Type) [Group G] (S : Subgroup G), S.FiniteIndex → Bdd G → Bdd ↥S

def CoindRetract : Prop :=
  ∀ (G : Type) [Group G] (S : Subgroup G), S.FiniteIndex → ∀ A : Rep.{0} ℂ G,
    ∃ (π : A ⟶ Rep.coind S.subtype (Rep.res S.subtype A)) (ι : Rep.coind S.subtype (Rep.res S.subtype A) ⟶ A), π ≫ ι = 𝟙 A

def BddOver : Prop := ∀ (G : Type) [Group G] (S : Subgroup G), S.FiniteIndex → Bdd ↥S → Bdd G

def BddComm : Prop := ∀ (G : Type) [Group G] (Γ Λ : Subgroup G), Subgroup.Commensurable Γ Λ → Bdd ↥Λ → Bdd ↥Γ

def BddComplex : Prop := ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ), Bdd (KT.Gm L N)

def FixOrb : Prop :=
  ∀ (G Z : Type) [Group G] [MulAction G Z] (σ : G →* G) (s : Z → Z), (∀ (g : G) z, s (g • z) = σ g • s z) →
    ∀ W : Set Z, (∀ z ∈ W, s z = z) → (∀ z ∈ W, Finite (MulAction.stabilizer G z)) →
      (∃ R : Set Z, R.Finite ∧ ∀ z ∈ W, ∃ g : G, g • z ∈ R) →
      ∃ R : Set Z, R.Finite ∧ ∀ z ∈ W, ∃ g : G, σ g = g ∧ g • z ∈ R

section Real

open UpperTheory.V.KT

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

def IsConj (σ : 𝓞 L →+* 𝓞 L) : Prop := ∀ (w : InfinitePlace L) (x : 𝓞 L), embO w (σ x) = starRingEnd ℂ (embO w x)

def HR : Submodule ℝ (HS L N) where
  carrier := {h | ∀ w i j, (mat h w i j).im = 0}
  add_mem' := fun {a b} ha hb w i j => by
    rw [mat_add, Matrix.add_apply, Complex.add_im, ha w i j, hb w i j, add_zero]
  zero_mem' := fun w i j => by simp
  smul_mem' := fun c h hh w i j => by
    rw [mat_smul, Matrix.smul_apply, Complex.smul_im, hh w i j, smul_zero]

def qr (y : NZ L N) : ↥(HR L N) →L[ℝ] ℝ := (qc L N y).comp (HR L N).subtypeL

def Tr : Set ↥(HR L N) := {h | h.1 ∈ Psd L N}

variable {L N}

@[simp] theorem qr_apply (y : NZ L N) (h : ↥(HR L N)) : qr L N y h = q h.1 y.1 := rfl

def sLat (σ : 𝓞 L →+* 𝓞 L) (y : Lat L N) : Lat L N := fun a => σ (y a)

variable (N) in

def sGm (σ : 𝓞 L →+* 𝓞 L) : Gm L N →* Gm L N := Matrix.GeneralLinearGroup.map σ

variable (N) in

def Fix (σ : 𝓞 L →+* 𝓞 L) : Subgroup (Gm L N) := (sGm N σ).eqLocus (MonoidHom.id _)

theorem mem_Fix {σ : 𝓞 L →+* 𝓞 L} {g : Gm L N} : g ∈ Fix N σ ↔ sGm N σ g = g := Iff.rfl

theorem sLat_smul (σ : 𝓞 L →+* 𝓞 L) (g : Gm L N) (y : Lat L N) : sLat σ (g • y) = sGm N σ g • sLat σ y := by
  funext a
  simp [sLat, sGm, smul_lat, Matrix.mulVec, dotProduct]

end Real

open UpperTheory.V.KT

def RePart : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ → ∀ k : HS L N,
    ∃ k' : ↥(HR L N), (∀ y, q k'.1 y = (q k y + q k (sLat σ y)) / 2) ∧
      (k ∈ Psd L N → k'.1 ∈ Psd L N ∧ (k' = 0 → k = 0))

def ReInv : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ → (∀ x, σ (σ x) = x) ∧
    ∀ h ∈ HR L N, (∀ y, q h (sLat σ y) = q h y) ∧ ∀ g ∈ Fix N σ, g • h ∈ HR L N

def GoodRe : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ →
    ConeExtensionAcyclic.Good (qr L N) (Tr L N)

def ActRe : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ →
    ∃ _ : MulAction ↥(Fix N σ) (ConeExtensionAcyclic.Vert (qr L N)),
      (∀ (g : ↥(Fix N σ)) (v : ConeExtensionAcyclic.Vert (qr L N)), (g • v).1.1 = g.1 • v.1.1) ∧
      ∀ (n : ℕ) (g : ↥(Fix N σ)) (t : Fin n → ConeExtensionAcyclic.Vert (qr L N)), t ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) n →
        (fun j => g • t j) ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) n

def SpanRe : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ →
    ∀ (p : ℕ), ∀ t ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) (p + 1), Spans {y : Lat L N | ∀ j, q (t j).1.1 y = 1}

open Pointwise in

def MinOrb : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N p : ℕ), ∃ R : Set (Fin (p + 1) → Set (Lat L N)), R.Finite ∧
    ∀ h : Fin (p + 1) → HS L N, (∀ j, h j ∈ Ry L N) → Spans {y : Lat L N | ∀ j, q (h j) y = 1} →
      ∃ g : Gm L N, g • (fun j => minVec (h j)) ∈ R

open Pointwise in

def MinStab : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ), ∀ h ∈ Ry L N, Spans (minVec h) →
    Finite (MulAction.stabilizer (Gm L N) (minVec h))

def OrbRe : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ → ∀ p : ℕ,
    ∃ R : Set (Fin (p + 1) → HS L N), R.Finite ∧ ∀ t ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) (p + 1),
      ∃ g ∈ Fix N σ, (fun j => g • (t j).1.1) ∈ R

def BddFix : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ → Bdd ↥(Fix N σ)

def ExCM : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (L : Type) (_ : Field L) (_ : NumberField L)
    (_ : IsTotallyComplex L) (i : F →+* L) (s : L →+* L), (∀ (φ : L →+* ℂ) x, φ (s x) = starRingEnd ℂ (φ x)) ∧
      ∀ x : L, s x = x ↔ x ∈ i.range

def ExCMInt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (L : Type) (_ : Field L) (_ : NumberField L)
    (_ : IsTotallyComplex L) (i : 𝓞 F →+* 𝓞 L) (σ : 𝓞 L →+* 𝓞 L), IsConj L σ ∧ Function.Injective i ∧
      ∀ x : 𝓞 L, σ x = x ↔ x ∈ i.range

def FixEquiv : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] (i : A →+* B) (σ : B →+* B) (N : ℕ), Function.Injective i →
    (∀ x : B, σ x = x ↔ x ∈ i.range) →
    Nonempty (↥((Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _)) ≃* GL (Fin N) A)

end UpperTheory.V.Af.BA
