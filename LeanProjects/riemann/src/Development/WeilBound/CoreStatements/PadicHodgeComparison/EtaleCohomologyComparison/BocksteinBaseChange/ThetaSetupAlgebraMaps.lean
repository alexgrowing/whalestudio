import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GlobalTheory.LogCris

namespace CrystallineSemistableComparison

structure Per (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Type 1 where
  A : Type
  B : Type
  [ringA : CommRing A]
  [fieldB : Field B]
  i : A →+* B
  t : A
  z : ℤ_[l] →+* A
  φ : A →+* A
  σA : K.fixingSubgroup → A →+* A
  σ : K.fixingSubgroup → B →+* B
  q : ℚ_[l] →+* B
  o : K →+* B
  P : Subring B

attribute [instance] Per.ringA Per.fieldB

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Per

variable (R : Per l K)

def tB : R.B := R.i R.t

def IsU (x : R.B) : Prop := x ∈ R.P ∧ ∃ y ∈ R.P, x * y = 1

structure Facts : Prop where
  i_σ : ∀ (g : K.fixingSubgroup) (a : R.A), R.i (R.σA g a) = R.σ g (R.i a)
  thetaSetup_structureMap_comp : ∀ z : ℤ_[l], R.i (R.z z) = R.q z
  frobenius_period : R.φ R.t = (l : R.A) * R.t
  t_ne : R.tB ≠ 0
  t_mem : R.tB ∈ R.P
  q_mem : ∀ z, R.q z ∈ R.P
  o_mem : ∀ k : K, R.o k ∈ R.P
  σ_q : ∀ (g : K.fixingSubgroup) (z : ℚ_[l]), R.σ g (R.q z) = R.q z
  σ_mem : ∀ (g : K.fixingSubgroup) (x : R.B), x ∈ R.P → R.σ g x ∈ R.P
  galois_t_transform : ∀ g : K.fixingSubgroup, ∃ u, R.IsU u ∧ R.σ g R.tB = u * R.tB
  loc : ∀ x ∈ R.P, ∀ y ∈ R.P, R.IsU (x + y) → R.IsU x ∨ R.IsU y

structure Reg (S : Subring R.B) : Prop where
  q_mem : ∀ z, R.q z ∈ S
  stab : ∀ (g : K.fixingSubgroup), ∀ x ∈ S, R.σ g x ∈ S
  frac : ∀ x ∈ S, ∀ y ∈ S, ∀ w : R.B, w * y = x → y ≠ 0 → (∀ g, R.σ g w = w) → w ∈ S
  eig : ∀ x ∈ S, x ≠ 0 → (∀ g, ∃ z : ℚ_[l], R.σ g x = R.q z * x) → ∃ y ∈ S, x * y = 1

def admitted (S : Subring R.B) {d : ℕ} (r : K.fixingSubgroup → Matrix (Fin d) (Fin d) ℚ_[l]) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) R.B, (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧ ∀ g, (r g).map R.q * P.map (R.σ g) = P

end Per

def IsPow {N : ℕ → Type 1} (o : N 0 → Prop) (c : ∀ {i j : ℕ}, N i → N j → N (i + j) → Prop) (x : N 2) :
    ∀ k : ℕ, N (2 * k) → Prop
  | 0, z => o z
  | k + 1, z => ∃ y : N (2 * k), IsPow o c x k y ∧ c y x z

structure GMod (R : Type) [CommRing R] (Γ : Type) : Type 2 where
  N : ℕ → Type 1
  [ab : ∀ j, AddCommGroup (N j)]
  [md : ∀ j, Module R (N j)]
  act : ∀ j, Γ → N j →+ N j

attribute [instance] GMod.ab GMod.md

structure GAlg (R : Type) [CommRing R] (Γ : Type) : Type 2 extends GMod R Γ where
  one : N 0 → Prop
  cup : ∀ {i j : ℕ}, N i → N j → N (i + j) → Prop

structure Dat (R : Per l K) : Type 2 where
  Ch : Model l K → Type 1
  Mo : ∀ {M N : Model l K} (u : M.X ⟶ N.X), u ≫ N.p = M.p → Ch M → Ch N → Type 1
  A : ∀ {M : Model l K}, Ch M → GAlg R.A K.fixingSubgroup
  phiA : ∀ {M : Model l K} (a : Ch M) (j : ℕ), (A a).N j →+ (A a).N j
  pullA : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : Ch M} {b : Ch N}, Mo u hu a b →
    ∀ j, (A b).N j →ₗ[R.A] (A a).N j
  c1A : ∀ {M : Model l K} (a : Ch M), (A a).N 2 → Prop
  H : ∀ {M : Model l K}, Ch M → GAlg R.A K.fixingSubgroup
  fil : ∀ {M : Model l K} (a : Ch M) (j : ℕ), ℕ → (H a).N j → Prop
  c1H : ∀ {M : Model l K} (a : Ch M), (H a).N 2 → Prop
  pullH : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : Ch M} {b : Ch N}, Mo u hu a b →
    ∀ j, (H b).N j →+ (H a).N j
  H' : ∀ {M : Model l K}, Ch M → GMod R.A K.fixingSubgroup
  phi' : ∀ {M : Model l K} (a : Ch M) (j : ℕ), (H' a).N j →+ (H' a).N j

variable {R : Per l K} (G : Model l K → Prop)

structure Dat.Laws (D : Dat R) : Prop where
  ch : ∀ (M : Model l K), G M → Nonempty (D.Ch M)
  refine : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p), G M → G N → ∀ (a : D.Ch M) (b : D.Ch N),
    ∃ a' : D.Ch M, Nonempty (D.Mo (𝟙 M.X) (Category.id_comp _) a' a) ∧ Nonempty (D.Mo u hu a' b)
  act_smul : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ) (σ : K.fixingSubgroup) (c : R.A) (y : (D.A a).N j),
    (D.A a).act j σ (c • y) = R.σA σ c • (D.A a).act j σ y
  phi_smul : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ) (c : R.A) (y : (D.A a).N j), D.phiA a j (c • y) = R.φ c • D.phiA a j y
  one_uniq : ∀ {M : Model l K} (a : D.Ch M) (x y : (D.A a).N 0), (D.A a).one x → (D.A a).one y → x = y
  cup_uniq : ∀ {M : Model l K} (a : D.Ch M) {i j : ℕ} (x : (D.A a).N i) (y : (D.A a).N j) (z z' : (D.A a).N (i + j)),
    (D.A a).cup x y z → (D.A a).cup x y z' → z = z'
  cup_smul : ∀ {M : Model l K} (a : D.Ch M) {i j : ℕ} (c c' : R.A) (x : (D.A a).N i) (y : (D.A a).N j) (z : (D.A a).N (i + j)),
    (D.A a).cup x y z → (D.A a).cup (c • x) (c' • y) ((c * c') • z)
  first_chern_class_unique : ∀ {M : Model l K} (a : D.Ch M) (x y : (D.A a).N 2), D.c1A a x → D.c1A a y → x = y
  cup_ex : ∀ {M : Model l K} (a : D.Ch M) {i j : ℕ} (x : (D.H a).N i) (y : (D.H a).N j), ∃ z, (D.H a).cup x y z

structure EMap (D : Dat R) where
  e : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), M.T j →+ (D.A a).N j
  lin : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (z : ℤ_[l]) (v : M.T j), e a j (z • v) = R.z z • e a j v
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (v : M.T j),
    e a j (M.actT j σ v) = (D.A a).act j σ (e a j v)
  phi : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (v : M.T j), D.phiA a j (e a j v) = e a j v
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (m : D.Mo u hu a b),
    G M → G N → ∀ (j : ℕ) (v : N.T j), e a j (Model.pullT u hu j v) = D.pullA m j (e b j v)
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)), M.CupT x y z →
    (D.A a).cup (e a i x) (e a j y) (e a (i + j) z)
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∃ v, (D.A a).one (e a 0 v)
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∃ v : M.T 2, D.c1A a (R.t • e a 2 v)

structure BMap (D : Dat R) where
  β : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H a).N j →ₗ[R.A] (D.A a).N j
  β' : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H' a).N j →ₗ[R.A] (D.A a).N j
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : (D.H a).N j),
    β a j ((D.H a).act j σ x) = (D.A a).act j σ (β a j x)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (m : D.Mo u hu a b),
    G M → G N → ∀ (j : ℕ) (x : (D.H b).N j), β a j (D.pullH m j x) = D.pullA m j (β b j x)
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H a).N i) (y : (D.H a).N j) (z : (D.H a).N (i + j)),
    (D.H a).cup x y z → (D.A a).cup (β a i x) (β a j y) (β a (i + j) z)
  one : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x, (D.H a).one x → (D.A a).one (β a 0 x)
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ x, D.c1H a x → D.c1A a (β a 2 x)
  inj : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j : ℕ, ∃ n : ℕ, ∀ x, β a j x = 0 → R.t ^ n • x = 0
  surj : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j : ℕ, ∃ n : ℕ, ∀ y, ∃ x, D.fil a j n x ∧ β a j x = R.t ^ n • y
  act' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : (D.H' a).N j),
    β' a j ((D.H' a).act j σ x) = (D.A a).act j σ (β' a j x)
  phi' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (x : (D.H' a).N j),
    β' a j (D.phi' a j x) = D.phiA a j (β' a j x)
  surj' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j : ℕ, ∃ n : ℕ, ∀ y, ∃ x, β' a j x = R.t ^ n • y

structure PMap (D : Dat R) where
  κ : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.B)
  cupR : ∀ (M : Model l K) (i j : ℕ), HdR M.q i →ₗ[K] HdR M.q j →ₗ[K] HdR M.q (i + j)
  fin : ∀ (M : Model l K), G M → ∀ j : ℕ, FiniteDimensional K (HdR M.q j) ∧ ∀ x ∈ FilR M.q j (j + 1), x = 0
  top : ∀ (M : Model l K), G M → ∀ d : ℕ, M.Conn d → ∀ j : ℕ, ∀ x ∈ FilR M.q j (d + 1), x = 0
  cupR_fil : ∀ (M : Model l K), G M → ∀ (i j r s : ℕ), ∀ x ∈ FilR M.q i r, ∀ y ∈ FilR M.q j s,
    cupR M i j x y ∈ FilR M.q (i + j) (r + s)
  lin : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (c : R.A) (x : (D.H a).N j) (φ : Module.Dual K (HdR M.q j)),
    κ a j (c • x) φ = R.i c * κ a j x φ
  lin' : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (k : K) (x : (D.H a).N j) (φ : Module.Dual K (HdR M.q j)),
    κ a j x (k • φ) = R.o k * κ a j x φ
  act : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j : ℕ) (σ : K.fixingSubgroup) (x : (D.H a).N j)
    (φ : Module.Dual K (HdR M.q j)), κ a j ((D.H a).act j σ x) φ = R.σ σ (κ a j x φ)
  nat : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N} (m : D.Mo u hu a b),
    G M → G N → ∀ (j : ℕ) (x : (D.H b).N j) (φ : Module.Dual K (HdR M.q j)),
    κ a j (D.pullH m j x) φ = κ b j x (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu))
  fil : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ (j n r : ℕ) (x : (D.H a).N j) (φ : Module.Dual K (HdR M.q j)),
    D.fil a j n x → (∀ h ∈ FilR M.q j (r + 1), φ h = 0) → ∃ y ∈ R.P, R.tB ^ r * κ a j x φ = R.tB ^ n * y
  cup : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ {i j : ℕ} (x : (D.H a).N i) (y : (D.H a).N j) (z : (D.H a).N (i + j)),
    (D.H a).cup x y z → ∀ {m m' : ℕ} (b : Module.Basis (Fin m) K (HdR M.q i)) (b' : Module.Basis (Fin m') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      κ a (i + j) z φ = ∑ s, ∑ s', κ a i x (b.coord s) * κ a j y (b'.coord s') * R.o (φ (cupR M i j (b s) (b' s')))
  c1 : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ d : ℕ, M.Conn d →
    ∃ x z φ, D.c1H a x ∧ IsPow (N := (D.H a).N) (D.H a).one (D.H a).cup x d z ∧ R.IsU (κ a (2 * d) z φ)

def GMod.Fn (R : Per l K) (H : GMod R.A K.fixingSubgroup) (j : ℕ) (f : H.N j →+ R.B) : Prop :=
  (∀ (c : R.A) x, f (c • x) = R.i c * f x) ∧ ∀ (σ : K.fixingSubgroup) x, f (H.act j σ x) = R.σ σ (f x)

def GMod.Span (R : Per l K) (H : GMod R.A K.fixingSubgroup) (j : ℕ) (φ : H.N j →+ H.N j) (S : Subring R.B) : Prop :=
  ∃ (k r : ℕ) (w : Fin r → (H.N j →+ R.B) → R.B),
    (∀ f, GMod.Fn R H j f → ∀ (i : Fin r) (σ : K.fixingSubgroup), R.σ σ (w i f) = w i f) ∧
    ∀ x, ∃ b : Fin r → R.B, (∀ i, b i ∈ S) ∧ ∀ f, GMod.Fn R H j f → f (φ^[k] x) = ∑ i, b i * w i f

def Dat.Span (D : Dat R) (S : Subring R.B) : Prop :=
  ∀ (M : Model l K), G M → ∀ (a : D.Ch M) (j : ℕ), GMod.Span R (D.H' a) j (D.phi' a j) S

structure Pre (R : Per l K) where
  c : ∀ (M : Model l K) (n : ℕ), M.V n →+ (Module.Dual K (HdR M.q n) →+ R.B)
  cupR : ∀ (M : Model l K) (i j : ℕ), HdR M.q i →ₗ[K] HdR M.q j →ₗ[K] HdR M.q (i + j)
  lin : ∀ (M : Model l K) (n : ℕ) (z : ℚ_[l]) (v : M.V n) (φ : Module.Dual K (HdR M.q n)), c M n (z • v) φ = R.q z * c M n v φ
  lin' : ∀ (M : Model l K) (n : ℕ) (k : K) (v : M.V n) (φ : Module.Dual K (HdR M.q n)), c M n v (k • φ) = R.o k * c M n v φ
  fin : ∀ (M : Model l K), G M → ∀ j : ℕ, FiniteDimensional K (HdR M.q j) ∧ ∀ x ∈ FilR M.q j (j + 1), x = 0
  top : ∀ (M : Model l K), G M → ∀ d : ℕ, M.Conn d → ∀ j : ℕ, ∀ x ∈ FilR M.q j (d + 1), x = 0
  cupR_fil : ∀ (M : Model l K), G M → ∀ (i j r s : ℕ), ∀ x ∈ FilR M.q i r, ∀ y ∈ FilR M.q j s,
    cupR M i j x y ∈ FilR M.q (i + j) (r + s)
  equi : ∀ (M : Model l K) (n : ℕ), G M → ∀ (σ : K.fixingSubgroup) (v : M.V n) (φ : Module.Dual K (HdR M.q n)),
    c M n (M.act n σ v) φ = R.σ σ (c M n v φ)
  fil : ∀ (M : Model l K) (n : ℕ), G M → ∀ (r : ℕ) (v : M.V n) (φ : Module.Dual K (HdR M.q n)),
    (∀ x ∈ FilR M.q n (r + 1), φ x = 0) → R.tB ^ r * c M n v φ ∈ R.P
  nat : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n : ℕ), G M → G N →
    ∀ (v : N.V n) (φ : Module.Dual K (HdR M.q n)),
    c M n (Model.pullV u hu n v) φ = c N n v (φ ∘ₗ pullR n (Model.genMap u hu) (Model.genMap_q u hu))
  cup : ∀ (M : Model l K), G M → ∀ {i j : ℕ} (x : M.T i) (y : M.T j) (z : M.T (i + j)), M.CupT x y z →
    ∀ {m m' : ℕ} (b : Module.Basis (Fin m) K (HdR M.q i)) (b' : Module.Basis (Fin m') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      c M (i + j) (M.toV _ z) φ =
        ∑ s, ∑ s', c M i (M.toV _ x) (b.coord s) * c M j (M.toV _ y) (b'.coord s') * R.o (φ (cupR M i j (b s) (b' s')))
  c1 : ∀ (M : Model l K), G M → ∀ d : ℕ, M.Conn d → ∃ v φ, R.IsU (R.tB ^ d * c M (2 * d) v φ)

variable {G} in

def Pre.Span (P : Pre G R) (M : Model l K) (n : ℕ) (S : Subring R.B) : Prop :=
  ∃ (r : ℕ) (w : Fin r → Module.Dual K (HdR M.q n) → R.B), (∀ i φ (σ : K.fixingSubgroup), R.σ σ (w i φ) = w i φ) ∧
    ∀ v, ∃ b : Fin r → R.B, (∀ i, b i ∈ S) ∧ ∀ φ, P.c M n v φ = ∑ i, b i * w i φ

variable {G} in

def Pre.Inj (P : Pre G R) (M : Model l K) (n : ℕ) : Prop :=
  ∀ {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → R.B), (∀ φ, ∑ i, z i * P.c M n (b i) φ = 0) → z = 0

variable {G} in

def Pre.Strict (P : Pre G R) (M : Model l K) (n : ℕ) : Prop :=
  ∀ {a : ℕ} (b : Module.Basis (Fin a) ℚ_[l] (M.V n)) (z : Fin a → R.B),
    (∀ (r : ℕ) (φ : Module.Dual K (HdR M.q n)), (∀ x ∈ FilR M.q n (r + 1), φ x = 0) →
      R.tB ^ r * ∑ i, z i * P.c M n (b i) φ ∈ R.P) → ∀ i, z i ∈ R.P

end CrystallineSemistableComparison
