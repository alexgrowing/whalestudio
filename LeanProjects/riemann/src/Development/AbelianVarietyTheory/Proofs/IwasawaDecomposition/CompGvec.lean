import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl

section Lin

abbrev GVar (m a k b : ℕ) : Type :=
  {il : Fin m × Fin m // a ≤ (il.2 : ℕ) ∧ (il.2 : ℕ) < k ∧ k ≤ (il.1 : ℕ) ∧ (il.1 : ℕ) < b}

abbrev GPm (m a b : ℕ) : Type := {w : Equiv.Perm (Fin m) // ∀ i : Fin m, (i : ℕ) < a ∨ b ≤ (i : ℕ) → w i = i}

variable {S : Type} [CommRing S] {m a k b N : ℕ}

def gcell (x : GVar m a k b → S) (i l : Fin m) : S :=
  if h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b then x ⟨(i, l), h⟩ else if i = l then 1 else 0

def gvec {Q : Type} [AddCommGroup Q] [Module S Q] (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) : Fin m → Q :=
  fun l => ∑ i, gcell x i l • c (w.1 i)

theorem map_gcell {S' : Type} [CommRing S'] (φ : S →+* S') (x : GVar m a k b → S) (i l : Fin m) :
    φ (gcell x i l) = gcell (φ ∘ x) i l := by
  unfold gcell
  split_ifs <;> simp

theorem map_gvec {S' : Type} [CommRing S'] {φ : S →+* S'} {Q Q' : Type} [AddCommGroup Q] [Module S Q] [AddCommGroup Q']
    [Module S' Q'] (F : Q →ₛₗ[φ] Q') (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (l : Fin m) :
    F (gvec c w x l) = gvec (fun i => F (c i)) w (φ ∘ x) l := by
  simp only [gvec, map_sum, map_smulₛₗ, map_gcell]

theorem comp_gvec {S' : Type} [CommRing S'] (φ : S →+* S') {ι : Type} (c : Fin m → ι → S) (w : GPm m a b)
    (x : GVar m a k b → S) (l : Fin m) : φ ∘ gvec c w x l = gvec (fun i => φ ∘ c i) w (φ ∘ x) l := by
  funext r
  simp only [gvec, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, map_gcell]

variable (a b) in

def gxi (hk : k ≤ m) (c : Fin m → Fin (N + 1) → S) (w : GPm m a b) :
    Fin (plN N k + 1) → MvPolynomial (GVar m a k b) S :=
  plk (gvec (fun l => (MvPolynomial.C : S →+* MvPolynomial (GVar m a k b) S) ∘ c l) w
    (MvPolynomial.X : GVar m a k b → MvPolynomial (GVar m a k b) S)) (Fin.castLE hk)

variable (a b) in

def gell (hk : k ≤ m) (D : Fin m → Fin (N + 1) → S) (w : GPm m a b) : Fin (plN N k + 1) → S :=
  lform D (w.1 ∘ Fin.castLE hk)

structure Cells {R : Type} [CommRing R] (ρ : R →+* S) {J : Type} (ξ : J → Fin (N + 1) → S) (ℓ : J → Fin (N + 1) → R) :
    Prop where
  one : ∀ j, ∑ q, ρ (ℓ j q) * ξ j q = 1
  gen : ∀ j, Function.Surjective (MvPolynomial.eval₂Hom ρ (ξ j))
  ovl : ∀ (K : Type) [Field K] (j j' : J) (ψ' : S →+* K), ∑ q, ψ' (ρ (ℓ j q)) * ψ' (ξ j' q) ≠ 0 →
    ∃ (ψ : S →+* K) (u : Kˣ), ψ.comp ρ = ψ'.comp ρ ∧ ψ' ∘ ξ j' = (u : K) • (ψ ∘ ξ j)
  lin : ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → J) (e : T → R),
    ∀ j', ξ j' q = ∑ t, ρ (e t) * ∑ q', ρ (ℓ (jj t) q') * ξ j' q'

example (R : Type) [CommRing R] : Cells (N := 0) (RingHom.id R) (fun _ : Unit => fun _ => 1) fun _ _ => 1 :=
  ⟨by simp, fun _ r => ⟨MvPolynomial.C r, by simp⟩, fun _ _ _ _ ψ _ => ⟨ψ, 1, rfl, by simp⟩,
    fun _ => ⟨Unit, inferInstance, id, fun _ => 1, by simp⟩⟩

end Lin

section Geom

variable {O : Type} [CommRing O] {Z Z' : Scheme.{0}}

def Lifts (s : Z ⟶ Sp O) {N : ℕ} (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (z : Sp R ⟶ Z) (y₀ : Sp R ⟶ PSpace O N) (y : Sp K ⟶ Z'), y₀ ≫ PSpace.str O N = z ≫ s →
    y ≫ f = spMap (algebraMap R K) ≫ z → y ≫ q = spMap (algebraMap R K) ≫ y₀ →
    ∃ z' : Sp R ⟶ Z', spMap (algebraMap R K) ≫ z' = y

structure CellCl (s : Z ⟶ Sp O) (ch : Charts Z) (g : ∀ a, O →+* ch.R a) {V J : Type} {N : ℕ}
    (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N)
    (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')) : Prop where
  proj : IsProjOver (f ≫ s)
  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z'
  flat : Flat (f ≫ s)
  ovr : q ≫ PSpace.str O N = f ≫ s
  opn : ∀ a j, IsOpenImmersion (κ a j)
  sq : ∀ a j, κ a j ≫ f = spMap (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) ≫ ch.χ a
  pl : ∀ a j, ∃ hv, κ a j ≫ q = pt ((MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)).comp (g a)) (ξ a j) hv
  cover : ⋃ a, ⋃ j, Set.range (κ a j) = f ⁻¹' ch.carrier
  dense : Dense (f ⁻¹' ch.carrier)
  inj : ∀ (K : Type) [Field K] (w w' : Sp K ⟶ Z'), Set.range (w ≫ f) ⊆ ch.carrier → w ≫ f = w' ≫ f → w ≫ q = w' ≫ q →
    w = w'
  lift : Lifts s f q

variable {C : Coc Z} {N k : ℕ} (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k))

def Car {K : Type} [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K) : Prop :=
  ∃ (g : O →+* K) (hv : _), w ≫ q = pt g (plk (fun l => ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (ξ l)) id) hv

def Planar : Prop :=
  ∀ x : Z', ∃ (U : Z'.Opens) (_ : IsAffineOpen U) (α : C.A) (a : GL (Fin (C.n α)) Γ(Z', U)), x ∈ U ∧ U ≤ f ⁻¹ᵁ C.B α ∧
    ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K),
      Car Em f q w α h ξ → ∀ (l : Fin k) (j : Fin (C.n α)), k ≤ (j : ℕ) → ∑ i, ev w U hw (a j i) * ξ l i = 0

end Geom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Crd

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}

structure LCrd (M : Model Xo c V.subtype) {X : Scheme.{0}} (π : X ⟶ M.X) : Type 1 where
  C : Coc X
  N : ℕ
  Em : C.Emb N
  crd : ∀ (α : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X), ⊤ ≤ z ⁻¹ᵁ C.B α →
    (TanM (z ≫ π) M.t.G →ₗ[S] (Fin (C.n α) → S))
  tr : ∀ (α β : C.A) (S : Type) [CommRing S] (z : Sp S ⟶ X) (hα : ⊤ ≤ z ⁻¹ᵁ C.B α) (hβ : ⊤ ≤ z ⁻¹ᵁ C.B β)
    (v : TanM (z ≫ π) M.t.G), (C.tr α β z hα hβ).mulVec (crd β S z hβ v) = crd α S z hα v
  bc : ∀ (α : C.A) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ X) (z' : Sp S' ⟶ X)
    (_ : spMap φ ≫ z = z') (h : ⊤ ≤ z ⁻¹ᵁ C.B α) (h' : ⊤ ≤ z' ⁻¹ᵁ C.B α) (e : spMap φ ≫ z ≫ π = z' ≫ π)
    (v : TanM (z ≫ π) M.t.G), crd α S' z' h' (tanPull φ e v) = φ ∘ crd α S z h v
  inj : ∀ (α : C.A) (K : Type) [Field K] (z : Sp K ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ C.B α),
    Set.range z ⊆ π ⁻¹' Set.range M.j → Function.Injective (crd α K z h)

variable {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

def LCrd.emb (D : LCrd M π) (α : D.C.A) {S : Type} [CommRing S] (z : Sp S ⟶ X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α)
    (v : TanM (z ≫ π) M.t.G) : Fin (D.N + 1) → S := ((D.Em.A α).map (ev z _ h)).mulVec (D.crd α S z h v)

def IsFrVec (D : LCrd M π) (A : Atlas M π ty) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A)
    (cv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a) : Prop :=
  ∀ (a : A.ch.ι) (S : Type) [CommRing S] (φ : A.ch.R a →+* S) (z : Sp S ⟶ X), spMap φ ≫ A.ch.χ a = z →
    ∀ (h : ⊤ ≤ z ⁻¹ᵁ D.C.B (α a)) (u : TVecs Dw M.t (z ≫ π)), up u = (A.fr a).bc φ →
      ∀ i, φ ∘ cv a i = D.emb (α a) z h (u σ i)

def GRel (D : LCrd M π) (A : Atlas M π ty) (σ : E →+* ℂ) {k : ℕ} (hk : k ≤ Dw.mult σ) {X' : Scheme.{0}} (f : X' ⟶ X)
    (q : X' ⟶ PSpace V (plN D.N k)) {ty' : (E →+* ℂ) → Finset ℕ} (A' : Atlas M (f ≫ π) ty') : Prop :=
  ∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : TVecs Dw M.t ((w ≫ f) ≫ π)),
    A'.FlagAt w (up u) ↔ A.FlagAt (w ≫ f) (up u) ∧
      ∀ α h, Car D.Em f q w α h fun i => D.crd α K (w ≫ f) h (u σ (Fin.castLE hk i))

end Crd

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def IsLat (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π) : Prop :=
  ∀ α : D.C.A, ∃ (V : t.B.X.Opens) (m : Fin (D.C.n α) → Γ(t.L.N.toMod, V)), D.C.B α ≤ g ⁻¹ᵁ V ∧ VB.IsFrame m ∧
    ∀ (τ : (Y Z.i).X ⟶ (Y t.B.i).X) (mu : SABMap (Y Z.i).t (Y t.B.i).t τ), LocM.IsTrans t.B.i Z.i τ mu →
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Z.X) (h : ⊤ ≤ z ⁻¹ᵁ D.C.B α), Set.range z ⊆ Z.opn →
        ∀ (v : TanM (z ≫ Z.π) (Y Z.i).t.G) (v' : Sp (DualNumber K) ⟶ t.B.t.G.left) (hv' : IsTanAtG t.B.t (z ≫ g) v')
          (h' : ⊤ ≤ (z ≫ g) ⁻¹ᵁ V), v' ≫ t.B.tMap.φ = (tv v).left ≫ mu.φ →
          ∀ l, D.crd α K z h v l = tanEv t.B.t hv' h' (t.L.N.incl.app V (m l))

end GlobalTheory.GrCl
