import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out Classical
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

structure Clos (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) where
  u₀ : U₀.toScheme ⟶ Sp S.R
  u₀_pt : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap S.R.val.toRingHom
  P : Over M.Z
  [intP : IsIntegral P.left]
  proper : IsProper P.hom
  proj : IsProjOver (P.hom ≫ M.s)
  a₀ : pullback ρ.P.A.hom u₀ ⟶ P.left
  cart : IsPullback a₀ (pullback.snd ρ.P.A.hom u₀) P.hom U₀.ι
  O1 : LB P.left
  isLB : O1.IsLB
  st : S.J → O1.Sec
  crd : ∀ (K : Type) [Field K] (x : Sp K ⟶ pullback ρ.P.A.hom u₀) (v : S.J → K),
    ρ.Crd (x ≫ pullback.fst _ _) v → Crd O1 st (x ≫ a₀) v
  Λ : Type
  W : Λ → M.Z.Opens
  aff : ∀ l, IsAffineOpen (W l)
  ne : ∀ l, (W l : Set M.Z).Nonempty
  cover : ⨆ l, W l = ⊤
  B : Λ → Matrix S.J S.J Ω
  basis : ∀ l, ∀ z ∈ W l, EE.E z = Submodule.span (M.O z) (Set.range (B l))
  c : ∀ l, Matrix S.J S.J Γ(M.Z, W l)
  c_inv : ∀ l, (c l).map (valF M.pt (W l)) * B l = 1
  σ : ∀ l, S.J → (O1.pull (P.hom ⁻¹ᵁ W l).ι).Sec
  rel : ∀ l (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ (P.hom ⁻¹ᵁ W l).toScheme) (w : S.J → R),
    Crd (O1.pull (P.hom ⁻¹ᵁ W l).ι) (σ l) x w →
    Crd O1 st (x ≫ (P.hom ⁻¹ᵁ W l).ι) (((c l).map (valR (x ≫ (P.hom ⁻¹ᵁ W l).ι ≫ P.hom) (W l))).mulVec w)
  imm : ∀ l, ImmBy (k := Γ(M.Z, W l)) ((P.hom ∣_ W l) ≫ (aff l).isoSpec.hom) (O1.pull (P.hom ⁻¹ᵁ W l).ι) (σ l) Set.univ
attribute [instance] Clos.intP
namespace Clos
variable {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Q : Clos ρ M U₀ EE)

def G : Q.P.left.Opens :=
  ⨆ (z : M.Z) (_ : IsClosed ({z} : Set M.Z)) (W : M.Z.Opens) (_ : ∀ z' ∈ W, S.supI M z ⊆ S.supI M z') (i : S.J)
    (φ : Q.O1.Sec) (_ : IsLin (Q.P.hom ≫ M.s) Q.st (fun j => S.proj (S.TT M z) 0 j i) φ),
    Q.P.hom ⁻¹ᵁ W ⊓ nonzeroLocus φ

structure Ext where
  π : M.Z ⟶ Sp ℤ
  flat : Flat π
  lft : LocallyOfFiniteType π
  qc : QuasiCompact π
  sep : IsSeparated π
  normal : IsNormalScheme M.Z
  ne : (U₀ : Set M.Z).Nonempty
  ab : IsAbelianScheme ((Over.pullback Q.u₀).obj ρ.P.A)
  dim : SmoothOfRelativeDimension S.g ((Over.pullback Q.u₀).obj ρ.P.A).hom
  a : pullback ρ.P.A.hom Q.u₀ ⟶ Q.G.toScheme
  a_eq : a ≫ Q.G.ι = Q.a₀
  e : M.Z ⟶ Q.G.toScheme
  e_sec : e ≫ Q.G.ι ≫ Q.P.hom = 𝟙 M.Z
  e_zero : U₀.ι ≫ e = (eSec ((Over.pullback Q.u₀).obj ρ.P.A) ≫ a : U₀.toScheme ⟶ Q.G.toScheme)

def Ext.core {Q : Clos ρ M U₀ EE} (x : Q.Ext) : GlobalTheory.ZJ.Core where
  Z := M.Z
  π := x.π
  flat := x.flat
  lft := x.lft
  qc := x.qc
  sep := x.sep
  normal := x.normal
  U := U₀
  ne := x.ne
  g := S.g
  A := (Over.pullback Q.u₀).obj ρ.P.A
  comm := x.ab.comm
  ab := x.ab
  dim := x.dim
  P := Q.P
  proper := Q.proper
  G := Q.G
  a := x.a
  cart := by have := Q.cart; rw [← x.a_eq] at this; exact this
  e := x.e
  e_sec := x.e_sec
  e_zero := x.e_zero

def Tors {K : Type} [Field K] (t : Sp K ⟶ M.Z) (l : Q.Λ) : Set (S.J → K) :=
  {w | ∃ z ∈ Set.range t, ∃ x₀ ∈ S.supI M z, ∃ h ∈ S.HH M z, w = fun i => M.val t ((Q.B l i ⬝ᵥ S.ev h) / S.th x₀)}

def InFib {K : Type} [Field K] (x : Sp K ⟶ Q.P.left) : Prop :=
  ∀ (l : Q.Λ) (x' : Sp K ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (w : S.J → K), x' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι = x →
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x' w → ∀ (d : ℕ) (Pf : MvPolynomial S.J K),
      d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
      (∀ v ∈ Q.Tors (x ≫ Q.P.hom) l, MvPolynomial.eval v Pf = 0) → MvPolynomial.eval w Pf = 0

structure Fac {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) where
  at_ : S.At M y y₀
  yV : Sp u.V ⟶ M.Z
  fac : spMap u.j ≫ yV = y
  yK : Sp (FractionRing u.V) ⟶ U₀.toScheme
  yK_fac : yK ≫ U₀.ι = jK u.V ≫ yV
  yK_u : yK ≫ Q.u₀ = spMap u.yK

structure TMap {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} (t : ρ.GeoTest p y₀)
    (c : Q.Fac y t.u) where
  l : Q.Λ
  mem : y (cPt p) ∈ Q.W l
  m : Matrix S.J S.J t.u.V
  unit : IsUnit m.det
  m_eq : (Q.B l).map (M.val (gPt p ≫ y)) =
    (m.map fun a => (t.u.j a : PadicAlgCl p)) * t.b.map (algebraMap _ (PadicAlgCl p))
  f : t.u.G.left ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme
  f_over : f ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = t.u.G.hom ≫ c.yV
  φ : pullback t.u.G.hom (jK t.u.V) ⟶ pullback ρ.P.A.hom Q.u₀
  φ_fst : φ ≫ pullback.fst _ _ = t.u.U.gen.hom.left ≫ t.u.φ
  φ_snd : φ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ c.yK
  φ_f : φ ≫ Q.a₀ = pullback.fst _ _ ≫ f ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι
  crd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ψ : t.u.V →+* R) (x : Sp R ⟶ t.u.G.left) (w : S.J → R),
    x ≫ t.u.G.hom = spMap ψ → Crd (t.u.H S.N) t.σ x w →
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) (x ≫ f) ((m.map ψ).mulVec w)
end Clos

structure BaseFacts (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) : Prop where
  ov : S.Over₀ M U₀
  ee : S.IsEE M U₀ EE
  jac : JacobsonSpace M.Z
  atTest : ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀),
    M.Cen U₀ z y → S.At M y y₀ → S.HH M z = τ.yy.ker
  free : ∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ
  gen : ∀ ξ ∈ U₀, S.TT M ξ = ⊥
  mem : ∀ ξ i, Pi.single i (1 : Ω) ∈ EE.E ξ
  stab : ∀ ξ, ∀ h ∈ S.HH M ξ, ∀ v ∈ EE.E ξ, ((S.ρ h).map (algebraMap o Ω)).mulVec v ∈ EE.E ξ
  zero : ∀ ξ, IsClosed ({ξ} : Set M.Z) → ∀ v ∈ EE.E ξ,
    ((S.proj (S.TT M ξ) 0).map (algebraMap o Ω)).mulVec v = v → ∀ j, v j ∈ M.O ξ
  sec : ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧
    ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
      S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ
end GlobalTheory.ZH
end
