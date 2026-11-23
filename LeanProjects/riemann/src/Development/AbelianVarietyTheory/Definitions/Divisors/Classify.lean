import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.ClassifyField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

section Points

variable {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N N' : ℕ} (L : Link D G)

def actHom (o : Obj b N (spMap β)) : D.O →+* End (av o) :=
  RingHom.mk' ⟨⟨actEnd o, Subtype.ext o.act.one⟩, fun x y => Subtype.ext (o.act.mul x y)⟩
    (fun x y => Subtype.ext (o.act.add x y))

def PairIso (o : Obj b N (spMap β)) (π : End0 (av o)) (o' : Obj b N (spMap β)) (π' : End0 (av o')) : Prop :=
  ∃ (m : ObjMap o o' (𝟙 _)) (e : av o ≅ av o'), (AbVar.Hom.hom e.hom).left = m.φ ∧ GlobalTheory.LKP.Intertw e.hom π π'

def PairIsog (o : Obj b N (spMap β)) (π : End0 (av o)) (o' : Obj b N' (spMap β)) (π' : End0 (av o')) : Prop :=
  ∃ (I : TIso o) (I' : TIso o') (ψ : av o ⟶ av o') (g : G.GAf),
    IsIsogeny ψ ∧ Acts L I I' ψ 1 g ∧ GlobalTheory.LKP.Intertw ψ π π'

def raw {A : Type} [Ring A] [Algebra ℚ A] (o : Obj b N (spMap β)) (ia : A →ₐ[ℚ] End0 (av o)) : GlobalTheory.LKP.Raw k A where
  A := av o
  ia := ia
  L := o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left
  hL := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull o.isLB _

variable [CharP k p] [PerfectRing k p]

abbrev OFrame (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (o : Obj b N (spMap β)) (π : End0 (av o))
    (H : PDivGroup p k) (t : H.TorsionTower (av o).X) (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) : Type :=
  Frame L T red r H (fun c => t.map t (actEnd o c).hom)
    (fun m ψ => ∃ g : End (av o), m • π = toEnd0 _ g ∧ ψ = t.map t g.hom) d

def RowRel (r : ℕ) (w : Fin G.m) (c : ℤ) (u : GL (Fin G.n) (KQ p (G.Fw w) r))
    (X Y : Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r)) : Prop :=
  Y.map (intKQ p (G.Fw w) r).subtype =
    c • HMul.hMul (α := Matrix (Fin D.m) (Fin G.n) (KQ p (G.Fw w) r)) (β := Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
      (X.map (intKQ p (G.Fw w) r).subtype) u.val

structure Based (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (P : Pair G) (o : Obj b N (spMap β))
    (π : End0 (av o)) where

  I : TIso o
  ind : Induces o I

  x : (AfP p ⊗[ℚ] G.C)ˣ

  s : (AfP p)ˣ
  hx : Triv G (AfP p) P.β x s

  δ : Gr G r

  z : Gr G r
  nrm : IsNrm G r P.atP δ z
  supp : L.MuSupp r δ

  j : P.cent →* (End0 (av o))ˣ
  j_self : (j P.self : End0 (av o)) * π = 1
  j_af : ∀ y, ActsQ L I (j y : End0 (av o)) (P.toAf x s hx y)
  j_surj : ∀ u : End0 (av o), Commute u π → (∃ g, ActsQ L I u g) → ∃ y, (j y : End0 (av o)) = u

  H : PDivGroup p k

  t : H.TorsionTower (av o).X

  fr : OFrame L T red r o π H t δ.2
  j_p : ∀ y (m : ℤ) (ψ : End (av o)), m • (j y : End0 (av o)) = toEnd0 _ ψ → ∀ w X Y,
    RowRel r w m ((P.toQr r z y).2 w) X Y → T.map (t.map t ψ.hom) (fr.B w X) = fr.B w Y

variable {L}

def Based.ga {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {P : Pair G} {o : Obj b N (spMap β)}
    {π : End0 (av o)} (B : Based L T red r P o π) : G.GAf := P.toAf B.x B.s B.hx P.self

def Based.Coord {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {P : Pair G} {o : Obj b N (spMap β)}
    {π : End0 (av o)} (B : Based L T red r P o π) (o' : Obj b N (spMap β)) (π' : End0 (av o')) (g : G.GAf)
    (y : Gr G r) : Prop :=
  ∃ (I' : TIso o') (ψ : av o ⟶ av o') (m : ℕ) (v : ℤ) (H' : PDivGroup p k) (t' : H'.TorsionTower (av o').X)
    (fr' : OFrame L T red r o' π' H' t' (y⁻¹ * B.δ * sigG G r y).2),
    0 < m ∧ Induces o' I' ∧ IsIsogeny ψ ∧ Acts L B.I I' ψ m g⁻¹ ∧ GlobalTheory.LKP.Intertw ψ π π' ∧
    fr'.sp = B.fr.sp ∧
    (∀ w (c : ℤ) X Y, RowRel r w c (y.2 w)⁻¹ X Y →
      c • T.map (B.t.map t' ψ.hom) (fr'.B w X) = (m : ℤ) • B.fr.B w Y) ∧
    GlobalTheory.LKLoc.KotInv p (Q0 p) 1 r y.1 v ∧
    (padicValNat p (deg ψ) : ℤ) = (av o).dim * (2 * padicValNat p m - v)

end Points

def Live (L : Link D G) (r : ℕ) (P : Pair G) : Prop := ∃ δ z, IsNrm G r P.atP δ z ∧ L.MuSupp r δ

def JCompat (G : HTGroup p) {k : Type} [Field k] (red : (Obar p).toSubring →+* k) (j : GlobalTheory.LKP.Zb →+* k) : Prop :=
  ∀ (a : AlgebraicClosure ℚ) (z : GlobalTheory.LKP.Zb) (z' : (Obar p).toSubring), G.iotaC a = z → G.iotaP a = z' → j z = red z'

structure Chart (L : Link D G) (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra G.F M] where
  rank : Module.finrank G.F M = G.n

  i : M →ₐ[G.F] G.C

  H : Fin G.n → M
  pos : ∀ a, GlobalTheory.LKP.TotPos (H a)

  κ : VQ D ≃ₗ[ℚ] (Fin G.n → M)
  κ_i : ∀ x v, κ (L.rep (i x) v) = x • κ v

  oM : D.O →+* Matrix (Fin G.n) (Fin G.n) M
  κ_o : ∀ c v, κ (actQ D c v) = oM c *ᵥ κ v
  span : Submodule.span M (Set.range oM) = ⊤
  star : ∀ c, oM (D.star c).unop = GlobalTheory.LKP.sigH H (oM c)

namespace Chart

variable {L : Link D G} {M : Type} [Field M] [NumberField M] [IsCMField M] [Algebra G.F M] (ch : Chart L M)

def FormOf (β : G.Cˣ) (ξ : M) : Prop :=
  ∀ v w, D.EF.baseChange ℚ v (L.rep ((β⁻¹ : G.Cˣ) : G.C) w) = -GlobalTheory.LKP.psiH ch.H ξ (ch.κ v) (ch.κ w)

def IsRaw {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N : ℕ} (a : M)
    (o : Obj b N (spMap β)) (π : End0 (av o)) (ia : Matrix (Fin G.n) (Fin G.n) M →ₐ[ℚ] End0 (av o)) : Prop :=
  (∀ c, ia (ch.oM c) = toEnd0 _ (actEnd o c)) ∧ ia (Matrix.scalar _ a) * π = 1

end Chart

def typeOf (L : Link D G) (M : Type) [Field M] [NumberField M] [Algebra G.F M] (φ₀ : M →+* ℂ) : Finset (M →+* ℂ) :=
  insert φ₀ (Finset.univ.filter fun φ => φ (algebraMap G.F M (L.e D.ω)) = (starRingEnd ℂ) D.ρc ∧
    φ ≠ ComplexEmbedding.conjugate φ₀)

def MarkAt (L : Link D G) {M : Type} [Field M] [Algebra G.F M] (φ₀ : M →+* ℂ) (a : M) (mu : ℂ) : Prop :=
  ∃ i : Fin D.a, φ₀.comp (algebraMap G.F M) = G.iotaC.comp (L.s i) ∧
    mu = if (InfinitePlace.mk (G.iotaC.comp (L.s i))).embedding = G.iotaC.comp (L.s i) then φ₀ a
      else (starRingEnd ℂ) (φ₀ a)

def Classify : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R]
    (b : Base D R) (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p))
    (N r : ℕ), Setup L b β red N r → ∀ sel, L.GoodSel sel →
    ∃ (o : {q : Cls G // (Quot.out q).Mark (sel (Quot.out q).pol) ∧ Live L r (Quot.out q)} → Obj b N (spMap β))
      (π : ∀ q, End0 (av (o q))),
      (∀ q, Nonempty (Based L T red r (Quot.out q.1) (o q) (π q))) ∧
      ∀ (o' : Obj b N (spMap β)) (π' : End0 (av o')) ga δ, IsPair L T red r o' π' ga δ → L.MuSupp r δ → RegAf G ga →
        ∃! q, PairIsog L (o q) (π q) o' π'

end GlobalTheory.LKGeo
