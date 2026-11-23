import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.SeriesTie NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.TwInputs

def RealSide.ofPins {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (p : GlobalTheory.Mem.R3.Pins R F cG)
    (h : GlobalTheory.Mem.R3.Holds R F) (g : GlobalTheory.RealGeo.InGeo geo) (f : Finite T) (hh : HostHyp D) (s : ∀ j, FWT.VStd D j)
    (z : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) : RealSide D :=
  { Γ := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, core := C, R := R, F := F, cG := cG, geo := geo,
    char := RealDat3.characterisation_of_weak p.char h.aux.ex, phs := p.phs, guard := p.keep.guard, valKs := p.keep.valKs,
    idem := by obtain ⟨_, _, _, h2, _⟩ := p.keep.grp; exact h2
    unif := h.prim.unif, integral := h.aux.integral, inGeo := g, finT := f, host := hh, std := s, size := z }

section Second

variable {D : D7} (X : RealSide D) (S : RatDat D.ntw) {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ} {Pq} {hL} {eig} {θ}
  (Bs : SideB D cf Rw low Pq S hL eig θ) (fi : ∀ i : Fin D.R.m, FormsIso (S.A ((i : ℕ) + 1)) (X.R.FW i))
  (geq : ∀ (i : Fin D.R.m) (g : S.G), X.cG (X.R.eG ((fi i).eG g)) = S.eG g)

def formsOf : NExpRealS X.R X.cG S :=
  ⟨fi, geq, Bs.rho, Bs.chiL, Bs.eF, fun i j b h1 h2 => ⟨1, one_ne_zero,
    fun x hx => by rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (Bs.bsup i j b h1 h2 x).2 hx⟩, Bs.act⟩

def heckeOf : NExpRealH X.R X.cG S (formsOf X S Bs fi geq) :=
  { hL := hL, hs := Bs.hs, cHk := fun i b k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P) ^ k
    cHk_zero := fun _ _ _ => pow_zero _, cHk_unit := fun i b P => ((Bs.cHk i b P).isUnit.map _).pow _
    cHk_pow := fun _ _ _ _ => by rw [pow_one], hkEq := Bs.hkEq }

def SerSide.ofSecondStep (E : IntegralHeckeForms.XD D) (hr : GlobalTheory.ExportPin.Reads X.R X.cG S (formsOf X S Bs fi geq) hL)
    (Z : ExportTie (formsOf X S Bs fi geq) X.geo.v₀)
    (gt : GrpTie D X.A3.A X.F.P0 X.F.ψ0 X.F.P1 X.F.ψ1 (X.R.eG.trans X.cG))
    (no : ∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, Subsingleton (D.nexp.Fm i j b))
    (al : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b)
    (lo : ∀ i (P : PlE D.host), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK *
      (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i)
    (sb : ∀ i, ∀ P ∈ X.R.Sb, P ∈ D.ntw.S0 i) : SerSide X E :=
  { S := S, YS := formsOf X S Bs fi geq, sup := Bs.bsup, H := heckeOf X S Bs fi geq, reads := hr
    del := fun i b P hP σ hσ => by
      change algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P) ^ 1 = _
      rw [pow_one, Bs.cHk_del i b P hP σ hσ]; rfl
    Z := Z, U_eq := fun g => (gt.lvl0 g).symm
    psi_eq := fun i b g h => by
      obtain ⟨x, h1, h2⟩ := gt.psi0 g h i b
      rw [← map_inv₀, ← Units.val_inv_eq_inv_val, ← h1]
      exact (congrArg (Z.ρ.e i b) h2).trans (Z.good.e_LL0 i b x)
    low := lo, Sb := sb
    B_range := fun i _ j _ b => Bs.tw.B_range i j b
    hk_emb := fun i j b k P x h1 h2 h => Bs.hk_emb i j b k P x h1 h2 h.2.2.2 h.2.2.1 h.2.1
    hk_split := fun i _ j _ b k P h => by
      obtain ⟨s, hs⟩ := Bs.tw.hk_split i j b k P h.2.2.2
      rw [hs]; exact Polynomial.Splits.multisetProd (by
        intro p hp; obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hp; exact Polynomial.Splits.X_sub_C a)
    off := fun i _ => ⟨no i, Bs.hEig_zero i⟩
    all := al }

example : (heckeOf X S Bs fi geq).hL = hL := rfl

example (i : D.ntw.Tw) (b : Bool) (P : PlE D.host) : (heckeOf X S Bs fi geq).cHk i b 0 P = 1 := pow_zero _

end Second

def GalSide.ofFirstStep {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) (tr : GlobalTheory.Triple.IsTriple D)
    (lam : GlobalTheory.LamTie.LamDat D) (ok : lam.Ok) (tie : GlobalTheory.LamTie.IsLamTie D.ntw lam) (rank : 100 ≤ D.R.r)
    (primes : ∀ k, 2 * D.R.r ≤ D.host.g k) : GalSide D :=
  { wd := A.wdT, lab := A.lab, cf := cf, chr := A.chr, triple := tr, lam := lam, lamOk := ok, lamTie := tie, rank := rank,
    primes := primes }

def GalSide.ofFirstStepLoc {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) (L : LocAll (lay0 D))
    (chr : CharSide (withLoc L) (cfL L cf)) (tr : GlobalTheory.Triple.IsTriple (withLoc L)) (lam : GlobalTheory.LamTie.LamDat (withLoc L)) (ok : lam.Ok)
    (tie : GlobalTheory.LamTie.IsLamTie (withLoc L).ntw lam) (rank : 100 ≤ D.R.r) (primes : ∀ k, 2 * D.R.r ≤ D.host.g k) :
    GalSide (withLoc L) :=
  { wd := { A.wdT with }, lab := A.lab, cf := cfL L cf, chr := chr, triple := tr, lam := lam, lamOk := ok, lamTie := tie,
    rank := rank, primes := primes }

end GlobalTheory.TwInputs

end
