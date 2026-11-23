import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.LB (toMod)
open Limits (pullback)

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

variable (p) in

def ratFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))

namespace ratFibre

variable (p)

def fst : ratFibre p ⟶ X := pullback.fst _ _

def snd : ratFibre p ⟶ Sp ℚ := pullback.snd _ _

instance algebra : Algebra ℚ Γ(ratFibre p, ⊤) := algebraΓOfHom (snd p)

theorem isPullback : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom ℚ)) := IsPullback.of_hasPullback _ _

theorem strHom_eq : strHom ℚ (ratFibre p) = snd p := GlobalTheory.strHom_eq fun _ => rfl

def map (ν : Y ⟶ X) : ratFibre (ν ≫ p) ⟶ ratFibre p :=
  pullback.lift (fst (ν ≫ p) ≫ ν) (snd (ν ≫ p)) (by
    simpa only [Category.assoc] using (isPullback (ν ≫ p)).w)

theorem map_fst (ν : Y ⟶ X) : map p ν ≫ fst p = fst (ν ≫ p) ≫ ν := pullback.lift_fst _ _ _

theorem map_snd (ν : Y ⟶ X) : map p ν ≫ snd p = snd (ν ≫ p) := pullback.lift_snd _ _ _

theorem isPullback_map (ν : Y ⟶ X) : IsPullback (fst (ν ≫ p)) (map p ν) ν (fst p) := by
  refine IsPullback.of_bot ?_ (map_fst p ν).symm (isPullback p)
  simpa only [map_snd, Category.assoc] using isPullback (ν ≫ p)

end ratFibre

variable (p) in

def ratDeg (L : LB X) : ℤ := degOfRank ℚ (toMod (L.pull (ratFibre.fst p))) 1

theorem ratDeg_eq_degLB [IsIntegral (ratFibre p)] {L : LB X} (hL : L.IsLB) :
    ratDeg p L = degLB ℚ (L.pull (ratFibre.fst p)) :=
  ((isVB_toMod (Semi.LB.isLB_pull hL _)).deg_eq ℚ).symm

abbrev CxPts.pt (y : CxPts p σ) : X := y.1 (IsLocalRing.closedPoint ℂ)

def germOrd {W : X.Opens} (f : Γ(X, W)) {x : X} (hx : x ∈ W) : ℕ :=
  (Ring.ord (X.presheaf.stalk x) (X.presheaf.germ W x hx f)).toNat

theorem germOrd_res {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {x : X} (hx : x ∈ W') :
    germOrd (resG X h f) hx = germOrd f (h hx) :=
  congrArg (fun a => (Ring.ord (X.presheaf.stalk x) a).toNat) (Cartier.germ_resG h x hx f)

theorem germOrd_unit_mul {W : X.Opens} (u : Γ(X, W)ˣ) (f : Γ(X, W)) {x : X} (hx : x ∈ W) :
    germOrd (u.val * f) hx = germOrd f hx := by
  rw [germOrd, germOrd, map_mul, Ring.ord, Ring.ord,
    Ideal.span_singleton_mul_left_unit (u.isUnit.map _)]

theorem germOrd_eq_zero {W : X.Opens} {f : Γ(X, W)} {x : X} (hx : x ∈ W) (h : x ∈ X.basicOpen f) :
    germOrd f hx = 0 := by
  rw [germOrd, Ring.ord_of_isUnit ((X.mem_basicOpen f x hx).1 h)]
  rfl

theorem exists_mem_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i :=
  Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))

def secOrd {L : LB X} (hL : L.IsLB) (s : L.Sec) (x : X) : ℕ :=
  germOrd (s.f (exists_mem_chart hL x).choose) (exists_mem_chart hL x).choose_spec

theorem secOrd_eq {L : LB X} (hL : L.IsLB) (s : L.Sec) {x : X} {i : L.ι} (hi : x ∈ L.U i) :
    secOrd hL s x = germOrd (s.f i) hi := by
  have hj := (exists_mem_chart hL x).choose_spec
  have hx : x ∈ L.U (exists_mem_chart hL x).choose ⊓ L.U i := ⟨hj, hi⟩
  exact (germOrd_res inf_le_left _ hx).symm.trans ((congrArg (germOrd · hx) (s.compat _ i)).trans
    ((germOrd_unit_mul (L.g _ i) _ hx).trans (germOrd_res inf_le_right _ hx)))

theorem secOrd_eq_zero {L : LB X} (hL : L.IsLB) {s : L.Sec} {x : X} (h : x ∈ nonzeroLocus s) :
    secOrd hL s x = 0 := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h
  rw [secOrd_eq hL s (X.basicOpen_le _ hi), germOrd_eq_zero _ hi]

end GlobalTheory
