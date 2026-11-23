import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Classify
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.Frame

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {k : Type} [Field k] [CharP k p]
  [PerfectRing k p] {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {H : PDivGroup p k}
  {act : D.O → (H ⟶ H)} {rat : ℤ → (H ⟶ H) → Prop} {d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)}

def part (fr : Frame L T red r H act rat d) (w : Fin G.m) : Submodule (WittVector p k) (T.M H) :=
  Submodule.span (WittVector p k) (Set.range (fr.B w))

def partF (fr : Frame L T red r H act rat d) (w : Fin G.m) : Submodule (WittVector p k) (T.M H) :=
  Submodule.span (WittVector p k) ((fun x => T.F H x) '' (fr.part w : Set (T.M H)))

def cokLen (fr : Frame L T red r H act rat d) (w : Fin G.m) : ℕ∞ :=
  Module.length (WittVector p k) (fr.part w ⧸ (fr.partF w).comap (fr.part w).subtype)

end GlobalTheory.LKGeo.Frame
