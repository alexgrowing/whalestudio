import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def keyInOf {R : Type} [CommRing R] (t : SAB H (Sp R)) (th : t.PP.L.Sec) (g : ℕ) (hg : 1 ≤ g)
    (v : Fin g → (epsR R ⟶ t.G)) (hv : IsLieBasis v) (hab : IsAbelianScheme t.G)
    (hd : SmoothOfRelativeDimension g t.G.hom) (hs : Out.Sym t.G t.PP.L) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) (hth : ∀ s : Sp R, ∃ x : t.G.left, t.G.hom x = s ∧ x ∈ Out.nonzeroLocus th) : KeyIn R where
  P := { A := t.G, isAb := hab, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB,
         rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := hs, ample := ha, ktriv := hk }
  g_pos := hg
  rig := t.PP.rig
  rig_gen := t.PP.rigGen
  th := th
  th_ne := hth
  v := v
  basis := hv

theorem keyPB_of_keyOver {R K : Type} [CommRing R] [Field K] (f : R →+* K) (t : SAB H (Sp R)) (th : t.PP.L.Sec)
    (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)) (hv hab hd hs ha hk hth) (h : KeyOver f t th x v) :
    KeyPB x (keyInOf t th x.P.g x.g_pos v hv hab hd hs ha hk hth) f := by
  obtain ⟨φ, he, w, h1, h2, h3, h4, h5⟩ := h
  refine ⟨φ, he, w, rfl, dualMap f, h1, h2, h3, h4, fun a => ?_, ?_, h5⟩
  · ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [dualMap]

theorem unit_of_good (κ : GlobalTheory.KeyCl.Rule) (hκ : GlobalTheory.KeyCl.UnitSp κ) {R K : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (t : SAB H (Sp R))
    (th : t.PP.L.Sec) (x : KeyIn K) (v : Fin x.P.g → (epsR R ⟶ t.G)) (h : KeyOver (algebraMap R K) t th x v)
    (hv : IsLieBasis v) (hab : IsAbelianScheme t.G) (hd : SmoothOfRelativeDimension x.P.g t.G.hom)
    (hs : Out.Sym t.G t.PP.L) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hth : ∀ s : Sp R, ∃ y : t.G.left, t.G.hom y = s ∧ y ∈ Out.nonzeroLocus th) :
    ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  obtain ⟨u, hu, -⟩ := hκ R K _ x (keyPB_of_keyOver _ t th x v hv hab hd hs ha hk hth h)
  exact ⟨u, hu⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyBadModel
