import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.FlagAmple.PlkLoc

theorem exists_coord_f0 : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ (Φ.C k).π ⁻¹ᵁ V), ∃ B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn, g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B := by
  intro D A N j S κ s Φ k V hV φ g hfs hst hne
  revert hne
  generalize Φ.C k = C
  intro hne
  set ψ := baseFn C V hne with hψ
  have h1 : genericPt C.Y ≫ C.π = spMap ψ ≫ hV.fromSpec := by
    have hm : C.π (genericPoint C.Y.X) ∈ V := hne
    rw [genericPt, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hV.fromSpecStalk_eq_fromSpecStalk hm,
      IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp, Scheme.Hom.germ_stalkMap,
      Scheme.Hom.app_eq_appLE]
    rfl
  have h3 : (genericPt C.Y ≫ C.π ≫ genι _) = spMap ψ ≫ (hV.fromSpec ≫ genι _) := by
    rw [← Category.assoc, h1, Category.assoc]
  have hal : algebraMap _ C.Y.Fn = (ψ.comp φ).comp κ.e.toRingHom := by
    have e1 : genericPt C.Y ≫ C.Y.str = spMap (algebraMap _ C.Y.Fn) := (GlobalTheory.FlagBundle.ratOf C.Y).pt_s
    rw [← C.π_str, ← Category.assoc, h1, Category.assoc, ← Category.assoc hV.fromSpec, hfs] at e1
    have e2 : spMap ((ψ.comp φ).comp κ.e.toRingHom) = spMap (algebraMap _ C.Y.Fn) := by
      rw [← e1]
      show Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective e2)).symm
  have h2 : constF κ.e C.Y = ψ.comp φ := by
    ext a
    simp [constF, hal]
  obtain ⟨g', hg'⟩ := hst C.Y.Fn ψ
  have hv : ∀ τ, (fun l => spMap (dualMap ψ) ≫ g.v τ l) = g'.v τ := fun τ => funext fun l => (hg' τ l).symm
  have ex : ∀ τ i, ∃ a, IsCombAtG _ (genericPt C.Y ≫ C.π ≫ genι _) (fun l => spMap (dualMap ψ) ≫ g.v τ l) a
      (C.f0.v τ i) := by
    intro τ i
    have ht := C.f0.tan τ i
    have he := C.f0.eig τ i
    generalize C.f0.v τ i = w at ht he ⊢
    rw [h3] at ht ⊢
    rw [h2] at he
    rw [hv τ]
    exact (g'.basis τ w ht he).exists
  choose B hB using ex
  exact ⟨B, h3, h2, hB⟩

end GlobalTheory.FlagAmple.PlkLoc
