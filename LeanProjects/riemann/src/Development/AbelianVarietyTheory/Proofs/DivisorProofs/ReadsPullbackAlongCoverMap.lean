import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionUnitsGenericOpen

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

noncomputable section

open GlobalTheory.FrameGlue.PowGlue GlobalTheory.TrueGeo.SmallSec in

theorem GlobalTheory.LatChain.reads_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (A : Adl C Y) (p : ℕ)
    (V V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X), Lies V' V π →
    ∀ c : V.X → V.X.functionFieldˣ, Reads V p A c →
      Reads V' p A fun x => Units.map (SmallSec.fnMap π hπ).toMonoidHom (c (π x)) := by
  intro F _ _ Y C A p V V' π hπ hL c hR
  obtain ⟨hη, W, U, hW, hov, hunit, hnorm⟩ := hR
  obtain ⟨g, hgj, hgπ⟩ := hL
  have hη' := RootLine.j_gen_specializes V'
  have hg : g (genericPoint V'.G) ⤳ genericPoint V.G := specializes_of_eq (gen_of_lies V V' π hπ g hgj)
  obtain ⟨hηV, eV⟩ := V.φ_eq_fnMap
  obtain ⟨hηV', eV'⟩ := V'.φ_eq_fnMap
  have hφ : ∀ t, V'.φ t = fnMap g hg (V.φ t) := by
    intro t
    rw [eV', eV, ← ProjSpace.fnMap_comp g V.π hg hηV (ProjSpace.comp_genericPoint_specializes _ _ hg hηV) t]
    exact ProjSpace.fnMap_congr hgπ.symm _ _ _
  have hcc : ∀ f, fnMap V'.j hη' (fnMap π hπ f) = fnMap g hg (fnMap V.j hη f) := by
    intro f
    rw [← ProjSpace.fnMap_comp V'.j π hη' hπ (ProjSpace.comp_genericPoint_specializes _ _ hη' hπ),
      ← ProjSpace.fnMap_comp g V.j hg hη (ProjSpace.comp_genericPoint_specializes _ _ hg hη)]
    exact ProjSpace.fnMap_congr hgj.symm _ _ _
  have hval : ∀ x, (jm V' hη' ((Units.map (fnMap π hπ).toMonoidHom (c (π x)) : V'.X.functionFieldˣ)) :
      V'.G.functionField) = fnMap g hg (jm V hη (c (π x))) := by
    intro x
    exact hcc _
  refine ⟨hη', W, fun x => π ⁻¹ᵁ U (π x), hW, fun x hx => hov _ (hx.map π), ?_, ?_⟩
  · intro x z hz
    have hgz : V.j (g z) ∈ U (π x) := by
      have : V.j (g z) = π (V'.j z) := by rw [← Scheme.Hom.comp_apply, hgj, Scheme.Hom.comp_apply]
      rw [this]; exact hz
    have hπz : V.π (g z) = V'.π z := by rw [← Scheme.Hom.comp_apply, hgπ]
    have H := RootLine.unitAt_fnMap g hg (hunit (π x) (g z) hgz)
    rw [map_mul, ← hφ, hπz] at H
    rw [hval]
    exact H
  · intro v hv e y hy z yt e1 e2 x hyt
    have hz : V'.j (below z) ∈ π ⁻¹ᵁ U (π x) := by
      have h1 : (z ≫ V'.j) (IsLocalRing.closedPoint _) ∈ π ⁻¹ᵁ U (π x) := by
        rw [← e2]
        exact hyt (Set.mem_univ _)
      exact h1
    have hb : V'.π (below z) = below y.1 := by rw [← e1]; rfl
    have e1' : (z ≫ g) ≫ V.π = y.1 := by rw [Category.assoc, hgπ, e1]
    have e2' : spMap e.O.subtype ≫ (yt ≫ π) = (z ≫ g) ≫ V.j := by
      rw [← Category.assoc, e2, Category.assoc, Category.assoc, hgj]
    have hUa : ⊤ ≤ (yt ≫ π) ⁻¹ᵁ U (π x) := fun w hw => hyt hw
    have HV := hnorm v hv e y hy (z ≫ g) (yt ≫ π) e1' e2' (π x) hUa
    have hgz : V.j (g (below z)) ∈ U (π x) := by
      have : V.j (g (below z)) = π (V'.j (below z)) := by
        rw [← Scheme.Hom.comp_apply, hgj, Scheme.Hom.comp_apply]
      rw [this]; exact hz
    have hπz : V.π (g (below z)) = below y.1 := by rw [← Scheme.Hom.comp_apply, hgπ, hb]
    have hU := hunit (π x) (g (below z)) hgz
    rw [hπz] at hU
    rw [← valAt_fnMap g hg z hU.regAt, map_mul, ← hφ] at HV
    rw [hval]
    exact HV

end
