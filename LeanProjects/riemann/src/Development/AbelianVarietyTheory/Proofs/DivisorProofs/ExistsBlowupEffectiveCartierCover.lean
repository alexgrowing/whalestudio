import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFactoringProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LatChain.BlowDom

theorem exists_cover_over_blowup : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p ≠ 0 → ∀ J : V.X.IdealSheafData, (∀ x ∈ J.support, x ∉ V.X.basicOpen (p : Γ(V.X, ⊤))) → ∃ (V' : Cover Y) (Z : Scheme.{0}) (b : Z ⟶ V.X) (ν : V'.X ⟶ Z), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) ∧ (ν ≫ b) ≫ V.p = V'.p ∧ Lies V' V (ν ≫ b) := by
  intro F _ _ Y V p hp0 J hJp
  have := V.ar.isNoetherianRing
  obtain ⟨Z, b, hb, hproj, hiso⟩ := ProjBlowup.exists_blowup V.p V.ar.isProjOver J
  let U : V.X.Opens := J.support.compl
  have hbV : IsIso (b ∣_ U) := hiso U fun _ hx => hx
  have huF : IsUnit ((p : ℕ) : Γ(Sp F, ⊤)) := by
    have := (IsUnit.mk0 (p : F) (Nat.cast_ne_zero.2 hp0)).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    simpa using this
  have huW : IsUnit ((p : ℕ) : Γ(V.G, ⊤)) := by
    let φ : Γ(Sp F, ⊤) →+* Γ(V.G, ⊤) := ((V.π ≫ Y.str).app ⊤).hom
    have := huF.map φ
    rwa [map_natCast φ] at this
  have hrange : Set.range V.j ⊆ Set.range U.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w ∈ V.j ⁻¹ᵁ V.X.basicOpen (p : Γ(V.X, ⊤)) := by
      simp only [Scheme.preimage_basicOpen, map_natCast]
      exact (Scheme.basicOpen_of_isUnit V.G huW).ge (show w ∈ (⊤ : V.G.Opens) from trivial)
    exact fun hx => hJp _ hx hw
  let jV : V.G ⟶ U.toScheme := IsOpenImmersion.lift U.ι V.j hrange
  have hjV : jV ≫ U.ι = V.j := IsOpenImmersion.lift_fac _ _ _
  let h : V.G ⟶ Z := jV ≫ inv (b ∣_ U) ≫ (b ⁻¹ᵁ U).ι
  have hh : h ≫ b = V.j := by
    simp only [h, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hjV]
  obtain ⟨V', ν, g, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_cover_factoring_projective F Y V Z (b ≫ V.p) h hproj (by rw [← Category.assoc, hh])
  refine ⟨V', Z, b, ν, hb.1, by rw [Category.assoc, h₁], g, ?_, h₃⟩
  rw [← Category.assoc, h₂, Category.assoc, hh]

end GlobalTheory.LatChain.BlowDom
