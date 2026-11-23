import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBasesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonLeftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonRightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : R →+* S) (b : T →+* R) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  show Spec.map (CommRingCat.ofHom (a.comp b)) = Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have h' : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := h
  have := Spec.map_injective h'
  exact CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e

theorem spMap_dualMap_id (Ω : Type) [Field Ω] : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
  have : dualMap (RingHom.id Ω) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
  simp

theorem cst_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] {a b : F →+* Ω}
    (h : a.comp (algebraMap (𝓞 F) F) = b.comp (algebraMap (𝓞 F) F)) : a = b :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

theorem exists_cover : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 := by
  intro hG hW E _ _ _ H D l Xo c Y Sys Fx R o S hSp hSd hdeg
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  haveI : CharZero R.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y o.𝔐.Ω₀ o.𝔐.ξ₀ o.𝔐.gen₀
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt (o.𝔐.ξ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    have e : o.𝔐.ξ ≫ o.𝔐.f = Spec.map (CommRingCat.ofHom o.𝔐.fn) ≫ o.𝔐.ξ₀ := o.𝔐.fn_over
    rw [e, genPt_comp]; exact hgen₀
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y R.Ω (o.𝔐.ξ ≫ o.𝔐.f) S hgen hSp
  obtain ⟨K₁, _, J₁, _, y₁, bk₁, bx₁, M₁, h₁, hbk₁, hy₁, hdom₁, hnorm₁, hsm₁⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes R.K R.ι R.Ω Ω i R.y o.𝔐.X o.𝔐.ξ hfin o.𝔐.all o.𝔐.tie
  have hξ₁ : M₁.ξ ≫ h₁ ≫ o.𝔐.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
    have e : M₁.ξ ≫ h₁ = Spec.map (CommRingCat.ofHom i) ≫ o.𝔐.ξ := hdom₁
    rw [← Category.assoc, e, Category.assoc]
  have hgen₁ : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ h₁ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    rw [hξ₁]; show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ _) ∈ _
    rw [genPt_comp]; exact hgen
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω (M₁.ξ ≫ h₁ ≫ o.𝔐.f) hgen₁
  obtain ⟨K₂, _, J₂, _, y₂, bk₂, bx₂, B, g, hbk₂, hy₂, hdom₂, hf₂, hR₂, hfree₂, hiso₂⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ (h₁ ≫ o.𝔐.f) y₀ hnorm₁ hy₀ hgen₁ hSp hSd
      (fun _ _ => le_rfl) (fun p hp => by rw [hξ₁]; exact htors p hp) hroot
  have hgB : B.ξ ≫ g = M₁.ξ := by
    have e : B.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hdomB : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ o.𝔐.ξ (g ≫ h₁) i := by
    show B.ξ ≫ g ≫ h₁ = _
    rw [← Category.assoc, hgB]; exact hdom₁
  have hfB : B.f = (g ≫ h₁) ≫ o.𝔐.f := by rw [hf₂, Category.assoc]
  have hBξ : B.ξ ≫ B.f = y₀ ≫ Y.j := by
    rw [hf₂, ← Category.assoc, hgB]; exact hy₀
  have hcst : B.cst = i.comp o.𝔐.cst := by
    have h1 := B.cst_over
    have h2 := o.𝔐.cst_over
    have h3 : B.ξ ≫ B.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
      rw [hf₂, ← Category.assoc, hgB]; exact hξ₁
    have h4 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) =
        spMap ((i.comp o.𝔐.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← Category.assoc, h3, RingHom.comp_assoc, spMap_comp', ← h2]
      simp
    haveI := c.fin
    haveI : NumberField c.F := {}
    exact cst_ext (spMap_inj h4)
  obtain ⟨jA, hext, hpt, hact, hlat⟩ :=
    GlobalTheory.T.hodge_comp_comparison_left E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 B i (g ≫ h₁) hdomB hfB
  obtain ⟨Li₀, _, _, M₀, j, V₀, hspan, hj, hV, hflag⟩ :=
    GlobalTheory.T.hodge_comp_comparison_middle E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hfin hdomB hfB hcst hext hpt hact
  have hvb := GlobalTheory.T.hodge_comp_comparison_right E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hdomB hfB hcst hext hpt hact hlat
  obtain ⟨K₃, _, J₃, _, y₃, bk₃, bx₃, 𝔐, g', Fl, xdeg, e, hbk₃, hy₃, hdom₃, hf₃, hR₃, hc₃, hfree₃, hFd, hFb, hlines, -, hiso₃⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω K₂ J₂ y₂ B y₀ (fun s a => jA (o.Fl.b s a)) Li₀ _ _ M₀ j V₀ _ hBξ hSd hfree₂
      (fun p hp => by rw [hR₂]; exact hroot p hp) hspan hj hV hflag
  have hsm₂ : SmoothGenericFibreM y₂ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₁ J₁ y₁ K₂ J₂ y₂ M₁.X B.X M₁.ξ B.ξ g M₁.all B.all M₁.tie B.tie hdom₂ hsm₁ hiso₂
  have hsm₃ : SmoothGenericFibreM y₃ :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω K₂ J₂ y₂ K₃ J₃ y₃ B.X 𝔐.X B.ξ 𝔐.ξ g' B.all 𝔐.all B.tie 𝔐.tie hdom₃ hsm₂
      (fun q hq => hiso₃ q hq (hvb q hq))
  have hg' : 𝔐.ξ ≫ g' = B.ξ := by
    have e : 𝔐.ξ ≫ g' = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ B.ξ := hdom₃
    rw [e]; simp
  refine ⟨Ω, inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, fun k => bk₃ (bk₂ (bk₁ k)),
    fun k => (bx₁ k).trans ((bx₂ _).trans (bx₃ _)), i, 𝔐, g' ≫ g ≫ h₁, Fl, xdeg, e,
    hbk₃.comp (hbk₂.comp hbk₁), ?_, ?_, ?_, ?_, ?_, ?_, hlines, ?_, hsm₃, ?_⟩
  · intro k a
    simp only [Equiv.trans_apply]
    rw [hy₃, hy₂, hy₁]
  · show 𝔐.ξ ≫ g' ≫ g ≫ h₁ = _
    rw [← Category.assoc, hg']; exact hdomB
  · rw [hf₃, hf₂]; simp
  · rw [hc₃, hcst]
  · intro s a
    rw [hFb, hpt, spMap_dualMap_id, Category.id_comp]
  · rw [hFd, hdeg, _root_.mul_one]
  · intro p hp
    have := hfree₃ p hp
    exact this
  · intro p hp
    rw [hR₃, hR₂]

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
