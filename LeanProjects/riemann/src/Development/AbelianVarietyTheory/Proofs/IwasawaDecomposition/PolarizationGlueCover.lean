import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotIsProjOverAffineLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

theorem isPhiDiv_of_openCover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {I : Type} {R : I → Type} [∀ i, CommRing (R i)] {ω : ∀ i, R i →+* c.F} (Z : Model Xo c β) (C : ∀ i, Model Xo c (ω i)) (u : ∀ i, (C i).X ⟶ Z.X) (φ : InvFun (𝓞 E)) (DZ : EffCartierData Z.X) (BD : ∀ i, EffCartierData (C i).X), (∀ i, IsOpenImmersion (u i)) → (∀ i, (C i).j ≫ u i = Z.j) → (∀ i, Nonempty (SABMap (C i).t Z.t (u i))) → (∀ x : Z.X, ∃ i, x ∈ Set.range (u i)) → (∀ i, DZ.idealSheaf.comap (u i) = (BD i).idealSheaf) → (∀ i, IsPhiDiv φ (C i) (BD i)) → IsPhiDiv φ Z DZ := by
  intro E _ _ _ H D l Xo c O _ β I R _ ω Z C u φ DZ BD hopen hj hsab hcov hcomap hphi
  intro W _ _ _ hW ϖ hϖ χ t m P hgen be hbe hmon
  obtain ⟨i, hi⟩ := hcov (χ (IsLocalRing.closedPoint W))
  have hrange : Set.range χ ⊆ Set.range (u i) := by
    rintro _ ⟨x, rfl⟩
    have hsp : χ x ⤳ χ (IsLocalRing.closedPoint W) :=
      (IsLocalRing.specializes_closedPoint x).map χ.continuous
    exact hsp.mem_open (u i).isOpenEmbedding.isOpen_range hi
  obtain ⟨χ', rfl⟩ : ∃ χ', χ' ≫ u i = χ := ⟨IsOpenImmersion.lift (u i) χ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨mi⟩ := hsab i
  obtain ⟨m', -⟩ := (GlobalTheory.PullCalcTest.existsUnique_cancel mi m).exists
  have hgen' : Set.range (Out.jK W ≫ χ') ⊆ Set.range (C i).j := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hgen ⟨y, rfl⟩
    refine ⟨z, (u i).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hj i, hz]
    simp [Scheme.Hom.comp_apply]
  obtain ⟨n, hn, hid⟩ := hphi i W hW ϖ hϖ χ' t m' P hgen' be hbe hmon
  refine ⟨n, hn, ?_⟩
  rw [← idlAlong_comap, hcomap i, hid]

end GlobalTheory.TorRef
