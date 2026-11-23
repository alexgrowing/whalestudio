import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineDomainNbhdNormalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsPullPreserveBasicOpensStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedMapSendsChartOpensStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartPull

theorem exists_secOn_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {σ : 𝓞 E ≃+* 𝓞 E} (mu : TwMap σ t' t f) (U : S.Opens)
    (θ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U i)) (hθ : θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ U))
    (hne : ∀ y ∈ U, ∃ (g : t.G.left) (i : t.PP.L.ι), t.G.hom g = y ∧ g ∈ t.G.left.basicOpen (θ i))
    (U' : S'.Opens) (hle : U' ≤ f ⁻¹ᵁ U) :
    ∃ θ' : (∀ i, Γ(t'.G.left, t'.G.hom ⁻¹ᵁ U' ⊓ t'.PP.L.U i)), θ' ∈ secOn t'.PP.L (t'.G.hom ⁻¹ᵁ U') ∧
      ∀ y ∈ U', ∃ (g : t'.G.left) (i : t'.PP.L.ι), t'.G.hom g = y ∧ g ∈ t'.G.left.basicOpen (θ' i) := by
  obtain ⟨w, hw, -⟩ := mu.lin
  have sq := mu.cart.1
  have hW : t'.G.hom ⁻¹ᵁ U' ≤ mu.cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U) := by
    intro g hg
    show t.G.hom (mu.cm.F g) ∈ U
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
    exact hle hg
  obtain ⟨θ', hθ', hval⟩ := GlobalTheory.T.sections_pull_preserve_basic_opens _ _ mu.cm.F t.PP.L t'.PP.L w hw t.PP.isLB t'.PP.isLB _ θ hθ _ hW
  refine ⟨θ', hθ', fun y hy => ?_⟩
  obtain ⟨g, j, hg, hgj⟩ := hne (f y) (hle hy)
  obtain ⟨g', hg', hy'⟩ := Scheme.exists_preimage_of_isPullback sq g y hg
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (t'.PP.isLB.cover.ge (Set.mem_univ g'))
  have hgU : g' ∈ t'.G.hom ⁻¹ᵁ U' := by show t'.G.hom g' ∈ U'; rw [hy']; exact hy
  have hj : mu.cm.F g' ∈ t.PP.L.U j := by rw [hg']; exact (t.G.left.basicOpen_le _ hgj).2
  exact ⟨g', i, hy', (hval g' i j hgU hi hj).2 (by rw [hg']; exact hgj)⟩

theorem exists_chart_of_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H)
    (Xo : Moduli D l) (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (Z : GMod Xo c) (Z' : GMod Xo' c')
    (σ : 𝓞 E ≃+* 𝓞 E) (π : Z'.X ⟶ Z.X) (mu : TwMap σ Z'.t Z.t π), σ H.w0 = H.w0 →
    ∀ (M : GlobalTheory.Reg.MChart Z) (x : Z'.X), π x ∈ M.U → ∃ M' : GlobalTheory.Reg.MChart Z', x ∈ M'.U := by
  intro E _ _ _ H D l l' Xo Xo' c c' Z Z' σ π mu hσ M x hx
  haveI := c'.fin
  haveI : NumberField c'.F := {}
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z'.proj
  have : IsLocallyNoetherian Z'.X := LocallyOfFiniteType.isLocallyNoetherian Z'.s
  obtain ⟨U', hle, hxU, hU', hdom⟩ := GlobalTheory.T.exists_affine_domain_nbhd_normal Z'.X Z'.normal (π ⁻¹ᵁ M.U) x hx
  obtain ⟨θ', hθ', hne'⟩ := exists_secOn_pull mu M.U M.θ M.θ_mem M.θ_ne U' hle
  obtain ⟨v₀, ρ, hlie⟩ := GlobalTheory.T.twisted_map_sends_chart_opens E H D l l' Xo Xo' c c' _ _ _ _ Z Z' σ π mu hσ M U' hU' hle
  exact ⟨⟨U', hU', hdom, θ', hθ', hne', M.n, v₀, ρ, hlie⟩, hxU⟩

end GlobalTheory.ChartPull
