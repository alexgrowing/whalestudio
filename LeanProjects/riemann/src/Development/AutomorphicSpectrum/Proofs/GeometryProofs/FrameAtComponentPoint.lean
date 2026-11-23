import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenConditionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasisStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangentsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames

theorem exists_affine_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ p₀ hO hτ h1 h2 h3 h4 hp₀
  obtain ⟨hinj, hnoeth, hfr⟩ := hO
  haveI := hnoeth
  have := projProper _ _ _ Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3c, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ ⟨hinj, hnoeth, hfr⟩ hτ
  obtain ⟨g, b, hb, hS⟩ := h3c p₀ hp₀
  obtain ⟨S₁, hS₁⟩ := hS τ
  obtain ⟨S₂, hS₂⟩ := hS (ComplexEmbedding.conjugate τ)
  obtain ⟨hspan, N, hpN, hN⟩ := GlobalTheory.T.lattice_frame_open_condition Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ g b hb
  have e₁ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) p₀ g b S₁ Z.gen hspan hb.2 hS₁
  have e₂ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) p₀ g b S₂
    Z.gen hspan hb.2 hS₂
  have card : ∀ (S : Finset (Fin g)) (n : ℕ) (u : Fin n → Z.V), LinearIndependent Z.Ω u →
      Submodule.span Z.Ω (Set.range u) = Submodule.span Z.Ω (b '' S) → S.card = n := by
    intro S n u hu hsp
    have a₁ := finrank_span_eq_card hu
    have a₂ := finrank_span_eq_card (hb.1.comp (Subtype.val : S → Fin g) Subtype.val_injective)
    have a₃ : Set.range (b ∘ (Subtype.val : S → Fin g)) = b '' S := by
      rw [Set.range_comp, Subtype.range_coe]
    rw [a₃, ← hsp, a₁] at a₂
    simpa using a₂.symm
  have c₁ := card S₁ D.p b₁ h1 (h2.trans e₁)
  have c₂ := card S₂ D.q b₂ h3 (h4.trans e₂)
  let ι₁ := S₁.orderEmbOfFin c₁
  let ι₂ := S₂.orderEmbOfFin c₂
  have r₁ : Set.range (b ∘ ι₁) = b '' S₁ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have r₂ : Set.range (b ∘ ι₂) = b '' S₂ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  obtain ⟨W, hW, hWd⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X p₀.1
  have hmem : ∀ i, b i ∈ Z.M.lat p₀ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨A, hA, EB, i₁, i₂, MB, e, hpA, hAN, hval⟩ := GlobalTheory.T.lattice_sections_affine_model Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ (N ⊓ W) (Fin g) b ⟨hpN, hW⟩ hmem
  have hd : IsDomain Γ(Y.X, A) := hWd A hpA (hAN.trans inf_le_right)
  have hcl := GlobalTheory.T.affine_domain_generic_specializes Y.X Z.Ω _ A hA p₀ Z.gen hd hpA
  have hcA : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X), y = spMap f ≫ hA.fromSpec → centre y ∈ A := by
    intro f y hy
    have h5 : centre y ∈ Set.range hA.fromSpec := by
      subst hy
      exact ⟨spMap f (IsLocalRing.closedPoint ℂ), (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [hA.range_fromSpec] at h5
  refine ⟨A, hA, EB, i₁, i₂, MB, e ∘ ι₁, e ∘ ι₂, b ∘ ι₁, b ∘ ι₂, hpA, fun q hq => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.p b ι₁ ι₁.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₁]; exact e₁)
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.q b ι₂ ι₂.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₂]; exact e₂)
  · intro f y v w hy hs hv hw
    have hyA := hcA f y hy
    have h := hcl _ hyA
    have hq := (hN ⟨centre y, h⟩ (hAN hyA).1).2
    exact ⟨GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z τ σ D.p _ y h v hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.p b ι₁ ι₁.injective hb.1 hq (by rw [r₁]; exact e₁))
        (fun i => hval y f h hy (ι₁ i) (v i) (hv i)),
      GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z _ σ D.q _ y h w hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.q b ι₂ ι₂.injective hb.1 hq (by rw [r₂]; exact e₂))
        (fun j => hval y f h hy (ι₂ j) (w j) (hw j))⟩
  · intro f y v w hy h hv hw
    exact ⟨fun i => hval y f h hy (ι₁ i) (v i) (hv i), fun j => hval y f h hy (ι₂ j) (w j) (hw j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames
