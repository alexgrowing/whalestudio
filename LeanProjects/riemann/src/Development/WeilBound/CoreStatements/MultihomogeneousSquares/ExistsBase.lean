import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalSncChartSystem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegreeStatement

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

def overCpt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (A : HodgeCpt Y S y)
    {Ω₀ : Type} [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (h₀ : IsCptGen ξ₀) (i : Ω₀ →+* Ω)
    (hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i) : HodgeCpt Y S y where
  X := A.X
  ξ := A.ξ
  all := A.all
  tie := A.tie
  normal := A.normal
  f := A.f
  Ω₀ := Ω₀
  ξ₀ := ξ₀
  gen₀ := h₀
  cst := A.cst
  cst_over := A.cst_over
  fn := i
  fn_over := hi
  t := A.t
  m := A.m
  Li := A.Li
  M := A.M
  ρ := A.ρ
  act := A.act
  S_prime := A.S_prime
  R := A.R
  R_ge := A.R_ge
  tors := A.tors
  vb := A.vb

open Limits GeoModel in

theorem exists_base' (hRes : ResK.ResKStatement) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀]
    (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (hg : IsCptGen ξ₀) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k))
      (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X)
      (y₀ : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Nonempty K ∧ (letI := i.toAlgebra; FiniteDimensional Ω₀ Ω) ∧
      Flat.NormalCpt M₁.ξ ∧ M₁.ξ ≫ f₁ = y₀ ≫ Y.j ∧ M₁.ξ ≫ f₁ = spMap i ≫ ξ₀ ∧
      (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ 4)) ∧ (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4)) ∧
      SncPts M₁.ξ D.dim {p | Char0 M₁.ξ p ∧ p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} ∧
      Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨w₀, -⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ hgen₀
  obtain ⟨cst, -⟩ := exists_cst (Y := Y) w₀
  haveI : CharZero Ω₀ := charZero_of_injective_ringHom cst.injective
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := ChgField.exists_field E H D l Xo c Y Ω₀ ξ₀ S hgen₀ hS
  obtain ⟨K₀, _, J₀, _, yc, X₀, ξ', f₀, bd₀, -, hall₀, htie₀, hf₀, -, -⟩ := GlobalTheory.T.exists_coords_of_generic_point hRes E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, M, h, -, -, hdom, hnorm, hsm⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes K₀ J₀ Ω₀ Ω i yc X₀ ξ' hfin hall₀ htie₀
  have hMξ : M.ξ ≫ h ≫ f₀ = spMap i ≫ ξ₀ := by
    have e : M.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ ξ' := hdom
    rw [← Category.assoc, e, Category.assoc, hf₀]
  have hgenM : GlobalTheory.CompanionTheory.Ar.genPt (M.ξ ≫ h ≫ f₀) ∈ genericPoints Y.X := by
    rw [hMξ]
    show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) ∈ _
    rw [genPt_comp]
    exact hgen₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω _ hgenM
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c _ _ Y Ω₀ ξ₀ Ω y₀ i hinj hg (hy₀ ▸ hMξ)
  have htr : Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
    letI : Algebra Ω₀ Ω := i.toAlgebra
    haveI : FiniteDimensional Ω₀ Ω := hfin
    haveI : FaithfulSMul ℤ Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ Ω₀).mpr Int.cast_injective
    haveI : FaithfulSMul Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective Ω₀ Ω).mpr i.injective
    have htow := trdeg_add_eq ℤ Ω₀ (A := Ω)
    rw [hA, trdeg_eq_zero_iff.2 (Algebra.IsAlgebraic.of_finite Ω₀ Ω), add_zero] at htow
    exact htow.symm
  obtain ⟨U, hd, hAb⟩ := GlobalTheory.T.dense_open_generic_fibre E H D l Xo c Y Ω _ _ M (h ≫ f₀) y₀ hy₀
  have hU := GlobalTheory.T.generic_fibre_open_coords E H D l Xo c Y Ω K₁ J₁ y₁ M (h ≫ f₀) y₀ U hy₀ hsm htr
  have hnm : Tor.IsNormalScheme M.X := ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M.ξ M.tie.gen M.all).2).1 hnorm
  obtain ⟨N, x, X, ξ, f₂, hall, htie, hf₂, hp⟩ := exists_patches_of_res hRes c.F M.X ((h ≫ f₀) ≫ Y.s)
    (GlobalTheory.T.projective_model_over_base E H D l Xo c Y Ω _ _ M (h ≫ f₀)) hnm U hd D.dim hU _ hAb Ω M.ξ M.tie.gen
  obtain ⟨K, _, J, _, y, M₁, g, hne, hdom₁, hn₁, hp₁⟩ := GlobalTheory.T.exists_projective_coord_model Ω X ξ N x D.dim
    (f₂ ⁻¹' ((h ≫ f₀) ⁻¹' abLocus Y.t.G)) hall htie hp
  have hg₁ : M₁.ξ ≫ g = ξ := by
    have e : M₁.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ := hdom₁
    rw [e]; simp
  have hξ₁ : M₁.ξ ≫ g ≫ f₂ ≫ h ≫ f₀ = M.ξ ≫ h ≫ f₀ := by
    rw [← Category.assoc, hg₁, ← Category.assoc, hf₂]
  refine ⟨Ω, inferInstance, inferInstance, K, inferInstance, J, inferInstance, y, M₁, g ≫ f₂ ≫ h ≫ f₀, y₀, i, hne, hfin, hn₁,
    hξ₁.trans hy₀, hξ₁.trans hMξ, fun p hp' => ?_, hroot, ?_, htr⟩
  · rw [hξ₁, hMξ]
    exact htors p hp'
  · convert hp₁ using 4
    simp

theorem stBase : StBase := by
  intro hRes hW E _ _ _ H D l Xo c Y S Ω₀ _ ξ₀ hξ₀ hS hSd
  obtain ⟨Ω, _, _, K₁, _, J₁, _, y₁, M₁, f₁, z₀, i, ⟨k₁⟩, hfin, hN, hz₀, hdomi, htors, hroot, hsnc₁, htr⟩ :=
    exists_base' hRes E H D l Xo c Y Ω₀ ξ₀ hξ₀ S hS
  have hgen₁ : f₁ (GlobalTheory.CompanionTheory.Ar.genPt M₁.ξ) ∈ genericPoints Y.X := by
    have e : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ f₁) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
      rw [hdomi]; exact GeoModel.genPt_comp i ξ₀
    have h0 := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hξ₀
    rw [← e] at h0
    exact h0
  obtain ⟨K₂, _, J₂, _, y₂, bk, bx, A, g, -, -, hdom₂, hf₂, hR₂, hfree, hiso⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ f₁ z₀ hN hz₀ hgen₁ hS hSd
      (fun _ _ => le_rfl) htors hroot
  have hgA : A.ξ ≫ g = M₁.ξ := by
    have e : A.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hsncA : GeoModel.SncPts A.ξ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} :=
    GlobalTheory.T.snc_points_transfer_dominating Ω _ _ _ _ M₁.X A.X M₁.ξ A.ξ g D.dim _ M₁.all A.all M₁.tie A.tie hdom₂ hiso hsnc₁
  have hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i := by
    show A.ξ ≫ A.f = _
    rw [hf₂, ← Category.assoc, hgA]
    exact hdomi
  obtain ⟨bd, hbd, hbd'⟩ := GlobalTheory.T.snc_model_boundary_coords Ω A.X A.ξ K₂ J₂ y₂ D.dim
    {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} A.tie (fun p hp' => hp'.1) hsncA
  have hab : abLocus A.t.G = A.f ⁻¹' abLocus Y.t.G :=
    (Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x).symm
  letI algi : Algebra Ω₀ Ω := i.toAlgebra
  haveI : FiniteDimensional Ω₀ Ω := hfin
  haveI : Nonempty K₂ := ⟨bk k₁⟩
  refine ⟨Ω, inferInstance, inferInstance, K₂, inferInstance, J₂, inferInstance, y₂, overCpt A ξ₀ hξ₀ i hi,
    Module.finrank Ω₀ Ω, inferInstance, rfl, ⟨Module.finrank_pos, rfl⟩,
    (GlobalTheory.T.birational_of_transcendence_degree A.X Ω A.ξ K₂ J₂ y₂ _ A.tie htr).2, ⟨bd, hbd, fun z w hw => ?_⟩, fun p _ => congrFun hR₂ p, hfree⟩
  rw [hbd' z w hw]
  constructor
  · rintro ⟨h, -, h2⟩ hI
    have h3 : centre z ∈ abLocus A.t.G := hI
    rw [hab, hf₂] at h3
    exact h2 h3
  · intro hn
    refine ⟨A.all _, GlobalTheory.T.char_zero_centre_of_complex Ω A.X A.ξ z _ A.tie.gen, fun h => hn ?_⟩
    show centre z ∈ abLocus A.t.G
    rw [hab, hf₂]
    exact h

end SquareStatements
