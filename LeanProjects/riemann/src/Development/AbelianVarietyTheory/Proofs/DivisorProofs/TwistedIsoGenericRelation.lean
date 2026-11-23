import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedFrameTriangularThroughStalkFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

namespace GlobalTheory.ShFam.GalCarry.Tw

theorem isDominant_spMap_genericPt {F : Type} [Field F] (Y : Var F) {K : Type} [Field K] (a : Y.Fn →+* K) :
    IsDominant (spMap a ≫ genericPt Y) := by
  constructor
  have hz : (spMap a ≫ genericPt Y) (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X := by
    have : (spMap a ≫ genericPt Y) (IsLocalRing.closedPoint K) ∈ Set.range (Y.X.fromSpecStalk (genericPoint Y.X)) :=
      Set.mem_range.2 ⟨spMap a (IsLocalRing.closedPoint K), rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hg : genericPoint Y.X ∈ closure (Set.range (spMap a ≫ genericPt Y)) :=
    closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self _)) (specializes_iff_mem_closure.1 hz)
  have hu : closure ({genericPoint Y.X} : Set Y.X) = Set.univ := genericPoint_spec Y.X
  rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, ← hu]
  exact closure_minimal (Set.singleton_subset_iff.2 hg) isClosed_closure

theorem algebraMap_stalk_genericPoint {F : Type} [Field F] (Y : Var F) :
    @algebraMap (Y.X.presheaf.stalk (genericPoint Y.X)) Y.X.functionField _ _ (stalkFunctionFieldAlgebra _ _) =
      RingHom.id _ := by
  show (Y.X.presheaf.stalkSpecializes _).hom = _
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem exists_genRel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : Tw Z) (F : Type) [Field F] (e : F ≃+* c.F) (C C' : FlagCpt Z e) (φ : C.Y.X ≅ C'.Y.X), (∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ C.Y.X), T.PtRel C C' p (p ≫ φ.hom)) → ∃ (ψ : C'.Y.Fn →+* C.Y.Fn) (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), T.GenRel C C' φ ψ t₀ := by
  intro E _ _ _ H Dw l Xo c O _ β Z T F _ e C C' φ hrel
  set a : C.Y.Fn →+* AlgebraicClosure C.Y.Fn := algebraMap C.Y.Fn (AlgebraicClosure C.Y.Fn) with ha
  set pb : Sp (AlgebraicClosure C.Y.Fn) ⟶ C.Y.X := spMap a ≫ genericPt C.Y with hpb
  obtain ⟨hπ, χ, f, f', hχ, hpush, hc, hc'⟩ := hrel (AlgebraicClosure C.Y.Fn) pb

  have h1 : φ.hom ≫ C'.π = C.π ≫ T.g.hom := by
    have : IsDominant pb := isDominant_spMap_genericPt C.Y a
    have : IsProper Z.s := projProper O Z.X Z.s Z.proj
    have : IsProper (genStr Z) := inferInstance
    have : IsSeparated (genStr Z ≫ terminal.from (Sp c.F)) := inferInstance
    refine ext_of_isDominant_of_isSeparated (genStr Z ≫ terminal.from (Sp c.F)) (terminal.hom_ext _ _) pb ?_
    rw [← Category.assoc, hπ]
  have : IsDominant φ.hom := inferInstance
  set ψ : C'.Y.Fn →+* C.Y.Fn := GlobalTheory.functionFieldMap φ.hom with hψ
  have h2 : genericPt C.Y ≫ φ.hom = spMap ψ ≫ genericPt C'.Y := (GlobalTheory.specMap_functionFieldMap φ.hom).symm

  have hstr : φ.hom ≫ C'.Y.str = C.Y.str := by
    rw [← C'.π_str, ← C.π_str, ← Category.assoc, h1, Category.assoc, ← Category.assoc T.g.hom, T.g_str]
  have hconst : constF e C.Y = ψ.comp (constF e C'.Y) := by
    have h := GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn C'.Y.str φ.hom
    rw [hstr] at h
    unfold constF
    rw [← RingHom.comp_assoc]
    change (Cartier.constFn C.Y.str).comp _ = ((GlobalTheory.functionFieldMap φ.hom).comp (Cartier.constFn C'.Y.str)).comp _
    rw [h]
  have hx0 : (genericPt C.Y ≫ C.π ≫ genι Z) ≫ T.ρ.hom = spMap ψ ≫ genericPt C'.Y ≫ C'.π ≫ genι Z := by
    rw [← Category.assoc (spMap ψ), ← h2]
    simp only [Category.assoc]
    rw [← Category.assoc φ.hom, h1, Category.assoc, T.g_ι]

  obtain ⟨g₀, hg₀⟩ := T.exists_push C.f0 rfl rfl

  obtain ⟨t, hA⟩ := CarriesAt.tri_of_carries E H Dw l Xo c O β Z F e C (AlgebraicClosure C.Y.Fn) χ _ f pb hc
    (genericPoint C.Y.X) a (constF e C.Y) C.f0 1 rfl (by
      rw [algebraMap_stalk_genericPoint]
      exact C.f0.tri_refl)
  have hpb' : pb ≫ φ.hom = spMap (a.comp ψ) ≫ stalkPt C'.Y (genericPoint C'.Y.X) := by
    rw [hpb, Category.assoc, h2]
    simp [spMap, Spec.map_comp, stalkPt, genericPt]
  obtain ⟨t', hA'⟩ := CarriesAt.tri_of_carries E H Dw l Xo c O β Z F e C' (AlgebraicClosure C.Y.Fn) χ _ f' (pb ≫ φ.hom)
    hc' (genericPoint C'.Y.X) (a.comp ψ) (constF e C'.Y) C'.f0 1 hpb' (by
      rw [algebraMap_stalk_genericPoint]
      exact C'.f0.tri_refl)
  have hB : g₀.Tri a f' (fun τ i => t (T.emb τ) (T.ix i)) := (hg₀.tri_iff hpush fun _ _ => rfl).1 hA

  obtain ⟨k, hk⟩ := C'.f0.exists_isMap ψ hconst hx0
  obtain ⟨kK, hkK⟩ := k.exists_isMap a hB.2.1 hB.1
  obtain ⟨g₀K, hg₀K⟩ := g₀.exists_isMap a hB.2.1 hB.1
  have hkK' : C'.f0.IsMap (a.comp ψ) kK := fun τ i => by
    rw [hkK τ i, hk τ i, ← Category.assoc, ← CarriesAt.spMap_dualMap_comp]
  have hinj : Function.Injective a := a.injective
  have key : ∀ τ, (k.co g₀ τ).BlockTriangular id ∧ ∀ i, IsUnit (k.co g₀ τ i i) := by
    intro τ
    have hU := EigFrame.Tri.co (τ := τ) hA' hkK'
    have hV := EigFrame.Tri.co (τ := τ) hB hg₀K
    have hVt : (g₀K.co f' τ).BlockTriangular id := fun a i h => hV.1 a i h
    have hVd : IsUnit (g₀K.co f' τ).det := g₀K.isUnit_det_co f' τ
    have hW : kK.co g₀K τ = kK.co f' τ * (g₀K.co f' τ)⁻¹ := by
      rw [← kK.co_mul g₀K f' τ, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hVd, Matrix.mul_one]
    have hWt : (kK.co g₀K τ).BlockTriangular id := by
      haveI := Matrix.invertibleOfIsUnitDet _ hVd
      rw [hW]
      exact Matrix.BlockTriangular.mul (fun a i h => hU.1 a i h) (Matrix.blockTriangular_inv_of_blockTriangular hVt)
    have hM : kK.co g₀K τ = (k.co g₀ τ).map a := EigFrame.IsMap.co τ hkK hg₀K hB.1
    have hMt : (k.co g₀ τ).BlockTriangular id := fun i j h => hinj (by
      have := hWt h
      rw [hM, Matrix.map_apply] at this
      rw [this, map_zero])
    exact ⟨hMt, CarriesAt.isUnit_diag_of_blockTriangular hMt (k.isUnit_det_co g₀ τ)⟩
  refine ⟨ψ, fun τ i => ((key τ).2 i).unit, h1, h2, g₀, hg₀, hx0, hconst, fun τ i =>
    ⟨fun j => k.co g₀ τ j i, ((key τ).2 i).unit_spec.symm, fun j hj => (key τ).1 hj, ?_⟩⟩
  rw [← funext (hk τ)]
  exact k.co_spec g₀ τ i

end GlobalTheory.ShFam.GalCarry.Tw
