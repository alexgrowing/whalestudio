import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SabExtNormalStOfHomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisibilityOnClosedFibreSpreads
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageGenericFiberIsOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FactorThroughGenericFiberStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef.TriplePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem range_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j = abLocus Y.t.G ∩ Y.s ⁻¹' Set.range (spMap β) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : Y.jQ y ∈ Set.range Y.jQ := ⟨y, rfl⟩
    rw [← Y.ab_gen] at hy
    refine ⟨hy, ?_⟩
    rw [Set.mem_preimage, ← Set.mem_preimage, ← Scheme.Pullback.range_fst]
    exact ⟨Y.jQ y, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [Set.mem_preimage, ← Set.mem_preimage, ← Scheme.Pullback.range_fst] at h2
    obtain ⟨p, rfl⟩ := h2
    have hp : p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := h1
    rw [Y.ab_gen] at hp
    obtain ⟨y, rfl⟩ := hp
    exact ⟨y, rfl⟩

theorem factor_j {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {T : Scheme.{0}} (f : T ⟶ Y.X)
    (hf : Set.range f ⊆ Set.range Y.j) (h : T ⟶ Sp c.F) (hh : h ≫ spMap β = f ≫ Y.s) :
    ∃ u : T ⟶ Xo.XF c, u ≫ Y.j = f := by
  haveI := Y.jQ_open
  let p : T ⟶ pullback Y.s (spMap β) := pullback.lift f h hh.symm
  have hp : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨x, rfl⟩
    rw [← Y.ab_gen]
    show (p ≫ pullback.fst _ _) x ∈ abLocus _
    rw [pullback.lift_fst]
    exact ((range_j Y).le (hf ⟨x, rfl⟩)).1
  refine ⟨IsOpenImmersion.lift Y.jQ p hp, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.TorRef.TriplePull

namespace GlobalTheory.TorRef.TriplePull

theorem sab_of_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ξ' : Sp R' ⟶ Z.X) (t' : SAB H (Sp R')), IsCN R' → Dense (ξ' ⁻¹' Set.range Z.j) → SABMap t' X.t (ξ' ≫ π) → Nonempty (SABMap t' Z.t ξ') := by
  intro E _ _ _ H D l Xo c X Z π hπ R' _ _ _ ξ' t' hR hd m
  obtain ⟨hN, hIC, -, -⟩ := hR
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨t'', ⟨n''⟩⟩ := exists_sabPull ξ' Z.t
  have hU : IsOpen (ξ' ⁻¹' Set.range Z.j) := by
    have e : ξ' ⁻¹' Set.range Z.j =
        abLocus t''.G ∩ (ξ' ≫ Z.s) ⁻¹' Set.range (spMap (algebraMap (𝓞 c.F) c.F)) := by
      rw [range_j, Set.preimage_inter]
      congr 1
      ext x
      exact abLocus_pullback abLocusOne Z.t.semi n''.cart.1 x
    rw [e]
    exact (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t''.G t''.semi).inter (GlobalTheory.T.preimage_generic_fiber_isOpen _ _ _ _)
  let U : (Sp R').Opens := ⟨_, hU⟩
  have hUr : Set.range (U.ι ≫ ξ') ⊆ Set.range Z.j := by
    rintro _ ⟨x, rfl⟩
    have hx : U.ι x ∈ (U : Set (Sp R')) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    exact hx
  obtain ⟨h, hh⟩ := GlobalTheory.T.factor_through_generic_fiber (𝓞 c.F) c.F U.toScheme ((U.ι ≫ ξ') ≫ Z.s) (by
    rintro _ ⟨x, rfl⟩
    exact ((range_j Z).le (hUr ⟨x, rfl⟩)).2)
  obtain ⟨u, hu⟩ := factor_j Z (U.ι ≫ ξ') hUr h hh
  obtain ⟨t₀, ⟨n₀⟩⟩ := exists_sabPull u Z.oF.t
  have hp0 : IsProper t₀.G.hom := MorphismProperty.of_isPullback (P := @IsProper) n₀.cart.1 Z.oF.proper
  obtain ⟨a1, -⟩ := ObjMaps.exists_sab_comp Z.m n₀
  obtain ⟨a, -⟩ := ObjMaps.exists_sab_cancel n'' (hu ▸ a1 : SABMap t₀ Z.t (U.ι ≫ ξ'))
  obtain ⟨zx, -⟩ := ObjMaps.exists_sab_cancel X.m0.toSABMap
    (by rw [Category.id_comp]; exact Z.m0.toSABMap : SABMap Z.oF.t Xo.univ.t (𝟙 _ ≫ pullback.fst _ _))
  obtain ⟨c1, -⟩ := ObjMaps.exists_sab_comp zx n₀
  obtain ⟨c2, -⟩ := ObjMaps.exists_sab_comp X.m c1
  have hux : (u ≫ 𝟙 _) ≫ X.jQ ≫ pullback.fst _ _ = U.ι ≫ ξ' ≫ π := by
    rw [Category.comp_id]
    change u ≫ X.j = _
    rw [← hπ, ← Category.assoc, hu, Category.assoc]
  obtain ⟨a', -⟩ := ObjMaps.exists_sab_cancel m (hux ▸ c2 : SABMap t₀ X.t (U.ι ≫ ξ' ≫ π))
  haveI : IsNoetherianRing R' := hN
  haveI : IsIntegrallyClosed R' := hIC
  have hNorm : Geo.Tor.IsNormalScheme (Sp R') := GlobalTheory.IsNormalScheme.pred _
  have hDom : IsDominant U.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact hd⟩
  obtain ⟨b, -⟩ := sabExtNormalSt_of_homExtNormalSt GlobalTheory.homExtNormal E H (Sp R') U.toScheme U.ι hNorm
    inferInstance hDom t₀ t' t'' a' a hp0
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp n'' b
  exact ⟨(Category.id_comp ξ') ▸ n⟩

end GlobalTheory.TorRef.TriplePull
