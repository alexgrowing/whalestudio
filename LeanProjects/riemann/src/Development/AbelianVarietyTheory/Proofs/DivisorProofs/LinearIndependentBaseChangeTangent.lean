import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanBase

attribute [local instance] Over.cartesianMonoidalCategory

theorem linearIndependent_bcTan : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K L : Type} [Field K] [Field L] (φ : K →+* L) {x : Sp K ⟶ X} {x' : Sp L ⟶ X} (hx : spMap φ ≫ x = x') {J : Type} [Fintype J] (b : J → TanM x t.G), LinearIndependent K b → LinearIndependent L (fun i => bcTan (t := t) φ hx (b i)) := by
  intro E _ _ _ H X t K L _ _ φ x x' hx J _ b hb
  classical
  obtain ⟨n, D, hD, hst⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t K x
  have e0 : spMap (RingHom.id K) ≫ x = x := by
    rw [show spMap (RingHom.id K) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  haveI : Module.Finite K (TanM x t.G) := by
    refine Module.finite_def.2 (Submodule.fg_def.2 ⟨Set.range fun i => tanOf (GlobalTheory.LieMet.isTan_map _ e0 (hD i)),
      Set.finite_range _, top_unique fun w _ => ?_⟩)
    have h' := hst K (RingHom.id K) (tv w).left
    rw [e0] at h'
    obtain ⟨a, ha, -⟩ := h' (isTan_tv w)
    rw [(GlobalTheory.LieMet.isComb_iff (fun i => tanOf (GlobalTheory.LieMet.isTan_map _ e0 (hD i))) a w).1 ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B := Module.Basis.sumExtend hb
  have hfin : Finite (J ⊕ Module.Basis.sumExtendIndex hb) := Module.Finite.finite_basis B
  letI : Fintype (J ⊕ Module.Basis.sumExtendIndex hb) := Fintype.ofFinite _
  let e := Fintype.equivFin (J ⊕ Module.Basis.sumExtendIndex hb)
  let B2 := B.reindex e
  have hB : ∀ j, B2 (e (Sum.inl j)) = b j := by
    intro j
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
    simp only [B, Module.Basis.sumExtend, Module.Basis.reindex_apply, Module.Basis.coe_extend,
      Equiv.symm_symm, Equiv.trans_apply, Equiv.sumCongr_apply]
    rfl
  have hv : ∀ i, IsTanAtG t x (tv (B2 i)).left := fun i => isTan_tv (B2 i)
  have hbas : ∀ w, IsTanAtG t x w → ∃! cf, IsCombAtG t x (fun i => (tv (B2 i)).left) cf w := by
    intro w hw
    have key : ∀ cf, IsCombAtG t x (fun i => (tv (B2 i)).left) cf w ↔ tanOf hw = ∑ i, cf i • B2 i :=
      fun cf => GlobalTheory.LieMet.isComb_iff B2 cf (tanOf hw)
    refine ⟨B2.repr (tanOf hw), (key _).2 (B2.sum_repr _).symm, fun cf hcf => ?_⟩
    exact funext (Fintype.linearIndependent_iffₛ.1 B2.linearIndependent _ _
      (((key _).1 hcf).symm.trans (B2.sum_repr _).symm))
  have hv' : ∀ i, IsTanAtG t x' (spMap (dualMap φ) ≫ (tv (B2 i)).left) :=
    fun i => GlobalTheory.LieMet.isTan_map φ hx (hv i)
  have li := GlobalTheory.GradedPieces.linInd_of_basis hv' (GlobalTheory.GradedPieces.basis_map φ hx hv hbas)
  have li2 := li.comp (fun j => e (Sum.inl j)) (e.injective.comp Sum.inl_injective)
  have hf : (fun j => GlobalTheory.LocM.Frm.bcTan (t := t) φ hx (b j)) =
      (fun i => tanOf (hv' i)) ∘ (fun j => e (Sum.inl j)) := by
    funext j
    simp only [Function.comp]
    rw [← hB j]
    rfl
  exact hf ▸ li2

end GlobalTheory.TanBase
