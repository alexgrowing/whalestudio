import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapPowEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateGluedSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateUnitTorsionPointStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

set_option maxHeartbeats 1000000 in

theorem levelHT_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ) (b : P'.Bˣ), P'.Gl κ b →
    ∀ x0 : R →+* 𝓞_ℂ_[p], P'.Full ((IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap x0) →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
      PtOn Y (spMap x0 ≫ ξ) yy P π ψ → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P → ∀ tt : P.T,
      (∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) →
    ∀ hvec : Fin g → 𝓞_ℂ_[p],
      (∀ (k : Fin g) (β : P'.B →+* DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})),
        P'.At ((algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0)
          (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k) β →
        (β b).snd = Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (hvec k)) →
    ∀ (k : Fin g) (x : LieG P.Gt), ITie P π x (spMap (dualMap x0) ≫ e k) →
      hvec k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ R _ _ ξ g e he P' κ b hb x0 hF yy P π ψ hOn hLR tt hW hvec hD k x hI
  have hu : IsUnit (x0 P'.f) := by
    by_contra hn
    exact hF.1 (Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 hn))
  have hg := hOn.2.1
  have htors := GlobalTheory.T.hodge_tate_map_pow_eq_one E H Y.X Y.t R ξ (p ^ n) P' 𝓞_ℂ_[p] x0 hu P.G π hg
  have hι := jH_ι P' x0 hu hg.1 htors
  have hOFF : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.IsOpenFiniteFlatSubgroup P.G (p ^ n) (jH P' x0 hu hg.1 htors) := by
    refine ⟨GlobalTheory.T.hodge_tate_map_open_immersion E H Y.X Y.t R ξ p n P' x0 hu P π hg htors, GlobalTheory.T.hodge_tate_scheme_finite E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu,
      GlobalTheory.T.hodge_tate_scheme_flat E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu, fun S => ?_, fun S x y => ?_, fun S x => ?_⟩
    · obtain ⟨z, hz⟩ := exists_unit P' x0 hu hg S
      exact ⟨z, by rw [hι, hz]⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.T.hodge_tate_difference_section E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu P.G π hg S x y
      exact ⟨z, by rw [hι, hz]⟩
    · have key : ∀ m : ℕ, ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) ^ m := by
        intro m
        induction m with
        | zero =>
          obtain ⟨z, hz⟩ := exists_unit P' x0 hu hg S
          exact ⟨z, by rw [hz, pow_zero]⟩
        | succ m ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨z', hz'⟩ := GlobalTheory.T.hodge_tate_difference_section E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu P.G π hg S z x
          exact ⟨z', by rw [hz', hz, pow_succ]⟩
      have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
      obtain ⟨z, hz⟩ := key (p ^ n - 1)
      refine ⟨z, ?_⟩
      rw [hι, hz]
      symm
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, ← MonObj.comp_pow, htors, MonObj.comp_one]
  have hChar : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.IsCharacter P.G (p ^ n) (jH P' x0 hu hg.1 htors) (chi P' x0 hu b) :=
    fun S x y z h => GlobalTheory.T.hodge_tate_glued_section E H Y.X Y.t R ξ (p ^ n) P' _ x0 hu P.G π hg κ b hb S x y z (by rwa [hι] at h)
  have hExt : ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A),
      z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ jH P' x0 hu hg.1 htors ≫ torsion.ι P.G (p ^ n)).left →
        algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ chi P' x0 hu b) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
    intro w z hz
    rw [hι] at hz
    exact GlobalTheory.T.hodge_tate_unit_torsion_point E H Y.X Y.t R ξ p n P' x0 hu P π hg b tt hW w z hz
  have hR : (p : 𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨xG, hC, hxG⟩ := hI
  have hv0 : IsTanAtG Y.t (spMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0) ≫ ξ)
      (spMap (dualMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) ≫ e k) :=
    GlobalTheory.FactorDepth.isTanAtG_map Y.t _ (he.1 k)
  have hq : ((p ^ n : ℕ) : 𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) = 0 := GlobalTheory.HTMap.cast_quot _ p n
  have hu' : IsUnit ((RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})))
      (((algebraMap (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
        ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) P'.f)) :=
    hu.map ((RingHom.id _).comp ((algebraMap _ (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
      (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))))
  obtain ⟨β, hβ⟩ := GlobalTheory.HTMap.tan_at P' hv0 hq (RingHom.id _) hu'
  have e1 : (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
      ((algebraMap (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp
        ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) =
      (algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))).comp x0 :=
    by rw [RingHom.id_comp, ← RingHom.comp_assoc]; exact congrArg (fun f => RingHom.comp f x0) (alg_dual_mk _)
  have e2 : spMap (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫
      spMap (dualMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0)) ≫ e k =
      spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ spMap (dualMap x0) ≫ e k := by
    rw [show spMap (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) = 𝟙 _ from Spec.map_id _,
      Category.id_comp, GlobalTheory.HTMap.spc_assoc (dualMap x0) (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) (e k),
      GlobalTheory.HTMap.dual_comp]
  rw [e1, e2] at hβ
  have h2 := hD k β hβ
  have hcmp := cmp_of_corr P n hC (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.isNilpotent_dual hR)
  have hw : ptOf P' x0 hu β hβ.1 ≫ jH P' x0 hu hg.1 htors ≫ torsion.ι P.G (p ^ n) =
      P.cmp _ (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.isNilpotent_dual hR)
        (ptMap (dualBC (Algebra.ofId 𝓞_ℂ_[p] (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ x.1) := by
    rw [hι, hcmp]
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, hβ.2, Over.comp_left, Category.assoc, hxG, ptMap_dualBC_left]
    · rw [Over.w, Over.w]
  have h1 := hLR n (Hs P' x0 hu) (jH P' x0 hu hg.1 htors) hOFF tt (chi P' x0 hu b) hChar hExt
    (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) hR x (ptOf P' x0 hu β hβ.1) hw
  rw [unitOf_ptOf_chi] at h1
  have h3 := congrArg TrivSqZeroExt.snd h1
  rw [h2, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
    Ideal.Quotient.algebraMap_eq] at h3
  have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.alLeft P tt).1 x = -((P.al₀ tt).1 x) := rfl
  rw [h4, Ideal.Quotient.eq, sub_neg_eq_add] at h3
  exact h3

end GlobalTheory.FinPartAt
