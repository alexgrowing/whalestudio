import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapPowEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSchemeFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateGluedSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionField
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.RootFrame
open scoped NNReal
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

noncomputable section SlopeTestRemainingChoices

open GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

private theorem finite_Bt : Module.Finite O (Bt P' x0 hu) := by
  haveI : Module.Finite (Localization.Away P'.f) P'.B := P'.fin.finite
  haveI : Module.Finite (OL P' x0 hu) (Bt P' x0 hu) := Module.Finite.base_change _ _ _
  haveI : Module.Finite O (OL P' x0 hu) := inferInstanceAs (Module.Finite O O)
  exact Module.Finite.trans (OL P' x0 hu) (Bt P' x0 hu)

private theorem ex_ch (χ : TorsChar t (spMap x0 ≫ ξ) q) :
    ∃ ch : Hs P' x0 hu ⟶ Gm (Sp O), ∀ (D : Type) [CommRing D] [Algebra O D] [Module.Finite O D]
      (α : Bt P' x0 hu →ₐ[O] D) (w : Over.mk (spMap (algebraMap O D) ≫ spMap x0 ≫ ξ) ⟶ t.G),
      w.left = spMap (α.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left →
        unitOf (ptMap α ≫ ch) = χ.χ D w := by
  haveI := finite_Bt P' x0 hu
  let u₀ : Over.mk (spMap (algebraMap O (Bt P' x0 hu)) ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (sq P' x0 hu)
  have hu₀ : u₀ ^ q = 1 := GlobalTheory.HTMap.tors_of (g := spMap (inB P' x0 hu)) (w := P'.u) rfl P'.fin.tors
  obtain ⟨ch, hch⟩ := GlobalTheory.GmPoints.unitOf_bijective (O := O).2 (χ.χ _ u₀)
  refine ⟨ch, fun D _ _ _ α w hw => Units.ext ?_⟩
  rw [GlobalTheory.GmPoints.unitOf_ptMap, hch]
  exact (χ.nat _ D α u₀ w hu₀ (hw.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)).symm

private theorem ch_mul (χ : TorsChar t (spMap x0 ≫ ξ) q) {ch : Hs P' x0 hu ⟶ Gm (Sp O)}
    (hch : ∀ (D : Type) [CommRing D] [Algebra O D] [Module.Finite O D]
      (α : Bt P' x0 hu →ₐ[O] D) (w : Over.mk (spMap (algebraMap O D) ≫ spMap x0 ≫ ξ) ⟶ t.G),
      w.left = spMap (α.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left →
        unitOf (ptMap α ≫ ch) = χ.χ D w)
    {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π)
    (hm : Mono (aH P' x0 hu hg.1)) (S : Over (Sp O)) (x y z : S ⟶ Hs P' x0 hu)
    (h : z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1)) :
    z ≫ ch = (x ≫ ch) * (y ≫ ch) := by
  haveI := finite_Bt P' x0 hu
  obtain ⟨c, hc₁, hc₂⟩ := exists_mul_factor S x y
  let a : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu := Algebra.TensorProduct.includeLeft
  let b : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu := Algebra.TensorProduct.includeRight
  obtain ⟨z₀, hz₀⟩ := exists_mul_affine P' x0 hu hg a b
  have hz : z = c ≫ z₀ := by
    rw [← cancel_mono (aH P' x0 hu hg.1), h, Category.assoc, hz₀, MonObj.comp_mul, ← Category.assoc, hc₁,
      ← Category.assoc, hc₂]
  obtain ⟨α, rfl⟩ := eq_ptMap' z₀
  have ha := at_alg P' x0 hu a
  have hb := at_alg P' x0 hu b
  let w₁ : Over.mk (spMap (algebraMap O (Bt P' x0 hu ⊗[O] Bt P' x0 hu)) ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  let w₂ : Over.mk (spMap (algebraMap O (Bt P' x0 hu ⊗[O] Bt P' x0 hu)) ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (hb.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  have h12 : (w₁ * w₂).left = spMap (α.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left := by
    rw [← aH_left_π_ptMap P' x0 hu hg.1 α, hz₀]
    exact hg.2 (specO O _) _ _ w₁ w₂ (aH_left_π_ptMap P' x0 hu hg.1 a).symm
      (aH_left_π_ptMap P' x0 hu hg.1 b).symm
  have k : ptMap α ≫ ch = (ptMap a ≫ ch) * (ptMap b ≫ ch) := by
    apply GlobalTheory.GmPoints.unitOf_bijective.1
    rw [GlobalTheory.GmPoints.unitOf_mul, hch _ α _ h12, hch _ a w₁ rfl, hch _ b w₂ rfl]
    exact χ.mul _ w₁ w₂ (GlobalTheory.HTMap.FP.At.tors (w := w₁) ha) (GlobalTheory.HTMap.FP.At.tors (w := w₂) hb)
  rw [hz, Category.assoc, k, MonObj.comp_mul, ← Category.assoc, hc₁, ← Category.assoc, hc₂]

end SlopeTestRemainingChoices

open GlobalTheory.FinPartAt in
set_option maxHeartbeats 1000000 in
private theorem generalized_bernoulli_change_level {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {p : ℕ} [Fact p.Prime] {n : ℕ} [StarRing (𝓞 E)] {R : Type} [CommRing R]
    {ξ : Sp R ⟶ X} (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p)
    (yb : Sp 𝓞_ℂ_[p] ⟶ X) (hy : yb = spMap x0 ≫ ξ) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G yb π)
    (hLR : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P) (tt : P.T) (χ : TorsChar t yb (p ^ n))
    (hW : ∀ (w : Over.mk (spMap (algebraMap 𝓞_ℂ_[p] 𝓞_ℂ_[p]) ≫ yb) ⟶ t.G) (z : GlobalTheory.ChTor.Pts P.A.A),
      w ^ (p ^ n) = 1 → z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w.left →
      algebraMap 𝓞_ℂ_[p] ℂ_[p] (χ.χ 𝓞_ℂ_[p] w : 𝓞_ℂ_[p]ˣ) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]))
    {g : ℕ} (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (h : Fin g → 𝓞_ℂ_[p])
    (he : ∀ i, IsTanAtG t yb (e i)) (hD : DlogIs t p n χ e h) (k : Fin g) (x : LieG P.Gt) (hI : ITie P π x (e k)) :
    h k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  subst hy
  have htors := GlobalTheory.T.hodge_tate_map_pow_eq_one E H X t R ξ (p ^ n) P' 𝓞_ℂ_[p] x0 hu P.G π hg
  have hι := jH_ι P' x0 hu hg.1 htors
  have hopen := GlobalTheory.T.hodge_tate_map_open_immersion E H X t R ξ p n P' x0 hu P π hg htors
  have hm : Mono (aH P' x0 hu hg.1) := ⟨fun a b hab => by
    have h1 : a ≫ jH P' x0 hu hg.1 htors = b ≫ jH P' x0 hu hg.1 htors :=
      GlobalTheory.KernelNoTorsion.torsion_hom_ext (by rw [Category.assoc, Category.assoc, hι, hab])
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (jH P' x0 hu hg.1 htors).left, ← Over.comp_left, ← Over.comp_left, h1]⟩
  have hOFF : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.IsOpenFiniteFlatSubgroup P.G (p ^ n) (jH P' x0 hu hg.1 htors) := by
    refine ⟨hopen, GlobalTheory.T.hodge_tate_scheme_finite E H X t R ξ (p ^ n) P' _ x0 hu,
      GlobalTheory.T.hodge_tate_scheme_flat E H X t R ξ (p ^ n) P' _ x0 hu, fun S => ?_, fun S x y => ?_, fun S x => ?_⟩
    · obtain ⟨z, hz⟩ := exists_unit P' x0 hu hg S
      exact ⟨z, by rw [hι, hz]⟩
    · obtain ⟨z, hz⟩ := GlobalTheory.T.hodge_tate_difference_section E H X t R ξ (p ^ n) P' _ x0 hu P.G π hg S x y
      exact ⟨z, by rw [hι, hz]⟩
    · have key : ∀ m : ℕ, ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) ^ m := by
        intro m
        induction m with
        | zero =>
          obtain ⟨z, hz⟩ := exists_unit P' x0 hu hg S
          exact ⟨z, by rw [hz, pow_zero]⟩
        | succ m ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨z', hz'⟩ := GlobalTheory.T.hodge_tate_difference_section E H X t R ξ (p ^ n) P' _ x0 hu P.G π hg S z x
          exact ⟨z', by rw [hz', hz, pow_succ]⟩
      have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
      obtain ⟨z, hz⟩ := key (p ^ n - 1)
      refine ⟨z, ?_⟩
      rw [hι, hz]
      symm
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel hpos, ← MonObj.comp_pow, htors, MonObj.comp_one]
  obtain ⟨ch, hch⟩ := ex_ch P' x0 hu χ
  have hChar : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.IsCharacter P.G (p ^ n) (jH P' x0 hu hg.1 htors) ch :=
    fun S x y z h => ch_mul P' x0 hu χ hch hg hm S x y z (by rwa [hι] at h)
  have hExt : ∀ (w : specO 𝓞_ℂ_[p] 𝓞_ℂ_[p] ⟶ Hs P' x0 hu) (z : GlobalTheory.ChTor.Pts P.A.A),
      z.left ≫ P.gen = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ (w ≫ jH P' x0 hu hg.1 htors ≫ torsion.ι P.G (p ^ n)).left →
        algebraMap 𝓞_ℂ_[p] ℂ_[p] (unitOf (w ≫ ch) : 𝓞_ℂ_[p]) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
    intro w z hz
    rw [hι] at hz
    obtain ⟨α, rfl⟩ := eq_ptMap' w
    have ha := at_alg P' x0 hu α
    let w₁ : Over.mk (spMap (algebraMap 𝓞_ℂ_[p] 𝓞_ℂ_[p]) ≫ spMap x0 ≫ ξ) ⟶ t.G :=
      GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
    rw [hch _ α w₁ rfl]
    refine hW w₁ z (GlobalTheory.HTMap.FP.At.tors (w := w₁) ha) ?_
    rw [← Category.assoc, hz, Category.assoc, aH_left_π_ptMap]
    rfl
  have hR : (p : 𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) ^ n = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨xG, hC, hxG⟩ := hI
  have hv0 : IsTanAtG t (spMap ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})).comp x0) ≫ ξ)
      (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ e k) := by
    rw [← GlobalTheory.HTMap.spc_assoc]
    exact GlobalTheory.FactorDepth.isTanAtG_map t _ (he k)
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
  rw [e1, show spMap (RingHom.id (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) = 𝟙 _ from Spec.map_id _,
    Category.id_comp] at hβ
  let w₁ : Over.mk (spMap (algebraMap 𝓞_ℂ_[p] (DualNumber (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫
      spMap x0 ≫ ξ) ⟶ t.G := GlobalTheory.HTMap.mkPt _ (hβ.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  have h2 := hD _ _ (GlobalTheory.HTMap.comb_single he k) w₁ rfl
  have hβ' : (liftB P' x0 hu β hβ.1).toRingHom.comp (inB P' x0 hu) = β :=
    RingHom.ext fun z => liftB_inB P' x0 hu β hβ.1 z
  have h5 := hch _ (liftB P' x0 hu β hβ.1) w₁ (by rw [hβ', hβ.2]; rfl)
  have hcmp := cmp_of_corr P n hC (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.isNilpotent_dual hR)
  have hw : ptOf P' x0 hu β hβ.1 ≫ jH P' x0 hu hg.1 htors ≫ torsion.ι P.G (p ^ n) =
      P.cmp _ (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.isNilpotent_dual hR)
        (ptMap (dualBC (Algebra.ofId 𝓞_ℂ_[p] (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}))) ≫ x.1) := by
    rw [hι, hcmp]
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, hβ.2, Over.comp_left, Category.assoc, hxG, ptMap_dualBC_left]
    · rw [Over.w, Over.w]
  have h1 := hLR n (Hs P' x0 hu) (jH P' x0 hu hg.1 htors) hOFF tt ch hChar hExt
    (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) hR x (ptOf P' x0 hu β hβ.1) hw
  rw [ptOf, h5] at h1
  have h3 := congrArg TrivSqZeroExt.snd h1
  have h6 : ∑ i, h i * (Pi.single k 1 : Fin g → 𝓞_ℂ_[p]) i = h k := by simp [Pi.single_apply]
  rw [h2, h6, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
    Ideal.Quotient.algebraMap_eq] at h3
  have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.alLeft P tt).1 x = -((P.al₀ tt).1 x) := rfl
  rw [h4, Ideal.Quotient.eq, sub_neg_eq_add] at h3
  exact h3

theorem UpperTheory.level_reduction_torsion_character :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) [IsLocallyNoetherian X], X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left), IsGrpPullback P.G t.G yb π → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.LevelReduction P → ∀ (tt : P.T) (χ : TorsChar t yb (p ^ n)), (∀ (w : Over.mk (spMap (algebraMap 𝓞_ℂ_[p] 𝓞_ℂ_[p]) ≫ yb) ⟶ t.G) (z : GlobalTheory.ChTor.Pts P.A.A), w ^ (p ^ n) = 1 → z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w.left → algebraMap 𝓞_ℂ_[p] ℂ_[p] (χ.χ 𝓞_ℂ_[p] w : 𝓞_ℂ_[p]ˣ) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p])) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (h : Fin g → 𝓞_ℂ_[p]), (∀ i, IsTanAtG t yb (e i)) → DlogIs t p n χ e h → ∀ (k : Fin g) (x : LieG P.Gt), ITie P π x (e k) → h k + (P.al₀ tt).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
  intro E _ _ _ H X t _ _ p _ n _ P yb π hg hLR tt χ hW g e h he hD k x hI
  have hq : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
  haveI : IsAlgClosed (FractionRing 𝓞_ℂ_[p]) :=
    IsAlgClosed.of_ringEquiv ℂ_[p] _ (FractionRing.algEquiv 𝓞_ℂ_[p] ℂ_[p]).symm.toRingEquiv
  haveI : CharZero 𝓞_ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).charZero
  obtain ⟨P', hP'⟩ := GlobalTheory.HTMap.ex_full hq (splitTors_of_isAlgClosed E H X t _ yb _ hq)
    (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) inferInstance
  have hu : IsUnit (RingHom.id 𝓞_ℂ_[p] P'.f) := by
    by_contra hn
    exact hP'.1 ((IsLocalRing.mem_maximalIdeal _).2 hn)
  refine generalized_bernoulli_change_level P' (RingHom.id _) hu P yb ?_ π hg hLR tt χ hW e h he hD k x hI
  rw [show spMap (RingHom.id 𝓞_ℂ_[p]) = 𝟙 _ from Spec.map_id _, Category.id_comp]
