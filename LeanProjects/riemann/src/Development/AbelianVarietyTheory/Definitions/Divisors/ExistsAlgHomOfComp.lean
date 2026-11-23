import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ModelChartLiftCoordsGeneratorIndep
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieBasisCoordinatesBijectiveTangent
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrPtTie
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppLEInjective
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

section Glue

theorem exists_algHom_of_comp {K S A B : Type} [CommRing K] [CommRing S] [Algebra K S] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (f : S →ₐ[K] A) (g : S →ₐ[K] B) (χ : A →+* B) (h : ∀ r, χ (f r) = g r) :
    ∃ χ' : A →ₐ[K] B, (∀ a, χ' a = χ a) ∧ χ'.comp f = g :=
  ⟨{ χ with commutes' := fun r => by rw [← f.commutes, ← g.commutes]; exact h _ }, fun _ => rfl, AlgHom.ext h⟩

theorem glue_val {K S : Type} [CommRing K] [CommRing S] [Algebra K S] {Z : Scheme.{0}} (z : Sp S ⟶ Z) {J : Type}
    {U : J → Z.Opens} (hc : ⨆ k, U k = ⊤)
    (val : ∀ (S' : Type) [CommRing S'] [Algebra K S'] (ψ : S →ₐ[K] S') (k : J),
      ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k → S')
    (nat : ∀ (S' S'' : Type) [CommRing S'] [Algebra K S'] [CommRing S''] [Algebra K S''] (ψ : S →ₐ[K] S')
      (χ : S' →ₐ[K] S'') (k k' : J) (h : ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k)
      (h' : ⊤ ≤ (spMap (χ.comp ψ).toRingHom ≫ z) ⁻¹ᵁ U k'), val S'' (χ.comp ψ) k' h' = χ (val S' ψ k h)) :
    ∃! a : S, ∀ (S' : Type) [CommRing S'] [Algebra K S'] (ψ : S →ₐ[K] S') (k : J)
      (h : ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k), ψ a = val S' ψ k h := by
  let lo (f : S) : S →ₐ[K] Localization.Away f := IsScalarTower.toAlgHom K S (Localization.Away f)
  let t : Set S := {f | ∃ k, ⊤ ≤ (spMap (lo f).toRingHom ≫ z) ⁻¹ᵁ U k}
  have ht : Ideal.span t = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum S := ⟨m, hm.isPrime⟩
    have : z p ∈ ⨆ k, U k := by rw [hc]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    obtain ⟨_, ⟨f, rfl⟩, hf, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ ((z ⁻¹ᵁ U k : (Sp S).Opens) : Set (Sp S)) from hk) (z ⁻¹ᵁ U k).isOpen
    refine hf (hle (Ideal.subset_span ⟨k, fun q _ => hsub ?_⟩))
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).le ⟨q, rfl⟩
  have comp : ∀ {S' S'' : Type} [CommRing S'] [Algebra K S'] [CommRing S''] [Algebra K S''] (ψ : S →ₐ[K] S')
      (χ : S' →ₐ[K] S'') (k : J), ⊤ ≤ (spMap ψ.toRingHom ≫ z) ⁻¹ᵁ U k →
      ⊤ ≤ (spMap (χ.comp ψ).toRingHom ≫ z) ⁻¹ᵁ U k := fun ψ χ k h => by
    rw [show spMap (χ.comp ψ).toRingHom = spMap χ.toRingHom ≫ spMap ψ.toRingHom from (spMap_comp' _ _).symm,
      Category.assoc]
    exact le_preimage_comp _ h
  have vcongr : ∀ {S' : Type} [CommRing S'] [Algebra K S'] (ψ ψ' : S →ₐ[K] S') (e : ψ = ψ') k k' h h',
      val S' ψ k h = val S' ψ' k' h' := by
    intro S' _ _ ψ ψ' e k k' h h'
    subst e
    exact nat S' S' ψ (AlgHom.id K S') k' k h' h
  obtain ⟨a, ha, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top t ht
    (fun f => val _ (lo f.1) f.2.choose f.2.choose_spec) (fun f g => by
      obtain ⟨χ₁, h₁, e₁⟩ := exists_algHom_of_comp (K := K) (lo f.1) (lo (f.1 * g.1))
        (IsLocalization.Away.awayToAwayRight f.1 g.1) (fun r => IsLocalization.Away.awayToAwayRight_eq f.1 g.1 r)
      obtain ⟨χ₂, h₂, e₂⟩ := exists_algHom_of_comp (K := K) (lo g.1) (lo (f.1 * g.1))
        (IsLocalization.Away.awayToAwayLeft g.1 f.1) (fun r => IsLocalization.Away.awayToAwayLeft_eq g.1 f.1 r)
      have a1 := nat _ _ (lo f.1) χ₁ f.2.choose f.2.choose f.2.choose_spec (comp _ χ₁ _ f.2.choose_spec)
      have a2 := nat _ _ (lo g.1) χ₂ g.2.choose g.2.choose g.2.choose_spec (comp _ χ₂ _ g.2.choose_spec)
      rw [← h₁, ← h₂, ← a1, ← a2]
      exact vcongr _ _ (e₁.trans e₂.symm) _ _ _ _)
  refine ⟨a, fun S' _ _ ψ k h => ?_, fun b hb => hu b fun f => hb _ (lo f.1) _ _⟩
  have ht' : Ideal.span (ψ '' t) = ⊤ := by
    rw [← Ideal.map_span ψ t, ht, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ ht'
  funext ⟨_, f, hf, rfl⟩
  let lo' : S' →ₐ[K] Localization.Away (ψ f) := IsScalarTower.toAlgHom K S' _
  let χ : Localization.Away f →ₐ[K] Localization.Away (ψ f) := IsLocalization.Away.mapₐ _ _ ψ f
  have e : χ.comp (lo f) = lo'.comp ψ := AlgHom.ext fun r => by simp [χ, lo, lo', IsLocalization.Away.map]
  show lo' (ψ a) = lo' (val S' ψ k h)
  rw [← nat _ _ ψ lo' k k h (comp _ _ _ h), ← vcongr _ _ e _ _ (comp _ _ _ hf.choose_spec),
    nat _ _ _ χ _ _ hf.choose_spec, ← ha ⟨f, hf⟩]
  exact (congrArg (fun g : S →ₐ[K] _ => g a) e).symm

end Glue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

section ToModel

variable {S S' : Type} [CommRing S] [CommRing S']

variable (Y) in

def liftTan (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt (y ≫ pullback.fst _ _) w) :
    Sp (DualNumber S) ⟶ Y.oF.t.G.left :=
  Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ y) (by rw [hw.1, Category.assoc])

theorem liftTan_univ (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt (y ≫ pullback.fst _ _) w) : liftTan Y y hw ≫ Y.m0.toSABMap.φ = w := Y.m0.cart.1.lift_fst _ _ _

theorem liftTan_over (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt (y ≫ pullback.fst _ _) w) :
    liftTan Y y hw ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y := Y.m0.cart.1.lift_snd _ _ _

theorem isTanAtG_liftTan (y : Sp S ⟶ Xo.XF c) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt (y ≫ pullback.fst _ _) w) : IsTanAtG Y.t (y ≫ Y.j) (liftTan Y y hw ≫ Y.m.φ) := by
  have h1 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ liftTan Y y hw = (1 : Over.mk y ⟶ Y.oF.t.G).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, liftTan_univ, hw.2]
      exact grpPull_one Y.m0.cart (Over.mk y)
    · have hid : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S :=
        RingHom.ext fun r => by simp
      rw [Category.assoc, liftTan_over, ← Category.assoc, spMap_comp', hid, Over.w]
      exact (congrArg (· ≫ y) (Spec.map_id _)).trans (Category.id_comp _)
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Y.m.cart.1.w, ← Category.assoc, liftTan_over, Category.assoc]
    rfl
  · rw [← Category.assoc, h1]
    exact (grpPull_one Y.m.cart (Over.mk y)).symm

variable (Y) in

def toModel (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) : TanM x Y.t.G :=
  mkT (ovT (t := Y.t) (v := liftTan Y y (h₀ ▸ hw) ≫ Y.m.φ) (hx ▸ isTanAtG_liftTan y (h₀ ▸ hw))) (smT_zero_ovT _)

theorem toModel_left (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) :
    (tv (toModel Y y h₀ hx hw)).left = liftTan Y y (h₀ ▸ hw) ≫ Y.m.φ := rfl

theorem toModel_eq_iff (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) (v : TanM x Y.t.G) :
    toModel Y y h₀ hx hw = v ↔ ∃ u : Sp (DualNumber S) ⟶ Y.oF.t.G.left,
      u ≫ Y.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y ∧ u ≫ Y.m0.toSABMap.φ = w ∧
        u ≫ Y.m.φ = (tv v).left := by
  constructor
  · rintro rfl
    exact ⟨_, liftTan_over _ _, liftTan_univ _ _, rfl⟩
  · rintro ⟨u, h1, h2, h3⟩
    apply tan_ext_left
    rw [toModel_left, ← h3]
    congr 1
    exact Y.m0.cart.1.hom_ext ((liftTan_univ _ _).trans h2.symm) ((liftTan_over _ _).trans h1.symm)

theorem toModel_injective (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀) {x : Sp S ⟶ Y.X}
    (hx : y ≫ Y.j = x) {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) (hw' : IsTanAt x₀ w')
    (e : toModel Y y h₀ hx hw = toModel Y y h₀ hx hw') : w = w' := by
  have h : liftTan Y y (h₀ ▸ hw) = liftTan Y y (h₀ ▸ hw') :=
    Y.m.cart.1.hom_ext (congrArg (fun v => (tv v).left) e) ((liftTan_over _ _).trans (liftTan_over _ _).symm)
  exact (liftTan_univ y _).symm.trans ((congrArg (· ≫ Y.m0.toSABMap.φ) h).trans (liftTan_univ y _))

theorem tanPull_toModel (φ : S →+* S') (y : Sp S ⟶ Xo.XF c) {x₀ : Sp S ⟶ Xo.X} (h₀ : y ≫ pullback.fst _ _ = x₀)
    {x : Sp S ⟶ Y.X} (hx : y ≫ Y.j = x) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w)
    {y' : Sp S' ⟶ Xo.XF c} (ey : spMap φ ≫ y = y') {x₀' : Sp S' ⟶ Xo.X} (h₀' : y' ≫ pullback.fst _ _ = x₀')
    {x' : Sp S' ⟶ Y.X} (hx' : y' ≫ Y.j = x') (e : spMap φ ≫ x = x') {w' : Sp (DualNumber S') ⟶ Xo.univ.t.G.left}
    (hw' : IsTanAt x₀' w') (ew : w' = spMap (dualMap φ) ≫ w) :
    tanPull φ e (toModel Y y h₀ hx hw) = toModel Y y' h₀' hx' hw' := by
  refine ((toModel_eq_iff y' h₀' hx' hw' _).2 ⟨spMap (dualMap φ) ≫ liftTan Y y (h₀ ▸ hw), ?_, ?_, ?_⟩).symm
  · rw [Category.assoc, liftTan_over, ← ey, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp',
      dualMap_comp_alg]
  · rw [Category.assoc, liftTan_univ, ew]
  · rw [Category.assoc]; rfl

variable [Algebra c.F S]

theorem xF_ext {y y' : Sp S ⟶ Xo.XF c} (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S))
    (hy' : y' ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (e : y ≫ Y.j = y' ≫ Y.j) : y = y' := by
  have := Y.jQ_open
  rw [← cancel_mono Y.jQ]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]; exact e
  · rw [Category.assoc, Category.assoc, Y.jQ_over, hy, hy']

theorem vec_iff_toModel {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {x₀ : Sp S ⟶ Xo.X}
    (Λ : M.Lift (ev x M.U h) x₀) {y : Sp S ⟶ Xo.XF c} (ey : Λ.xF = y) (h₀ : y ≫ pullback.fst _ _ = x₀)
    (hx : y ≫ Y.j = x) (cv : Fin M.n → S) {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hw : IsTanAt x₀ w) :
    Λ.Vec cv w ↔ toModel Y y h₀ hx hw = vec M x h cv := by
  have fwd : ∀ w (hw : IsTanAt x₀ w), Λ.Vec cv w → toModel Y y h₀ hx hw = vec M x h cv := by
    rintro _ hw ⟨v', u', h1, h2, rfl⟩
    refine (toModel_eq_iff y h₀ hx hw _).2 ⟨u'.left ≫ Λ.m'.φ, ?_, ?_, ?_⟩
    · rw [Category.assoc, Λ.m'.cart.1.w, ← Category.assoc, Over.w, ey]; rfl
    · rw [Category.assoc, ← Λ.liftedChartMap_eq]
    · rw [Category.assoc, ← Λ.matrix_two_by_two_congr]
      have e := congrArg (fun V => V.left) ((PullbackSections.isLieComb_iff Λ.m2.cart cv v' u').1 h2)
      refine e.trans ?_
      have hid : spMap (RingHom.id S) ≫ x = spMap (ev x M.U h) ≫ M.hU.fromSpec :=
        ((congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp _)).trans (spMap_ev x M.hU h).symm
      have hl : ∀ v : TanM x Y.t.G, (tv (tanPull (RingHom.id S) hid v)).left = (tv v).left := fun v =>
        (congrArg (· ≫ (tv v).left) (GlobalTheory.ModelChart.spMap_dualMapR_id S)).trans (Category.id_comp _)
      rw [← hl, vec_apply, map_sum, tv_sum']
      refine congrArg Over.Hom.left (Finset.prod_congr rfl fun j _ => ?_)
      rw [map_smulₛₗ, PullbackSections.tv_smul]
      congr 1
      apply Over.OverMorphism.ext
      rw [hl, lieBasis_left]
      exact h1 j
  refine ⟨fwd w hw, fun e => ?_⟩
  obtain ⟨b1, b2, -⟩ := vec_bijective E H Dw l Xo c O β Y M S _ x₀ Λ
  obtain ⟨w', hw', -⟩ := b1 cv
  rwa [toModel_injective y h₀ hx hw (b2 _ _ hw') (e.trans (fwd w' _ hw').symm)]

def frX (P : FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift P.x (spMap (algebraMap c.F S)) (P.x_over.trans (spMap_comp' _ _).symm)

theorem frX_fst (P : FrPt Xo c S) : frX P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _

theorem frX_snd (P : FrPt Xo c S) : frX P ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem eq_frX (P : FrPt Xo c S) {y : Sp S ⟶ Xo.XF c} (h₁ : y ≫ pullback.fst _ _ = P.x)
    (h₂ : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) : y = frX P :=
  pullback.hom_ext (h₁.trans (frX_fst P).symm) (h₂.trans (frX_snd P).symm)

theorem frX_frMap [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P') :
    spMap ψ.toRingHom ≫ frX P = frX P' :=
  eq_frX P' (by rw [Category.assoc, frX_fst, h.1]) (by
    rw [Category.assoc, frX_snd, spMap_comp']
    exact congrArg spMap ψ.comp_algebraMap)

variable (Y) in

def frVec (P : FrPt Xo c S) {x : Sp S ⟶ Y.X} (hx : frX P ≫ Y.j = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    TanM x Y.t.G := toModel Y (frX P) (frX_fst P) hx (P.tan σ i)

theorem tanPull_frVec [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {P : FrPt Xo c S} {P' : FrPt Xo c S'} (h : FrMap ψ P P')
    {x : Sp S ⟶ Y.X} (hx : frX P ≫ Y.j = x) {x' : Sp S' ⟶ Y.X} (hx' : frX P' ≫ Y.j = x')
    (e : spMap ψ.toRingHom ≫ x = x') (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    tanPull ψ.toRingHom e (frVec Y P hx σ i) = frVec Y P' hx' σ i :=
  tanPull_toModel _ _ _ _ _ (frX_frMap h) _ _ _ _ (h.2.1 σ i)

variable (c) in

def eigLie (x : Sp S ⟶ Y.X) (σ : E →+* ℂ) : Submodule S (TanM x Y.t.G) where
  carrier := {v | ∀ a : 𝓞 E, actR Y.t.act a v = algebraMap c.F S (embK c σ a) • v}
  zero_mem' := fun a => by rw [map_zero, smul_zero]
  add_mem' := fun hu hv a => by rw [map_add, hu a, hv a, smul_add]
  smul_mem' := fun r v hv a => by rw [map_smul, hv a, smul_comm]

theorem vec_mem_eigLie (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (σ : E →+* ℂ) (cv : Fin M.n → S) :
    vec M x h cv ∈ eigLie c x σ ↔ M.Eig (ev x M.U h) σ cv :=
  forall_congr' fun a => by rw [actR_vec, ← map_smul, (vec M x h).injective.eq_iff]

end ToModel

section Theta

variable {S T : Type} [CommRing S] [CommRing T]

theorem ev_appTop {Z Z' : Scheme.{0}} (z : Sp S ⟶ Z') (π : Z' ⟶ Z) (a : Γ(Z, ⊤)) :
    ev z ⊤ le_top (π.appTop.hom a) = ev (z ≫ π) ⊤ le_top a :=
  (congrArg (fun f => ev z ⊤ le_top (CommRingCat.Hom.hom f a)) (Scheme.Hom.appLE_eq_app (f := π) (U := ⊤)).symm).trans
    (ev_appLE z π le_rfl le_top le_top a)

theorem spMap_ev_top (ρ : Sp T ⟶ Sp S) : spMap ((ev ρ ⊤ le_top).comp (toΓ S)) = ρ := by
  have h := spMap_ev ρ (isAffineOpen_top (Sp S)) le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [← spMap_comp']
  exact h

def secMul {Z : Scheme.{0}} {L : LB Z} (g : Γ(Z, ⊤)) (s : L.Sec) : L.Sec where
  f i := resG Z le_top g * s.f i
  compat i j := by
    have e : resG Z (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
      (L.g i j).val * resG Z (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (s.f j) := s.compat i j
    show resG Z inf_le_left (resG Z le_top g * s.f i) = (L.g i j).val * resG Z inf_le_right (resG Z le_top g * s.f j)
    rw [map_mul, map_mul, resG_resG, resG_resG, e]
    ring

theorem isoMaps_secMul {Z : Scheme.{0}} {L N : LB Z} (w : LB.Iso L N) {s : L.Sec} {s' : N.Sec} (h : IsoMaps w s s')
    (g : Γ(Z, ⊤)) : IsoMaps w (secMul g s) (secMul g s') := by
  intro i k
  have e1 : resG Z inf_le_left (s'.f i) =
    (show Γ(Z, N.U i ⊓ L.U k) from (w.s (i, k)).val) * resG Z inf_le_right (s.f k) := h i k
  show resG Z inf_le_left (resG Z le_top g * s'.f i) =
    (show Γ(Z, N.U i ⊓ L.U k) from (w.s (i, k)).val) * resG Z inf_le_right (resG Z le_top g * s.f k)
  rw [map_mul, map_mul, resG_resG, resG_resG, e1]
  exact mul_left_comm _ _ _

theorem ev_res_secMul {Z : Scheme.{0}} {L : LB Z} (g : Γ(Z, ⊤)) (s : L.Sec) (k : L.ι) {W : Z.Opens} (h : W ≤ L.U k)
    (r : Sp T ⟶ Z) (hr : ⊤ ≤ r ⁻¹ᵁ W) :
    ev r W hr (resG Z h ((secMul g s).f k)) = ev r ⊤ le_top g * ev r W hr (resG Z h (s.f k)) := by
  show ev r W hr (resG Z h (resG Z le_top g * s.f k)) = _
  rw [map_mul, map_mul, resG_resG, ev_res r _ hr le_top]

theorem appLE_res_appTop {Z Z' B : Scheme.{0}} (g : Z' ⟶ Z) (p : Z ⟶ B) (p' : Z' ⟶ B) (e : g ≫ p = p') {U : Z.Opens}
    {V : Z'.Opens} (h : V ≤ g ⁻¹ᵁ U) (b : Γ(B, ⊤)) :
    resG Z' le_top (p'.appTop.hom b) = (g.appLE U V h).hom (resG Z le_top (p.appTop.hom b)) := by
  subst e
  refine ext_ev fun T _ r hr => ?_
  rw [ev_res r _ hr le_top, ev_appTop, ev_appLE r g h hr (le_preimage_map _ h hr), ev_res _ _ _ le_top,
    ev_appTop, Category.assoc]

def ThRel {x₀ : Sp S ⟶ Xo.X} {x : Sp S ⟶ Y.X} {t' : SAB H (Sp S)} (m1 : SABMap t' Xo.univ.t x₀) (m2 : SABMap t' Y.t x)
    (U : Y.X.Opens) (θ : ∀ i, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U i)) (s : LB.Sec (PPx x₀)) : Prop :=
  ∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (Y.t.PP.L.pull m2.φ))
    (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)),
    RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧
    (∀ (j : Y.t.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens)
      (h₁ : W ≤ m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j))
      (h₂ : W ≤ (Y.t.PP.L.pull m2.φ).U (fun _ => j) ⊓ t'.PP.L.U k),
      (m2.φ.appLE _ _ h₁).hom (θ j) =
        resG _ h₂ (w2.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (σ.f k)) ∧
    ∀ g : t'.G.left ⟶ Gx x₀, g ≫ (CartesianMonoidalCategory.snd (Over.mk x₀) Xo.univ.t.G).left = m1.φ →
      g ≫ (CartesianMonoidalCategory.fst (Over.mk x₀) Xo.univ.t.G).left = t'.G.hom →
      ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x₀).U (fun _ => j PUnit.unit)),
        s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))

theorem thRel_cast {x₀ : Sp S ⟶ Xo.X} {x x' : Sp S ⟶ Y.X} (e : x = x') {t' : SAB H (Sp S)}
    (m1 : SABMap t' Xo.univ.t x₀) (m2 : SABMap t' Y.t x) : ∃ m2' : SABMap t' Y.t x', m2'.φ = m2.φ ∧
      ∀ U θ s, ThRel m1 m2 U θ s → ThRel m1 m2' U θ s := by
  subst e
  exact ⟨m2, rfl, fun _ _ _ h => h⟩

theorem thRel_change (M M' : GChart Y) {x : Sp S ⟶ Y.X} (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) {x₀ : Sp S ⟶ Xo.X}
    {t' : SAB H (Sp S)} (m1 : SABMap t' Xo.univ.t x₀) (m2 : SABMap t' Y.t x) {s : LB.Sec (PPx x₀)}
    (hs : ThRel m1 m2 M.U M.θ s) : ThRel m1 m2 M'.U M'.θ
      (secMul ((fst (Over.mk x₀) Xo.univ.t.G).left.appTop.hom (toΓ S (ev x _ hh (thRat M M')))) s) := by
  have hw : m2.φ ≫ Y.t.G.hom = t'.G.hom ≫ x := m2.cart.1.w
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, a, d⟩ := hs
  refine ⟨w1, w2, secMul (t'.G.hom.appTop.hom (toΓ S (ev x _ hh (thRat M M')))) σ, secMul _ s1, r1, r2,
    isoMaps_secMul w1 i1 _, fun j k W h₁ h₂ => ?_, fun g g1 g2 j hj => ?_⟩
  · have h₁' : W ≤ m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := fun q hq =>
      ⟨by
        show (m2.φ ≫ Y.t.G.hom) q ∈ M.U
        rw [hw]
        exact (hh (Set.mem_univ (t'.G.hom q))).1, (h₁ hq).2⟩
    refine ext_ev fun T _ r hr => ?_
    have e1 := congrArg (ev r W hr) (a j k W h₁' h₂)
    have hx : (r ≫ m2.φ) ≫ Y.t.G.hom = spMap ((ev (r ≫ t'.G.hom) ⊤ le_top).comp (toΓ S)) ≫ x := by
      rw [spMap_ev_top, Category.assoc, hw, Category.assoc]
    have hm : ⊤ ≤ ((r ≫ m2.φ) ≫ Y.t.G.hom) ⁻¹ᵁ (M.U ⊓ M'.U) := by rw [hx]; exact le_preimage_comp _ hh
    have e2 := ev_thRat M M' (r ≫ m2.φ) j (le_preimage_map _ h₁' hr) (le_preimage_map _ h₁ hr) hm
    rw [ev_appLE r _ h₁' hr (le_preimage_map _ h₁' hr)] at e1
    rw [ev_congr hx _ hm (le_preimage_comp _ hh), ev_spMap _ x _ hh, e1] at e2
    rw [ev_appLE r _ h₁ hr (le_preimage_map _ h₁ hr), e2, map_mul, map_mul, ev_res_secMul, ev_appTop]
    exact mul_left_comm _ _ _
  · exact (congrArg₂ (· * ·) (appLE_res_appTop g _ _ g2 hj _) (d g g1 g2 j hj)).trans (map_mul _ _ _).symm

variable [Algebra c.F S]

theorem thTie_change (M M' : GChart Y) {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) {x₀ : Sp S ⟶ Xo.X} (Λ : M.toMChart.Lift (ev x M.U h) x₀)
    (Λ' : M'.toMChart.Lift (ev x M'.U h') x₀) {s s' : LB.Sec (PPx x₀)} (hs : Λ.ThTie s) (hs' : Λ'.ThTie s')
    (i : (PPx x₀).ι) : s'.f i = scal x₀ (ev x _ hh (thRat M M')) i * s.f i := by
  obtain ⟨n, hn, hn'⟩ := thRel_cast (spMap_ev x M.hU h) Λ.m1 Λ.m2
  obtain ⟨n', hm, hm'⟩ := thRel_cast (spMap_ev x M'.hU h').symm Λ.m1 n
  have key := hm' _ _ _ (thRel_change M M' hh Λ.m1 n (hn' _ _ _ hs))
  let Λ'' : M'.toMChart.Lift (ev x M'.U h') x₀ :=
    ⟨Λ.xF, Λ.xF_fst, Λ.xF_snd, Λ.xF_j.trans ((spMap_ev x M.hU h).trans (spMap_ev x M'.hU h').symm), Λ.t', Λ.m', Λ.m1,
      n', Λ.liftedChartMap_eq, hm.trans (hn.trans Λ.matrix_two_by_two_congr)⟩
  rw [TieUniq.thTie_unique Λ'' (LiftUnique.thTie Λ' Λ'' s' hs') key]
  rfl

theorem frPt_eq_of_tie {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U)
    {u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) S} {P Q : FrPt Xo c S} (hP : M.Comparison₂ (ev x M.U h) u P)
    (hQ : M.Comparison₂ (ev x M.U h) u Q) : P = Q := by
  obtain ⟨x₀, xo, v, t1, t2, t3, s, t4⟩ := P
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q
  obtain ⟨Λ, hv, hs⟩ := hP
  obtain ⟨Λ', hv', hs'⟩ := hQ
  obtain rfl : x₀ = x' := Λ.xF_fst.symm.trans
    ((congrArg (· ≫ pullback.fst _ _) (xF_ext Λ.xF_snd Λ'.xF_snd (Λ.xF_j.trans Λ'.xF_j.symm))).trans Λ'.xF_fst)
  obtain ⟨k1, k2⟩ := LiftUnique.lift_indep E H Dw l Xo c O β Y M S _ x₀ Λ' Λ
  obtain rfl : v = v' := by
    funext τ i
    exact ((vec_bijective E H Dw l Xo c O β Y M S _ x₀ Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))
  obtain rfl : s = s' := TieUniq.thTie_unique Λ hs (k2 _ hs')
  rfl

theorem frBor_of_frVec {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) (t : Ix Dw → Sˣ)
    (b : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S) (hb : ∀ σ, (b σ).BlockTriangular id)
    (hd : ∀ σ i, b σ i i = t (some ⟨σ, i⟩)) (hv : ∀ σ i, frVec Y P' hx' σ i = ∑ j, b σ j i • frVec Y P hx σ j)
    (hs : ∀ e : P'.x = P.x, ∀ i, (e ▸ P'.s).f i = scal P.x (t none : S) i * P.s.f i) : FrBor t P P' := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := by rw [← frX_fst, eX, frX_fst]
  have hs' := hs e
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have hv' : ∀ σ i, IsCombAt P.x (P.u σ) (fun j => b σ j i) (P'.u σ i) := fun σ i => by
    refine (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).2 ?_
    refine (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).2 ?_
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    rw [← hv]
    obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
    exact (toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  refine ⟨rfl, fun σ i => ⟨fun j => b σ j i, hd σ i, fun j hj => hb σ hj, hv' σ i⟩, 𝟙 _, Category.id_comp _,
    Category.id_comp _, fun i hi => (id_appLE_apply _ _ hi _).trans (hs' i).symm⟩

theorem frVec_of_frBor {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x) {t : Ix Dw → Sˣ} (hB : FrBor t P P') (σ : E →+* ℂ) :
    ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, b i i = t (some ⟨σ, i⟩)) ∧
      ∀ i, frVec Y P' hx' σ i = ∑ j, b j i • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := hB.1
  choose cf h1 h2 h3 using hB.2.1 σ
  refine ⟨fun j i => cf i j, fun j i hj => h2 i j hj, h1, fun i => ?_⟩
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1 (h3 i)
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

theorem frX_frBor {P P' : FrPt Xo c S} {t : Ix Dw → Sˣ} (hB : FrBor t P P') : frX P' = frX P :=
  eq_frX P ((frX_fst P').trans hB.1) (frX_snd P')

end Theta

end GlobalTheory.FlagMod
