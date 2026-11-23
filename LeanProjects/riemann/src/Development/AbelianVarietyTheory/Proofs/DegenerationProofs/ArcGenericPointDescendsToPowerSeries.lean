import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationDataStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.ArcPointDescent

theorem exists_embedding {A₀ A F : Type} [CommRing A₀] [IsDomain A₀] [CommRing A] [IsDomain A] [Field F] [IsAlgClosed F]
    (α : A₀ →+* A) (hα : Function.Injective α) (hf : α.Finite) (ω : A₀ →+* F) (hω : Function.Injective ω) :
    ∃ ψ : A →+* F, Function.Injective ψ ∧ ∀ r, ψ (α r) = ω r := by
  letI := α.toAlgebra
  letI := ω.toAlgebra
  have : Module.Finite A₀ A := hf
  have : FaithfulSMul A₀ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hα
  have : FaithfulSMul A₀ F := (faithfulSMul_iff_algebraMap_injective _ _).2 hω
  let ψ : A →ₐ[A₀] F := IsAlgClosed.lift
  refine ⟨ψ.toRingHom, ?_, fun r => ψ.commutes r⟩
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := A₀) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  intro x y h
  exact hω ((ψ.commutes x).symm.trans (h.trans (ψ.commutes y)))

theorem exists_finset {V F R A : Type} [CommRing V] [CommRing F] [Algebra V F] [CommRing R] [CommRing A]
    (g : R →+* A) (hg : g.Finite) (φ : R →+* V) (ψ : A →+* F) (h : ∀ r, ψ (g r) = algebraMap V F (φ r)) :
    ∃ s : Finset F, (∀ x ∈ s, IsIntegral V x) ∧ ∀ W : Subalgebra V F, (∀ x ∈ s, x ∈ W) → ∀ a, ψ a ∈ W := by
  classical
  letI := g.toAlgebra
  have : Module.Finite R A := hg
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := R) (M := A)
  refine ⟨t.image ψ, fun x hx => ?_, fun W hW a => ?_⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Algebra.IsIntegral.isIntegral (R := R) a).map_of_comp_eq φ ψ (RingHom.ext fun r => (h r).symm)
  · have ha : a ∈ Submodule.span R (t : Set A) := ht ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact hW _ (Finset.mem_image_of_mem _ hx)
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul]
      exact W.mul_mem (by rw [show algebraMap R A r = g r from rfl, h]; exact W.algebraMap_mem _) hx

theorem exists_common {V F R₁ A₁ R₂ A₂ : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) [Field F] [Algebra V F]
    [FaithfulSMul V F] [Algebra.IsAlgebraic V F] [CommRing R₁] [CommRing A₁] [CommRing R₂] [CommRing A₂]
    (g₁ : R₁ →+* A₁) (hg₁ : g₁.Finite) (φ₁ : R₁ →+* V) (ψ₁ : A₁ →+* F) (h₁ : ∀ r, ψ₁ (g₁ r) = algebraMap V F (φ₁ r))
    (g₂ : R₂ →+* A₂) (hg₂ : g₂.Finite) (φ₂ : R₂ →+* V) (ψ₂ : A₂ →+* F) (h₂ : ∀ r, ψ₂ (g₂ r) = algebraMap V F (φ₂ r)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (α : V →+* W) (ω : W →+* F) (e₁ : A₁ →+* W)
      (e₂ : A₂ →+* W), CDvr W ∧ α.Finite ∧ Function.Injective ω ∧ (∀ v, ω (α v) = algebraMap V F v) ∧
      (∀ a, ω (e₁ a) = ψ₁ a) ∧ ∀ a, ω (e₂ a) = ψ₂ a := by
  classical
  obtain ⟨d, hc, h0⟩ := hV
  obtain ⟨s₁, i₁, m₁⟩ := exists_finset g₁ hg₁ φ₁ ψ₁ h₁
  obtain ⟨s₂, i₂, m₂⟩ := exists_finset g₂ hg₂ φ₂ ψ₂ h₂
  obtain ⟨W, dW, cW, -, fW, -, -, -, hW⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F (s₁ ∪ s₂)
  have : CharZero W := charZero_of_injective_algebraMap (R := V) fun x y h =>
    FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  exact ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, W.val.toRingHom,
    ψ₁.codRestrict W (m₁ W fun x hx => hW x (Finset.mem_union_left _ hx) (i₁ x hx)),
    ψ₂.codRestrict W (m₂ W fun x hx => hW x (Finset.mem_union_right _ hx) (i₂ x hx)),
    ⟨dW, cW, this⟩, RingHom.finite_algebraMap.2 fW, Subtype.val_injective, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem cDvr_powerSeries (k : Type) [Field k] [CharZero k] : CDvr (PowerSeries k) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

theorem admissibleBase_maximalIdeal_completeDVR {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) :
    AdmBase V (IsLocalRing.maximalIdeal V) := by
  obtain ⟨d, hc, h0⟩ := hV
  exact ⟨inferInstance, inferInstance, inferInstance, hc⟩

theorem epi_spMap {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) :=
  letI := i.toAlgebra
  GlobalTheory.FixedPoint.epi_specAlg (K₀ := K) (K₁ := L)

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {f : A →+* B} {g : B →+* C} {h : A →+* C}
    (e : ∀ a, g (f a) = h a) : spMap g ≫ spMap f = spMap h := by
  rw [← spMap_comp]; exact congrArg spMap (RingHom.ext e)

theorem sp_sq {A B B' C : Type} [CommRing A] [CommRing B] [CommRing B'] [CommRing C] {f : A →+* B} {g : B →+* C}
    {f' : A →+* B'} {g' : B' →+* C} (e : ∀ a, g (f a) = g' (f' a)) : spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  rw [← spMap_comp, ← spMap_comp]; exact congrArg spMap (RingHom.ext e)

theorem exists_frac {A K : Type} [CommRing A] [IsDomain A] [Field K] (f : A →+* K) (hf : Function.Injective f) :
    ∃ t : FractionRing A →+* K, ∀ a, t (algebraMap A _ a) = f a :=
  ⟨IsFractionRing.lift hf, IsFractionRing.lift_algebraMap hf⟩

theorem frac_ext {A K : Type} [CommRing A] [IsDomain A] [CommRing K] {t t' : FractionRing A →+* K}
    (h : ∀ a, t (algebraMap A _ a) = t' (algebraMap A _ a)) : t = t' :=
  IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext h)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem mono_j {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) : Mono Y.j := by
  have : IsPreimmersion (spMap V.subtype) :=
    IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
  have := Y.jQ_open
  unfold Model.j
  infer_instance

theorem hasArcData_pull (h1 : Laws) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) {O : Type} [CommRing O] {β : O →+* c.F}
    {Y : Model Xo c β} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} {a : ArcIn D l β O' b}
    {V W : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W] (hV : CDvr V) (hW : CDvr W)
    (e : V →+* W) (he : Function.Injective e) (hl : IsLocalHom e) {f : O' →+* V} {u : V} {χ : Sp V ⟶ Y.X}
    (h : Y.HasArcData a (IsLocalRing.maximalIdeal V) f u χ) :
    Y.HasArcData a (IsLocalRing.maximalIdeal W) (e.comp f) (e u) (spMap e ≫ χ) := by
  obtain ⟨w⟩ := (Y.hasArcData_iff a _ f u χ).1 h
  obtain ⟨w', -⟩ := ArcWit.baseChange h3.cubePull h1.polBaseChange h4.unifBaseChange h5 (qkPullExists h1.globalFns)
    polOActPull (admissibleBase_maximalIdeal_completeDVR hV) (admissibleBase_maximalIdeal_completeDVR hW) w e he
    (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit e x hx)
  exact (Y.hasArcData_iff a _ _ _ _).2 ⟨w'⟩

theorem exists_closure (V : Type) [CommRing V] [IsDomain V] : ∃ (F : Type) (_ : Field F) (_ : Algebra V F),
    IsAlgClosed F ∧ FaithfulSMul V F ∧ Algebra.IsAlgebraic V F := by
  refine ⟨AlgebraicClosure (FractionRing V), inferInstance, inferInstance, inferInstance, ?_,
    (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing V)).2 inferInstance⟩
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq V (FractionRing V)]
  exact (algebraMap (FractionRing V) _).injective.comp (IsFractionRing.injective V _)

section ThetaShiftProofs

variable {O' : Type} [CommRing O'] [IsDomain O'] {R₁ : Type} [CommRing R₁] [IsDomain R₁] {g : PowerSeries O' →+* R₁}
  {y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c}

theorem traitData_desc {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {b : O →+* O'} {a : ArcIn D l β O' b}
    (gam : FractionRing (PowerSeries O') →+* FractionRing R₁)
    (hgam : ∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) (hg : g.Finite) (h : TraitData Y a g y₁)
    (y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c) (hy : spMap gam ≫ y = y₁) : TraitData Y a (RingHom.id _) y := by
  have gi : Function.Injective g := fun x x' e => IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))
    (gam.injective (by rw [hgam, hgam, e]))
  refine ⟨?_, fun V _ _ _ hV φ gV hgV χ hχ => ?_⟩
  · have := epi_spMap gam
    rw [← cancel_epi (spMap gam), ← Category.assoc, hy, h.1, ← Category.assoc, ← Category.assoc (spMap gam),
      ← Category.assoc (spMap gam ≫ _), sp_comp (f := algebraMap (PowerSeries O') (FractionRing (PowerSeries O'))) (g := gam)
        (h := (algebraMap R₁ _).comp g) hgam,
      sp_comp (f := RingHom.id _) (h := (algebraMap R₁ (FractionRing R₁)).comp g) fun _ => rfl,
      sp_comp (f := g) (h := (algebraMap R₁ (FractionRing R₁)).comp g) fun _ => rfl]
  have φi : Function.Injective φ := fun x x' e => IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))
    (gV.injective (by rw [hgV, hgV, e]))
  obtain ⟨F, _, _, _, _, _⟩ := exists_closure V
  have Fi := FaithfulSMul.algebraMap_injective V F
  obtain ⟨ψ, ψi, hψ⟩ := exists_embedding g gi hg ((algebraMap V F).comp φ) (Fi.comp φi)
  obtain ⟨W, _, _, _, α, ω, ρ, -, hW, αf, ωi, hα, hρ, -⟩ := exists_common hV g hg φ ψ hψ g hg φ ψ hψ
  have αi : Function.Injective α := fun x x' e => Fi (by rw [← hα, ← hα, e])
  have ρi : Function.Injective ρ := fun x x' e => ψi (by rw [← hρ, ← hρ, e])
  have hc : ∀ r, ρ (g r) = α (φ r) := fun r => ωi (by rw [hρ, hα, hψ]; rfl)
  have αl : IsLocalHom α := αf.to_isIntegral.isLocalHom αi
  obtain ⟨gW, hgW⟩ := exists_frac ((algebraMap W (FractionRing W)).comp ρ) ((IsFractionRing.injective W _).comp ρi)
  obtain ⟨αK, hαK⟩ := exists_frac ((algebraMap W (FractionRing W)).comp α) ((IsFractionRing.injective W _).comp αi)
  have e : gW.comp gam = αK.comp gV := frac_ext fun r => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hgam, hgV, hgW, hαK, RingHom.comp_apply, RingHom.comp_apply, hc]
  obtain ⟨k₁, k₂⟩ := h.2 W hW ρ gW hgW (spMap α ≫ χ) (by
    rw [← hy, Category.assoc, ← Category.assoc, sp_sq (RingHom.congr_fun e), Category.assoc, hχ, ← Category.assoc,
      ← Category.assoc, sp_sq (f := algebraMap V (FractionRing V)) (g := αK) (f' := α)
        (g' := algebraMap W (FractionRing W)) hαK])
  rw [hc] at k₁ k₂
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨x', rfl⟩ := αf.to_isIntegral.comap_surjective αi x
    exact k₁ (hu.map α) ⟨x', rfl⟩
  · obtain ⟨W', _, _, _, io, hW', ioi, iof, hd⟩ := k₂ fun hu' => hu (isUnit_of_map_unit α _ hu')
    refine ⟨W', inferInstance, inferInstance, inferInstance, io.comp α, hW', ioi.comp αi, iof.comp αf, ?_⟩
    have e₁ : io.comp (ρ.comp (g.comp PowerSeries.C)) =
        (io.comp α).comp (φ.comp ((RingHom.id _).comp PowerSeries.C)) := RingHom.ext fun x => congrArg io (hc _)
    rw [e₁, ← Category.assoc, ← spMap_comp] at hd
    exact hd

variable {W₀ : ValuationSubring ℂ} {Y : Model Xo c (c.V W₀).subtype} {b : c.V W₀ →+* O'}
  {a : ArcIn D l (c.V W₀).subtype O' b}

theorem exists_ext (h : TraitData Y a g y₁) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W)
    (ρ : R₁ →+* W) (gW : FractionRing R₁ →+* FractionRing W) (hgW : ∀ r, gW (algebraMap R₁ _ r) = algebraMap W _ (ρ r)) :
    ∃ χ : Sp W ⟶ Y.X, χ ≫ Y.s = spMap (ρ.comp (g.comp PowerSeries.C)) ≫ spMap b ∧ spMap gW ≫ y₁ ≫ Y.j = jK W ≫ χ := by
  have := hW.1
  let fK : c.F →+* FractionRing W := (Spec.preimage (spMap gW ≫ y₁ ≫ pullback.snd _ _)).hom
  have hf : spMap fK = spMap gW ≫ y₁ ≫ pullback.snd _ _ := Spec.map_preimage _
  have hj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c.V W₀).subtype := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have ho : (algebraMap W (FractionRing W)).comp ((ρ.comp (g.comp PowerSeries.C)).comp b) = fK.comp (c.V W₀).subtype := by
    have e : spMap ((algebraMap W (FractionRing W)).comp ((ρ.comp (g.comp PowerSeries.C)).comp b)) =
        spMap (fK.comp (c.V W₀).subtype) := by
      rw [spMap_comp _ fK, hf, Category.assoc, Category.assoc, ← hj, h.1, ← Category.assoc,
        sp_sq (f := algebraMap R₁ (FractionRing R₁)) (g := gW) (f' := ρ) hgW]
      simp only [spMap_comp, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  obtain ⟨⟨χ, ⟨h₁, h₂⟩, -⟩, -⟩ := GlobalTheory.ValuativeExtension.valuation_extension E H D l Xo c _ _ Y W (FractionRing W) _ fK
    (spMap gW ≫ y₁) ho (by rw [hf, Category.assoc])
  exact ⟨χ, by rw [h₁, spMap_comp], by rw [h₂, Category.assoc]⟩

theorem exists_data (hg : g.Finite) (h : TraitData Y a g y₁) {V F : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (hV : CDvr V) [Field F] [IsAlgClosed F] [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F]
    (φ : PowerSeries O' →+* V) (hu : ¬ IsUnit (φ PowerSeries.X)) (ka : FractionRing R₁ →+* F)
    (hka : ∀ r, ka (algebraMap R₁ _ (g r)) = algebraMap V F (φ r)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (α : V →+* A) (ψ : A →+* F) (ρ : R₁ →+* A)
      (χ : Sp A ⟶ Y.X), CDvr A ∧ α.Finite ∧ Function.Injective ψ ∧ (∀ v, ψ (α v) = algebraMap V F v) ∧
      (∀ r, ψ (ρ r) = ka (algebraMap R₁ _ r)) ∧ χ ≫ Y.s = spMap (α.comp (φ.comp PowerSeries.C)) ≫ spMap b ∧
      spMap ψ ≫ χ = spMap ka ≫ y₁ ≫ Y.j ∧
      Y.HasArcData a (IsLocalRing.maximalIdeal A) (α.comp (φ.comp PowerSeries.C)) (α (φ PowerSeries.X)) χ := by
  have Fi := FaithfulSMul.algebraMap_injective V F
  have ψi : Function.Injective (ka.comp (algebraMap R₁ (FractionRing R₁))) := ka.injective.comp (IsFractionRing.injective _ _)
  obtain ⟨W, _, _, _, α, ω, ρ, -, hW, αf, ωi, hα, hρ, -⟩ := exists_common hV g hg φ (ka.comp (algebraMap R₁ _)) hka
    g hg φ (ka.comp (algebraMap R₁ _)) hka
  have αi : Function.Injective α := fun x x' e => Fi (by rw [← hα, ← hα, e])
  have ρi : Function.Injective ρ := fun x x' e => ψi (by rw [← hρ, ← hρ, e])
  have hc : ∀ r, ρ (g r) = α (φ r) := fun r => ωi (by rw [hρ, hα, ← hka]; rfl)
  have αl : IsLocalHom α := αf.to_isIntegral.isLocalHom αi
  obtain ⟨gW, hgW⟩ := exists_frac ((algebraMap W (FractionRing W)).comp ρ) ((IsFractionRing.injective W _).comp ρi)
  obtain ⟨ωK, hωK⟩ := exists_frac ω ωi
  obtain ⟨χ, hs, hχ⟩ := exists_ext h hW ρ gW hgW
  obtain ⟨A, _, _, _, io, hA, ioi, iof, hd⟩ := (h.2 W hW ρ gW hgW χ hχ).2
    (by rw [hc]; exact fun hu' => hu (isUnit_of_map_unit α _ hu'))
  obtain ⟨ψ, hψi, hψ⟩ := exists_embedding io ioi iof ω ωi
  have e₁ : ρ.comp (g.comp PowerSeries.C) = α.comp (φ.comp PowerSeries.C) := RingHom.ext fun x => hc _
  rw [e₁] at hs hd
  rw [hc] at hd
  have e : ωK.comp gW = ka := frac_ext fun r => by
    rw [RingHom.comp_apply, hgW, RingHom.comp_apply, hωK, hρ, RingHom.comp_apply]
  refine ⟨A, inferInstance, inferInstance, inferInstance, io.comp α, ψ, io.comp ρ, spMap io ≫ χ, hA, iof.comp αf, hψi,
    fun v => (hψ _).trans (hα v), fun r => (hψ _).trans (hρ r), ?_, ?_, hd⟩
  · rw [Category.assoc, hs, ← Category.assoc, ← spMap_comp]
  · rw [← e, spMap_comp, Category.assoc, hχ, ← Category.assoc, ← Category.assoc, sp_comp hψ, sp_comp hωK]

theorem point_eq (h1 : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) [CharZero O'] (hg : g.Finite)
    (h : TraitData Y a g y₁) {V F : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (hV : CDvr V) [Field F] [IsAlgClosed F] [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F]
    (φ : PowerSeries O' →+* V) (φi : Function.Injective φ) (hu : ¬ IsUnit (φ PowerSeries.X)) (ka₁ ka₂ : FractionRing R₁ →+* F)
    (hka₁ : ∀ r, ka₁ (algebraMap R₁ _ (g r)) = algebraMap V F (φ r))
    (hka₂ : ∀ r, ka₂ (algebraMap R₁ _ (g r)) = algebraMap V F (φ r)) : spMap ka₁ ≫ y₁ = spMap ka₂ ≫ y₁ := by
  have Fi := FaithfulSMul.algebraMap_injective V F
  obtain ⟨A₁, _, _, _, α₁, ψ₁, ρ₁, χ₁, hA₁, f₁, i₁, a₁, r₁, s₁, p₁, d₁⟩ := exists_data hg h hV φ hu ka₁ hka₁
  obtain ⟨A₂, _, _, _, α₂, ψ₂, ρ₂, χ₂, hA₂, f₂, i₂, a₂, r₂, s₂, p₂, d₂⟩ := exists_data hg h hV φ hu ka₂ hka₂
  obtain ⟨W, _, _, _, α, ω, e₁, e₂, hW, αf, ωi, hα, he₁, he₂⟩ := exists_common hV α₁ f₁ (RingHom.id V) ψ₁ a₁
    α₂ f₂ (RingHom.id V) ψ₂ a₂
  obtain ⟨ωK, hωK⟩ := exists_frac ω ωi
  have αi : Function.Injective α := fun x x' e => Fi (by rw [← hα, ← hα, e])
  have key : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (α' : V →+* A) (ψ : A →+* F) (ρ : R₁ →+* A)
      (χ : Sp A ⟶ Y.X) (ka : FractionRing R₁ →+* F) (e : A →+* W), CDvr A → Function.Injective ψ →
      (∀ v, ψ (α' v) = algebraMap V F v) → (∀ r, ψ (ρ r) = ka (algebraMap R₁ _ r)) →
      χ ≫ Y.s = spMap (α'.comp (φ.comp PowerSeries.C)) ≫ spMap b → spMap ψ ≫ χ = spMap ka ≫ y₁ ≫ Y.j →
      Y.HasArcData a (IsLocalRing.maximalIdeal A) (α'.comp (φ.comp PowerSeries.C)) (α' (φ PowerSeries.X)) χ →
      (∀ x, ω (e x) = ψ x) → ∃ (χ' : Sp W ⟶ Y.X) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ Y.j = jK W ≫ χ' ∧
        χ' ≫ Y.s = spMap (α.comp (φ.comp PowerSeries.C)) ≫ spMap b ∧ spMap ω ≫ χ' = spMap ka ≫ y₁ ≫ Y.j ∧
        Y.HasArcData a (IsLocalRing.maximalIdeal W) (α.comp (φ.comp PowerSeries.C)) (α (φ PowerSeries.X)) χ' := by
    intro A _ _ _ α' ψ ρ χ ka e hA i a' r s p d he
    have ei : Function.Injective e := fun x x' q => i (by rw [← he, ← he, q])
    have hc : ∀ v, e (α' v) = α v := fun v => ωi (by rw [he, a', hα])
    have hc' : e.comp α' = α := RingHom.ext hc
    have el : IsLocalHom e := (RingHom.Finite.of_comp_finite (f := α') (hc' ▸ αf)).to_isIntegral.isLocalHom ei
    have ρi : Function.Injective ρ := fun x x' q => IsFractionRing.injective R₁ (FractionRing R₁)
      (ka.injective (by rw [← r, ← r, q]))
    obtain ⟨gW, hgW⟩ := exists_frac ((algebraMap W (FractionRing W)).comp (e.comp ρ))
      ((IsFractionRing.injective W _).comp (ei.comp ρi))
    have q : ωK.comp gW = ka := frac_ext fun x => by
      rw [RingHom.comp_apply, hgW, RingHom.comp_apply, hωK, RingHom.comp_apply, he, r]
    have p' : spMap ω ≫ spMap e ≫ χ = spMap ka ≫ y₁ ≫ Y.j := by rw [← Category.assoc, sp_comp he, p]
    have d' := hasArcData_pull h1 h3 h4 h5 hA hW e ei el d
    rw [← RingHom.comp_assoc, hc', hc] at d'
    refine ⟨spMap e ≫ χ, spMap gW ≫ y₁, ?_, ?_, p', d'⟩
    · have := epi_spMap ωK
      rw [← cancel_epi (spMap ωK), ← Category.assoc _ (jK W), sp_comp hωK, p', ← q, spMap_comp]
      simp only [Category.assoc]
    · rw [Category.assoc, s, ← Category.assoc, ← spMap_comp, ← RingHom.comp_assoc, hc']
  obtain ⟨χ, y, j, s, p, d⟩ := key A₁ α₁ ψ₁ ρ₁ χ₁ ka₁ e₁ hA₁ i₁ a₁ r₁ s₁ p₁ d₁ he₁
  obtain ⟨χ', y', j', s', p', d'⟩ := key A₂ α₂ ψ₂ ρ₂ χ₂ ka₂ e₂ hA₂ i₂ a₂ r₂ s₂ p₂ d₂ he₂
  have := hW.2.2
  have eq : χ = χ' := GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a W _ _ _ (admissibleBase_maximalIdeal_completeDVR hW)
    (IsLocalRing.maximalIdeal.isMaximal W).ne_top (αi.comp (φi.comp PowerSeries.C_injective)) χ χ' y y' j j' s s' d d'
  have := mono_j Y
  rw [← cancel_mono Y.j, Category.assoc, Category.assoc, ← p, ← p', eq]

end ThetaShiftProofs

theorem point_descends : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (ϖ : O'), ArcBase O' ϖ → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c) (gam : FractionRing (PowerSeries O') →+* FractionRing R₁), (∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r)) → g.Finite → IsIntegrallyClosed R₁ → TraitData Y a g y₁ → ∃ y : Sp (FractionRing (PowerSeries O')) ⟶ Xo.XF c, spMap gam ≫ y = y₁ ∧ TraitData Y a (RingHom.id _) y := by
  intro h1 h2 h3 h4 h5 _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b a ϖ _ R₁ _ _ g y₁ gam hgam hg _ h
  have gi : Function.Injective g := fun x x' e => IsFractionRing.injective (PowerSeries O') (FractionRing (PowerSeries O'))
    (gam.injective (by rw [hgam, hgam, e]))
  have c₁ : CharZero (FractionRing O') := IsFractionRing.charZero_of_isFractionRing O'
  have c₂ : CharZero (PowerSeries O') := charZero_of_injective_ringHom (f := PowerSeries.C (R := O')) PowerSeries.C_injective
  have c₃ : CharZero (FractionRing (PowerSeries O')) := IsFractionRing.charZero_of_isFractionRing (PowerSeries O')
  let V := PowerSeries (FractionRing O')
  have hV : CDvr V := cDvr_powerSeries _
  let φ : PowerSeries O' →+* V := PowerSeries.map (algebraMap O' (FractionRing O'))
  have φi : Function.Injective φ := PowerSeries.map_injective _ (IsFractionRing.injective O' _)
  have hu : ¬ IsUnit (φ PowerSeries.X) := by
    rw [show φ PowerSeries.X = PowerSeries.X from PowerSeries.map_X _]
    exact PowerSeries.X_irreducible.not_isUnit
  obtain ⟨F, _, _, _, _, _⟩ := exists_closure V
  have Fi := FaithfulSMul.algebraMap_injective V F
  obtain ⟨ψ, ψi, hψ⟩ := exists_embedding g gi hg ((algebraMap V F).comp φ) (Fi.comp φi)
  obtain ⟨ka, hka⟩ := exists_frac ψ ψi
  have hka' : ∀ r, ka (algebraMap R₁ _ (g r)) = algebraMap V F (φ r) := fun r => (hka _).trans (hψ r)
  have inv : ∀ s : F →+* F, (∀ x, s (ka (gam x)) = ka (gam x)) → spMap s ≫ spMap ka ≫ y₁ = spMap ka ≫ y₁ := fun s hs => by
    rw [← Category.assoc, ← spMap_comp]
    refine point_eq h1 h2 h3 h4 h5 hg h hV φ φi hu _ _ (fun r => ?_) hka'
    rw [RingHom.comp_apply, ← hgam, hs, hgam, hka']
  letI := gam.toAlgebra
  letI := ka.toAlgebra
  letI := (ka.comp gam).toAlgebra
  have : IsScalarTower (FractionRing (PowerSeries O')) (FractionRing R₁) F := .of_algebraMap_eq' rfl
  obtain ⟨⟨y, hy, -⟩, -⟩ := (GlobalTheory.FixedPoint.defined_over_of_fixed (K₀ := FractionRing (PowerSeries O'))
    (K₁ := FractionRing R₁) (L := F)).2 _ y₁ fun s => inv s fun x => s.commutes x
  exact ⟨y, hy, traitData_desc gam hgam hg h y hy⟩

end GlobalTheory.ArcPointDescent
