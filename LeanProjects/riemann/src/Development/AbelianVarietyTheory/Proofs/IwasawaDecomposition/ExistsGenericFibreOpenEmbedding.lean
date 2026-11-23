import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelFiniteOverModuliModelDescends
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGaloisCoverOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.ZM

namespace GlobalTheory.GenericDescent

theorem exists_descent_of_galois {K Fc F' : Type} [Field K] [Field Fc] [Field F'] [Algebra K Fc] [Algebra Fc F']
    [Algebra K F'] [IsScalarTower K Fc F'] [FiniteDimensional K F'] [IsGalois K F']
    {X₀ Y W : Scheme.{0}} (s₀ : X₀ ⟶ Sp K) (pY : Y ⟶ Sp F') (pW : W ⟶ Sp Fc) (hqp : IsQProjOver pY)
    [IsReduced Y] [IsSeparated pY] [IsSeparated pW]
    (jY : pullback s₀ (spMap (algebraMap K F')) ⟶ Y) [IsOpenImmersion jY] [IsDominant jY]
    (hjY : jY ≫ pY = pullback.snd _ _)
    (jW : pullback s₀ (spMap (algebraMap K Fc)) ⟶ W)
    (ρ : (F' ≃ₐ[K] F') → (Y ⟶ Y)) (hρ : ∀ a, ρ a ≫ pY = pY ≫ spMap (a : F' →+* F'))
    (r : (F' ≃ₐ[K] F') → (pullback s₀ (spMap (algebraMap K F')) ⟶ pullback s₀ (spMap (algebraMap K F'))))
    (hr₁ : ∀ a, r a ≫ pullback.fst _ _ = pullback.fst _ _)
    (hr₂ : ∀ a, r a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (a : F' →+* F'))
    (hρj : ∀ a, jY ≫ ρ a = r a ≫ jY)
    (q : Y ⟶ W) (hq : IsPullback q pY pW (spMap (algebraMap Fc F')))
    (rc : pullback s₀ (spMap (algebraMap K F')) ⟶ pullback s₀ (spMap (algebraMap K Fc)))
    (hrc₁ : rc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hrc₂ : rc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap Fc F'))
    (hqj : jY ≫ q = rc ≫ jW) :
    ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp K) (jK : X₀ ⟶ XK) (e : W ⟶ XK),
      IsOpenImmersion jK ∧ jK ≫ sK = s₀ ∧ IsPullback e pW sK (spMap (algebraMap K Fc)) ∧
      jW ≫ e = pullback.fst _ _ ≫ jK ∧
      ∀ (T : Scheme.{0}) [T.IsSeparated] (g : W ⟶ T) (g₀ : X₀ ⟶ T), jW ≫ g = pullback.fst _ _ ≫ g₀ →
        ∃ h : XK ⟶ T, e ≫ h = g ∧ jK ≫ h = g₀ := by
  have hc := DwModel.isGaloisCover_field K F'
  have hcomp : spMap (algebraMap Fc F') ≫ spMap (algebraMap K Fc) = spMap (algebraMap K F') := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hc₁ : ρ 1 = 𝟙 Y := by
    refine ext_of_isDominant_of_isSeparated pY ?_ jY ?_
    · rw [hρ, hc.one, Category.id_comp, Category.comp_id]
    · rw [hρj, Category.comp_id]
      have : r 1 = 𝟙 _ := by
        apply pullback.hom_ext
        · rw [hr₁, Category.id_comp]
        · rw [hr₂, hc.one, Category.comp_id, Category.id_comp]
      rw [this, Category.id_comp]
  have hcm : ∀ a b, ρ (a * b) = ρ a ≫ ρ b := fun a b => by
    refine ext_of_isDominant_of_isSeparated pY ?_ jY ?_
    · rw [Category.assoc, hρ, hρ, reassoc_of% hρ, hc.mul a b]
    · have : r (a * b) = r a ≫ r b := by
        apply pullback.hom_ext
        · rw [Category.assoc, hr₁, hr₁, hr₁]
        · rw [Category.assoc, hr₂, hr₂, reassoc_of% hr₂, hc.mul a b]
      rw [hρj, this, reassoc_of% hρj, hρj, Category.assoc]
  have hinv : ∀ a, ρ a ≫ pY ≫ spMap (algebraMap K F') = pY ≫ spMap (algebraMap K F') := fun a => by
    rw [reassoc_of% hρ, hc.inv]
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (a : F' ≃ₐ[K] F'), y ≫ ρ a = y → a = 1 := by
    intro k _ _ y a h
    have := hc.finite
    refine (hc.fibre k (y ≫ pY) (y ≫ pY) rfl).unique ?_ ?_
    · rw [Category.assoc, ← hρ, ← Category.assoc, h]
    · rw [hc.one, Category.comp_id]
  have hq' : IsQProjOver (pY ≫ spMap (algebraMap K F')) :=
    (GlobalTheory.isQProjOver_baseChange_and_finite_restrict K F' (algebraMap K F') Y (pY ≫ spMap (algebraMap K F'))).2 pY (RingHom.finite_algebraMap.mpr inferInstance) hqp
  have := hc.finite
  obtain ⟨Q, π, sQ, hπs, hG, -⟩ := exists_isGaloisCover_of_isQProjOver K Y _ _ ρ hq' hc₁ hcm hinv hfree
  have hPB : IsPullback pY π (spMap (algebraMap K F')) sQ := hc.isPullback hG hρ hπs.symm
  have hX : IsGaloisCover _ r (pullback.fst s₀ (spMap (algebraMap K F'))) :=
    hc.of_isPullback (IsPullback.of_hasPullback _ _).flip hr₂ hr₁
  have hXe : ∀ {Z : Scheme.{0}} (u v : X₀ ⟶ Z), pullback.fst s₀ (spMap (algebraMap K F')) ≫ u =
      pullback.fst s₀ (spMap (algebraMap K F')) ≫ v → u = v := fun u v h =>
    (hX.existsUnique_desc (pullback.fst _ _ ≫ v) fun a => by rw [reassoc_of% hr₁ a]).unique h rfl
  obtain ⟨jK, hjK, -⟩ := hX.existsUnique_desc (jY ≫ π) fun a => by rw [← reassoc_of% hρj a, hG.inv]
  have hjK' : pullback.fst s₀ (spMap (algebraMap K F')) ≫ jK = jY ≫ π := hjK
  have hjKs : jK ≫ sQ = s₀ := hXe _ _ (by
    rw [reassoc_of% hjK', hπs, reassoc_of% hjY, pullback.condition])
  have hPB2 : IsPullback jY (pullback.fst _ _) π jK := hG.isPullback hX (fun a => (hρj a).symm) hjK'.symm
  have hjo : IsOpenImmersion jK := by
    have := hG.fin
    have := hG.etale
    have := hG.onto
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hPB2 ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : FiniteDimensional Fc F' := Module.Finite.of_restrictScalars_finite K _ _
  have : IsGalois Fc F' := IsGalois.tower_top_of_isGalois K Fc F'
  have hcH := DwModel.isGaloisCover_field Fc F'
  have hin : ∀ h : F' ≃ₐ[Fc] F', spMap ((h.restrictScalars K : F' ≃ₐ[K] F') : F' →+* F') ≫
      spMap (algebraMap Fc F') = spMap (algebraMap Fc F') := hcH.inv
  let ρH : (F' ≃ₐ[Fc] F') → (Y ⟶ Y) := fun h => ρ (h.restrictScalars K)
  let rH : (F' ≃ₐ[Fc] F') → _ := fun h => r (h.restrictScalars K)
  have hρH : ∀ h, ρH h ≫ pY = pY ≫ spMap (h : F' →+* F') := fun h => hρ _
  have hrr : ∀ h, rH h ≫ rc = rc := fun h => by
    apply pullback.hom_ext
    · rw [Category.assoc, hrc₁]; exact hr₁ _
    · rw [Category.assoc, hrc₂]
      have e := hr₂ (h.restrictScalars K)
      change r (h.restrictScalars K) ≫ _ ≫ _ = _
      rw [reassoc_of% e, hin]
  have hqinv : ∀ h, ρH h ≫ q = q := fun h => by
    refine ext_of_isDominant_of_isSeparated pW ?_ jY ?_
    · rw [Category.assoc, hq.w, reassoc_of% hρH, hcH.inv]
    · have e := hρj (h.restrictScalars K)
      change jY ≫ ρ (h.restrictScalars K) ≫ q = _
      rw [reassoc_of% e, hqj, ← Category.assoc]
      exact congrArg (· ≫ jW) (hrr h)
  have hqc : IsGaloisCover _ ρH q := hcH.of_isPullback hq.flip hρH hqinv
  have hqe : ∀ {Z : Scheme.{0}} (u v : W ⟶ Z), q ≫ u = q ≫ v → u = v := fun u v h =>
    (hqc.existsUnique_desc (q ≫ v) fun a => by rw [reassoc_of% hqinv a]).unique h rfl
  have hrc : IsGaloisCover _ rH rc := hcH.of_isPullback
    (IsPullback.of_right (by rw [hrc₁, hcomp]; exact IsPullback.of_hasPullback _ _) hrc₂
      (IsPullback.of_hasPullback _ _)).flip (fun h => hr₂ _) hrr
  have hrce : ∀ {Z : Scheme.{0}} (u v : pullback s₀ (spMap (algebraMap K Fc)) ⟶ Z), rc ≫ u = rc ≫ v → u = v :=
    fun u v h => (hrc.existsUnique_desc (rc ≫ v) fun a => by rw [reassoc_of% hrr a]).unique h rfl
  let q' : Y ⟶ pullback sQ (spMap (algebraMap K Fc)) :=
    pullback.lift π (pY ≫ spMap (algebraMap Fc F')) (by rw [Category.assoc, hcomp, hπs])
  have hq'₁ : q' ≫ pullback.fst _ _ = π := pullback.lift_fst _ _ _
  have hq'₂ : q' ≫ pullback.snd _ _ = pY ≫ spMap (algebraMap Fc F') := pullback.lift_snd _ _ _
  have hp' : IsPullback q' pY (pullback.snd _ _) (spMap (algebraMap Fc F')) :=
    IsPullback.of_right (by rw [hq'₁, hcomp]; exact hPB.flip) hq'₂ (IsPullback.of_hasPullback _ _)
  have hq'inv : ∀ h, ρH h ≫ q' = q' := fun h => by
    apply pullback.hom_ext
    · rw [Category.assoc, hq'₁]; exact hG.inv _
    · rw [Category.assoc, hq'₂, reassoc_of% hρH, hcH.inv]
  have hq'c : IsGaloisCover _ ρH q' := hcH.of_isPullback hp'.flip hρH hq'inv
  have hq'e : ∀ {Z : Scheme.{0}} (u v : pullback sQ (spMap (algebraMap K Fc)) ⟶ Z), q' ≫ u = q' ≫ v → u = v :=
    fun u v h => (hq'c.existsUnique_desc (q' ≫ v) fun a => by rw [reassoc_of% hq'inv a]).unique h rfl
  obtain ⟨f, hf, -⟩ := hqc.existsUnique_desc q' hq'inv
  obtain ⟨f', hf', -⟩ := hq'c.existsUnique_desc q hqinv
  have hf₀ : q ≫ f = q' := hf
  have hf₀' : q' ≫ f' = q := hf'
  let ei : W ≅ pullback sQ (spMap (algebraMap K Fc)) :=
    ⟨f, f', hqe _ _ (by rw [reassoc_of% hf₀, hf₀', Category.comp_id]),
      hq'e _ _ (by rw [reassoc_of% hf₀', hf₀, Category.comp_id])⟩
  have hf₂ : f ≫ pullback.snd _ _ = pW := hqe _ _ (by rw [reassoc_of% hf₀, hq'₂, hq.w])
  refine ⟨Q, sQ, jK, f ≫ pullback.fst _ _, hjo, hjKs, ?_, ?_, ?_⟩
  · exact IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, reassoc_of% hf₂]⟩ ei rfl hf₂
  · refine hrce _ _ ?_
    rw [← reassoc_of% hqj, reassoc_of% hf₀, hq'₁, reassoc_of% hrc₁, hjK']
  · intro T _ g g₀ hg
    have hinvG : ∀ a, ρ a ≫ q ≫ g = q ≫ g := fun a => by
      refine ext_of_isDominant_of_isSeparated (terminal.from T) (terminal.hom_ext _ _) jY ?_
      rw [reassoc_of% hρj, reassoc_of% hqj, hg, reassoc_of% hrc₁, reassoc_of% hr₁]
    obtain ⟨h, hh, -⟩ := hG.existsUnique_desc (q ≫ g) hinvG
    have hh' : π ≫ h = q ≫ g := hh
    refine ⟨h, hqe _ _ ?_, hXe _ _ ?_⟩
    · rw [Category.assoc, reassoc_of% hf₀, reassoc_of% hq'₁, hh']
    · rw [reassoc_of% hjK', hh', reassoc_of% hqj, hg, reassoc_of% hrc₁]

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_normal_coeff (c : Coeff l) : ∃ c' : Coeff l, c.F ≤ c'.F ∧ Normal ℚ c'.F := by
  have := c.fin
  have hle : c.F ≤ IntermediateField.normalClosure ℚ c.F ℂ := IntermediateField.le_normalClosure c.F
  have : IsNormalClosure ℚ c.F (IntermediateField.normalClosure ℚ c.F ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun x => IsAlgClosed.splits _
  exact ⟨⟨IntermediateField.normalClosure ℚ c.F ℂ, inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, IsNormalClosure.normal (F := ℚ) (K := c.F) (L := IntermediateField.normalClosure ℚ c.F ℂ)⟩

theorem exists_genericMap (hM : PolMapSt) {Xo : Moduli D l} {c₁ c₂ : Coeff l}
    (Z₁ : Model Xo c₁ (algebraMap (𝓞 c₁.F) c₁.F)) (Z₂ : Model Xo c₂ (algebraMap (𝓞 c₂.F) c₂.F))
    (BD₁ : EffCartierData Z₁.X) (BD₂ : EffCartierData Z₂.X) {φ : InvFun (𝓞 E)} {m : ℕ} (htw : IsTwInv H φ)
    (h₁ : IsPol φ m Z₁ BD₁) (h₂ : IsPol φ m Z₂ BD₂) (f : c₂.F →+* c₁.F) (r : Xo.XF c₁ ⟶ Xo.XF c₂)
    (hr₁ : r ≫ pullback.fst _ _ = pullback.fst _ _) (hr₂ : r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f) :
    ∃ (π : Z₁.X ⟶ Z₂.X) (hπ : π ≫ Z₂.s = Z₁.s ≫ spMap (RingOfIntegers.mapRingHom f))
      (e : pullback Z₁.s (spMap (algebraMap (𝓞 c₁.F) c₁.F)) ⟶ pullback Z₂.s (spMap (algebraMap (𝓞 c₂.F) c₂.F))),
      IsFinite (pullback.lift π Z₁.s hπ) ∧ e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π ∧
      e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f ∧ Z₁.jQ ≫ e = r ≫ Z₂.jQ := by
  obtain ⟨hβ₁, hft, -⟩ := CoeffRings.coeff_isDedFrac E H l c₁
  obtain ⟨hβ₂, -, -⟩ := CoeffRings.coeff_isDedFrac E H l c₂
  obtain ⟨ν, -⟩ := LevelCover.sab_cancel Z₂.m0.toSABMap Z₁.m0.toSABMap r hr₁
  have hb : (algebraMap (𝓞 c₁.F) c₁.F).comp (RingOfIntegers.mapRingHom f) = f.comp (algebraMap (𝓞 c₂.F) c₂.F) := rfl
  have hsp : spMap (algebraMap (𝓞 c₁.F) c₁.F) ≫ spMap (RingOfIntegers.mapRingHom f) =
      spMap f ≫ spMap (algebraMap (𝓞 c₂.F) c₂.F) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  have hrs : r ≫ Z₂.j ≫ Z₂.s = Z₁.j ≫ Z₁.s ≫ spMap (RingOfIntegers.mapRingHom f) := by
    rw [FiniteTransition.openImmersion_comp_structure_eq_generic, reassoc_of% hr₂, ← Category.assoc Z₁.j, FiniteTransition.openImmersion_comp_structure_eq_generic, Category.assoc,
      hsp]
  obtain ⟨π, hπ, -, hfin, hj, -, -⟩ := hM E H D l l Xo Xo c₂ c₁ _ _ _ _ Z₂ Z₁ BD₂ BD₁ φ m (RingOfIntegers.mapRingHom f)
    (RingEquiv.refl _) r ((TwMap.reflEquiv _ _ _).symm ν) hβ₂ hβ₁ hft htw rfl h₂ h₁ hrs
  let e : pullback Z₁.s (spMap (algebraMap (𝓞 c₁.F) c₁.F)) ⟶ pullback Z₂.s (spMap (algebraMap (𝓞 c₂.F) c₂.F)) :=
    pullback.lift (pullback.fst _ _ ≫ π) (pullback.snd _ _ ≫ spMap f)
      (by rw [Category.assoc, hπ, pullback.condition_assoc, hsp, Category.assoc])
  have he₁ : e ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π := pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap f := pullback.lift_snd _ _ _
  refine ⟨π, hπ, e, hfin, he₁, he₂, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, he₁, ← Category.assoc, Category.assoc r]
    exact hj
  · rw [Category.assoc, he₂, ← Category.assoc, Z₁.jQ_over, Category.assoc, Z₂.jQ_over, hr₂]

end Model

theorem exists_generic_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (Z : ∀ c : Coeff l, Model Xo c (algebraMap (𝓞 c.F) c.F)) (BD : ∀ c, EffCartierData (Z c).X) (φ : InvFun (𝓞 E)) (m : ℕ), PolMapSt → IsTwInv H φ → (∀ c, IsPol φ m (Z c) (BD c)) → ∀ c : Coeff l, ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (jK : Xo.X ⟶ XK) (e : pullback (Z c).s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ XK), IsOpenImmersion jK ∧ jK ≫ sK = Xo.s ∧ IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧ (Z c).jQ ≫ e = pullback.fst _ _ ≫ jK ∧ ∀ (T : Scheme.{0}) [T.IsSeparated] (g : pullback (Z c).s (spMap (algebraMap (𝓞 c.F) c.F)) ⟶ T) (g₀ : Xo.X ⟶ T), (Z c).jQ ≫ g = pullback.fst _ _ ≫ g₀ → ∃ h : XK ⟶ T, e ≫ h = g ∧ jK ≫ h = g₀ := by
  intro E _ _ _ H D l Xo Z BD φ m hM htw hpol c
  obtain ⟨c', hle, hn⟩ := exists_normal_coeff c
  have := c.fin
  have := c'.fin
  letI aK : Algebra (KA l) c.F := (IntermediateField.inclusion c.le).toRingHom.toAlgebra
  letI aK' : Algebra (KA l) c'.F := (IntermediateField.inclusion c'.le).toRingHom.toAlgebra
  letI aF : Algebra c.F c'.F := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower (KA l) c.F c'.F := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ (KA l) c'.F := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ c.F c'.F := .of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (KA l) c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsGalois ℚ c'.F := ⟨⟩
  have : IsGalois (KA l) c'.F := IsGalois.tower_top_of_isGalois ℚ (KA l) c'.F
  have hsm : Smooth (spMap (algebraMap c.F c'.F)) := by
    have : Algebra.FormallyEtale c.F c'.F := Algebra.FormallyEtale.of_isSeparable _ _
    have : Algebra.FinitePresentation c.F c'.F := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩
  have hc := DwModel.isGaloisCover_field (KA l) c'.F
  have hcomp : spMap (algebraMap c.F c'.F) ≫ spMap (algebraMap (KA l) c.F) = spMap (algebraMap (KA l) c'.F) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

  let r : (c'.F ≃ₐ[KA l] c'.F) → (Xo.XF c' ⟶ Xo.XF c') := fun a =>
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (a : c'.F →+* c'.F)) (by
      rw [Category.assoc]
      exact pullback.condition.trans (congrArg (_ ≫ ·) (hc.inv a).symm))
  have hr₁ : ∀ a, r a ≫ pullback.fst _ _ = pullback.fst _ _ := fun a => pullback.lift_fst _ _ _
  have hr₂ : ∀ a, r a ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (a : c'.F →+* c'.F) :=
    fun a => pullback.lift_snd _ _ _
  let rc : Xo.XF c' ⟶ Xo.XF c := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (algebraMap c.F c'.F)) (by
    rw [Category.assoc]
    exact pullback.condition.trans (congrArg (_ ≫ ·) hcomp.symm))
  have hrc₁ : rc ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hrc₂ : rc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (algebraMap c.F c'.F) := pullback.lift_snd _ _ _
  choose π hπ ρ hρf hρ₁ hρ₂ hρj using fun a : c'.F ≃ₐ[KA l] c'.F => exists_genericMap hM (Z c') (Z c') (BD c') (BD c') htw (hpol c') (hpol c')
    (a : c'.F →+* c'.F) (r a) (hr₁ a) (hr₂ a)
  obtain ⟨πc, hπc, q, hfin, hq₁, hq₂, hqj⟩ := exists_genericMap hM (Z c') (Z c) (BD c') (BD c) htw (hpol c') (hpol c)
    (algebraMap c.F c'.F) rc hrc₁ hrc₂

  obtain ⟨hβ, -, -⟩ := CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨hβ', -, -⟩ := CoeffRings.coeff_isDedFrac E H l c'
  have := GlobalTheory.IsNormalScheme.of_pred (Z c).normal
  have := GlobalTheory.IsNormalScheme.of_pred (Z c').normal
  have : LocallyOfFiniteType (Z c).s := by
    obtain ⟨N, i, hi, e⟩ := (Z c).proj
    have := isProper_str (𝓞 c.F) N
    rw [← e]; infer_instance
  have := (Z c).jQ_open
  have := (Z c').jQ_open
  have : IsDominant (Z c).jQ := ⟨(Z c).jQ_dense⟩
  have : IsDominant (Z c').jQ := ⟨(Z c').jQ_dense⟩
  have hP : IsPullback rc (pullback.snd _ _) (pullback.snd Xo.s (spMap (algebraMap (KA l) c.F)))
      (spMap (algebraMap c.F c'.F)) :=
    IsPullback.of_right (by rw [hrc₁, hcomp]; exact IsPullback.of_hasPullback _ _) hrc₂ (IsPullback.of_hasPullback _ _)
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd (Z c).s (spMap (algebraMap (𝓞 c.F) c.F)))
      (spMap (algebraMap c.F c'.F)) :=
    isPullback_genericFibre_of_isFinite (algebraMap (𝓞 c.F) c.F) (algebraMap (𝓞 c'.F) c'.F)
      (RingOfIntegers.mapRingHom (algebraMap c.F c'.F)) (algebraMap c.F c'.F) hβ.2.2 hβ'.2.2 rfl (Z c).s (Z c').s
      (pullback.snd Xo.s (spMap (algebraMap (KA l) c.F))) πc hπc (Z c).jQ (Z c).jQ_over (hP.isoPullback.inv ≫ (Z c').jQ)
      (by rw [Category.assoc, (Z c').jQ_over, hP.isoPullback_inv_snd]) q hq₁ hq₂
      (by rw [Category.assoc, hqj, hP.isoPullback_inv_fst_assoc])
  have hnorm := isNormalScheme_genericFibre (algebraMap (𝓞 c'.F) c'.F) hβ'.2.2 (Z c').s
  have hpr : IsProper (pullback.snd (Z c').s (spMap (algebraMap (𝓞 c'.F) c'.F))) := isProper_genStr (Z c')
  have hpr' : IsProper (pullback.snd (Z c).s (spMap (algebraMap (𝓞 c.F) c.F))) := isProper_genStr (Z c)
  have hqp : IsQProjOver (pullback.snd (Z c').s (spMap (algebraMap (𝓞 c'.F) c'.F))) := by
    obtain ⟨N, i, hi, e⟩ := ProjSpace.isProjOver_pullback_snd (algebraMap (𝓞 c'.F) c'.F) (Z c').proj
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  exact exists_descent_of_galois Xo.s (pullback.snd (Z c').s _) (pullback.snd (Z c).s _) hqp (Z c').jQ (Z c').jQ_over
    (Z c).jQ ρ hρ₂ r hr₁ hr₂ hρj q hq rc hrc₁ hrc₂ hqj

end GlobalTheory.GenericDescent
