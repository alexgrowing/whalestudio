import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPeriodAnyLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PeriodSpacesFixedByCmCurveTorsionFixingAutomorph
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed

noncomputable section

namespace GlobalTheory.FixedPoint

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompRat GlobalTheory.CompRat.FixedConst
  GlobalTheory.AllWt GlobalTheory.FlatLine

theorem exists_descent {Y : Scheme.{0}} (K : IntermediateField ℚ ℂ) (x : Sp ℂ ⟶ Y)
    (hx : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → spMap (τ : ℂ →+* ℂ) ≫ x = x) :
    ∃ g : Sp K ⟶ Y, spMap (algebraMap K ℂ) ≫ g = x := by
  classical
  obtain ⟨⟨y, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField ℂ Y).symm.surjective x
  have hfix : ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ K, τ a = a) → φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ) = φ := by
    intro τ hτ
    have e : spMap (τ : ℂ →+* ℂ) ≫ (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ⟩ =
        (Scheme.SpecToEquivOfField ℂ Y).symm ⟨y, φ ≫ CommRingCat.ofHom (τ : ℂ →+* ℂ)⟩ := by
      change Spec.map _ ≫ Spec.map φ ≫ _ = Spec.map (φ ≫ _) ≫ _
      rw [Spec.map_comp, Category.assoc]
    have h2 := (Scheme.SpecToEquivOfField ℂ Y).symm.injective (e.symm.trans (hx τ hτ))
    exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2
  have hmem : ∀ r, φ.hom r ∈ K := by
    intro r
    obtain ⟨a, ha⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := K) (φ.hom r) (fun σ => by
      have h := hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩)
      exact congrArg (fun f => f.hom r) h)
    rw [← ha]
    exact a.2
  let ψ : Y.residueField y →+* K := φ.hom.codRestrict K hmem
  refine ⟨Spec.map (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ Y.fromSpecResidueField y, ?_⟩
  have hc : (CommRingCat.ofHom ψ : Y.residueField y ⟶ CommRingCat.of K) ≫ CommRingCat.ofHom (algebraMap K ℂ) = φ := by
    ext r
    rfl
  exact (Spec.map_comp_assoc _ _ _).symm.trans (congrArg (· ≫ Y.fromSpecResidueField y) (congrArg Spec.map hc))

theorem ev_eq_of_restrict {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (p : Sp ℂ) (hp : x p ∈ W) (f : Γ(Y, ⊤))
    (n : ℕ) (hf : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op f = n) : ev x f = n := by
  have hr : Set.range x ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim q p]
  have hf' : (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom f = n := hf
  have hle : W.ι ''ᵁ ⊤ ≤ W := (Scheme.Opens.ι_image_top W).le
  have e : (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op = (homOfLE (le_top : W ≤ ⊤)).op ≫ (homOfLE hle).op := rfl
  have key : (Y.presheaf.map (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op).hom f = n := by
    rw [e, Functor.map_comp]
    exact (congrArg (Y.presheaf.map (homOfLE hle).op).hom hf').trans (map_natCast _ n)
  rw [← IsOpenImmersion.lift_fac W.ι x hr, ev_comp, Scheme.Opens.ι_appTop]
  exact (congrArg _ key).trans (map_natCast _ n)

theorem exists_indicator {Y : Scheme.{0}} {Z : Set Y} (hZ : IsClopen Z) :
    ∃ f : Γ(Y, ⊤), ∀ (x : Sp ℂ ⟶ Y) (p : Sp ℂ), (x p ∈ Z → ev x f = 1) ∧ (x p ∉ Z → ev x f = 0) := by
  let V : Y.Opens := ⟨Z, hZ.isOpen⟩
  let W : Y.Opens := ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩
  have hVW : V ⊔ W = ⊤ := by
    apply TopologicalSpace.Opens.ext
    simp [V, W, Set.union_compl_self]
  have hdis : Disjoint V W := by
    rw [disjoint_iff]
    apply TopologicalSpace.Opens.ext
    simp [V, W]
  obtain ⟨f, hfV, hfW⟩ := exists_extension_zero V W hVW hdis 1
  refine ⟨f, fun x p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
  · have h := ev_eq_of_restrict x V p hp f 1 (by rw [hfV, Nat.cast_one])
    simpa using h
  · have h := ev_eq_of_restrict x W p hp f 0 (by rw [hfW, Nat.cast_zero])
    simpa using h

private theorem exists_isTypeFn' {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, fun τ => ?_⟩
  have hcard : Nat.card {i // (e.symm i).1 = τ} = m τ := by
    rw [Nat.card_congr (e.symm.subtypeEquiv (p := fun i => (e.symm i).1 = τ) (q := fun s => s.1 = τ)
      (fun _ => Iff.rfl)), Nat.card_congr (Equiv.sigmaSubtype τ), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]; simp [m, h]
  · rw [hcard]; simp [m, h]

private theorem spMap_comp_spMap_divisor {R₀ R R' : Type} [CommRing R₀] [CommRing R] [CommRing R'] (f : R →+* R')
    (g : R₀ →+* R) : spMap f ≫ spMap g = spMap (f.comp g) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_fixed_point (hD : 1 ≤ Dw.p + Dw.q)
    (hsig : Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) (Z : Comp Xo c) :
    ∃ x : Sp ℂ ⟶ Xo.XF c, x ≫ strK = spMap (algebraMap c.F ℂ) ∧ (∀ p, x p ∈ (Z : Set (Xo.XF c))) ∧
      ∀ τ : ℂ ≃+* ℂ, (∀ a ∈ c.F, τ a = a) → FixesCurve H τ l.M' → spMap (τ : ℂ →+* ℂ) ≫ x = x := by
  classical
  obtain ⟨g, ty, hty⟩ := exists_isTypeFn' H Dw.p Dw.q
  let σ₀ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hσ₀ : σ₀ (baseKA l).ρ = H.rt0 := rfl
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H Dw l Xo σ₀ g ty hD hσ₀ hty

  obtain ⟨L, _, _, j, g₀, hg₀, hZ₀⟩ := GlobalTheory.FlatLine.exists_numberField_point Z
  letI : Algebra c.F L := j.toAlgebra
  haveI : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ c.F), eq_ratCast (algebraMap ℚ L), map_ratCast])
  haveI : Algebra.IsAlgebraic c.F L := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := IsAlgClosed.lift
  have hφ : (φ : L →+* ℂ).comp j = algebraMap c.F ℂ := RingHom.ext fun a => φ.commutes a
  obtain ⟨hx₀, hZx₀⟩ := GlobalTheory.FlatLine.point_ext hg₀ hZ₀ (φ : L →+* ℂ)
  rw [hφ] at hx₀
  set x₀ : Sp ℂ ⟶ Xo.XF c := spMap (φ : L →+* ℂ) ≫ g₀ with hx₀def
  have hover : x₀ ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap σ₀ := by
    rw [pullback.condition, ← Category.assoc]
    erw [hx₀]
    rw [spMap_comp_spMap_divisor]
  obtain ⟨i, P, hP, hPx⟩ := F.onto _ (by rw [Category.assoc]; exact hover)
  obtain ⟨P', hP', hs⟩ := GlobalTheory.CompRat.exists_isSplit_period_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty hsig i
  have hcond : F.u i P' ≫ Xo.s = spMap (algebraMap c.F ℂ) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [F.over_σ i P' hP', spMap_comp_spMap_divisor]
  let xs : Sp ℂ ⟶ Xo.XF c := pullback.lift (F.u i P') (spMap (algebraMap c.F ℂ)) hcond
  have hxs₁ : xs ≫ pullback.fst _ _ = F.u i P' := pullback.lift_fst _ _ _
  have hxs₂ : xs ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := pullback.lift_snd _ _ _

  obtain ⟨f, hf⟩ := exists_indicator (GlobalTheory.TrivOrderTieCompare.isClopen_comp Z)
  have hvals : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      valAt' x ⊤ f ∈ ({0, 1} : Set ℂ) := by
    intro x _
    rw [valAt'_top]
    by_cases hx : x default ∈ (Z : Set (Xo.XF c))
    · simp [(hf x default).1 hx]
    · simp [(hf x default).2 hx]
  have heq := GlobalTheory.CompRat.valAt_eq_of_finite_values_anyLevel E H Dw l Xo σ₀ g ty F hD hσ₀ hty c
    (algebraMap c.F ℂ) f _ (Set.toFinite _) hvals i P P' hP hP' x₀ xs hPx.symm hx₀ hxs₁ hxs₂
  rw [valAt'_top, valAt'_top, (hf x₀ default).1 (hZx₀ default)] at heq
  refine ⟨xs, hxs₂, fun p => ?_, fun τ hτ hfix => ?_⟩
  · by_contra hp
    rw [(hf xs p).2 hp] at heq
    exact one_ne_zero heq
  · have hτσ : (τ : ℂ →+* ℂ).comp σ₀ = σ₀ := RingHom.ext fun a => hτ _ (IntermediateField.inclusion c.le a).2
    have hfixed := GlobalTheory.CompRat.AnyLevel.conj_point_eq_of_isSplit F hD hσ₀ hty τ hτσ hfix i P' hP' hs
    apply pullback.hom_ext
    · rw [Category.assoc, hxs₁, hfixed]
    · rw [Category.assoc, hxs₂, spMap_comp_spMap_divisor]
      congr 1
      exact RingHom.ext fun a => hτ a a.2

end GlobalTheory.FixedPoint

namespace GlobalTheory.FixedPoint

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
open AlgebraicGeometry CategoryTheory

theorem exists_frPt_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  intro E _ _ _ H Dw l Xo c hD hsig K _ hle hK Z
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨x, _, hxZ, hxfix⟩ := exists_fixed_point (H := H) (Xo := Xo) (c := c) hD hsig Z
  obtain ⟨g, hg⟩ := exists_descent K x (fun τ hτ => hxfix τ (fun a ha => hτ a (hle ha)) (hK τ hτ))
  have hcancel : ∀ a b : Sp K ⟶ Sp c.F, spMap (algebraMap K ℂ) ≫ a = spMap (algebraMap K ℂ) ≫ b → a = b := by
    intro a b hab
    rw [← Spec.map_preimage a, ← Spec.map_preimage b] at hab ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hab
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) hab
  have hgK : g ≫ strK = spMap (algebraMap c.F K) := by
    apply hcancel
    rw [← Category.assoc, hg, ‹x ≫ strK = spMap (algebraMap c.F ℂ)›, spMap_comp_spMap_divisor]
    rfl
  obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (g ≫ GlobalTheory.FlatLine.prX Xo c) (GlobalTheory.FlatLine.prX_over hgK)
  refine ⟨y, fun s => ?_⟩
  rw [GlobalTheory.FlatLine.ptF_eq hgK hy]
  have hs : s = spMap (algebraMap K ℂ) default := Subsingleton.elim _ _
  have h1 := hxZ default
  rw [← hg] at h1
  rw [hs]
  exact h1

end GlobalTheory.FixedPoint
