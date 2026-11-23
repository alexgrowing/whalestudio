import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O.WeightHt

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem card_ne_zero (w : V.G) (hw : IsClosed ({w} : Set V.G)) :
    (Nat.card (V.X.residueField (V.j w) →+* ℂ) : ℝ) ≠ 0 := by
  have hx : IsClosed ({V.π w} : Set Y.X) := by
    have := V.π.isClosedMap _ hw
    rwa [Set.image_singleton] at this
  obtain ⟨_, _⟩ := ExtConj.pts Y _ hx
  have hN : (Nat.card {y : AlgPt Y // below y.1 = V.π w} : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hF : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd : (V.π.residueDegree w : ℝ) ≠ 0 := by
    letI := (V.π.residueFieldMap w).hom.toAlgebra
    haveI : Module.Finite (Y.X.residueField (V.π w)) (V.G.residueField w) :=
      residueFieldMap_finite_of_locallyQuasiFinite V.π _
    exact Nat.cast_ne_zero.2 (Module.finrank_pos (R := Y.X.residueField (V.π w)) (M := V.G.residueField w)).ne'
  rw [CoverHt.card_emb V w hw]
  exact mul_ne_zero hF (mul_ne_zero hd hN)

theorem height_eq {u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ} {hu : ∀ σ y, CxPts.CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {w : V.G}
    (hw : IsClosed ({w} : Set V.G)) {h : V.X → ℝ} (H : (fnB u hu hc).IsArithHeight h) :
    h (V.j w) = (∑ᶠ σ, ∑ᶠ y ∈ {y : CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y) / 2 := by
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (V.j w)
  have := V.ar.isNoetherian_sub i
  obtain ⟨hc', hd⟩ := CoverHt.isAlgPt V w hw
  have hri : Set.range i = closure {V.j w} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hri] at hd
  rw [← hi] at hc'
  have hc'' : CharZero (Z.residueField (genericPoint Z)) :=
    charZero_of_injective_ringHom (i.residueFieldMap (genericPoint Z)).hom.injective
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ V.p) 0 := V.ar.of_isClosedImmersion i hcΓ hd
  have hr : IsRatSec ((fnB u hu hc).restr i).B fun _ => 1 := fun a b h => by
    have hL := ((fnB u hu hc).restr i).isLB
    obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
    have := congrArg (fun u : Γ(Z, _)ˣ => fnOf _ h.1 u.val) (hL.g_self a)
    rw [Units.val_one, map_one] at this
    exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm
  have hdeg := H.point Z i hcΓ hd _ hr
  have h₁ (z : Z) : (((fnB u hu hc).restr i).div hr).mult z = 0 := by
    obtain ⟨c, hc⟩ := exists_chart ((fnB u hu hc).restr i).isLB z
    exact ((presents_divOfRatSec _ hr).isEqn c z hc).mult_eq.trans (unitAt_one z).ord_eq_zero
  have hgen (y : Sp ℂ ⟶ Z) : below y = genericPoint Z :=
    SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField ℂ Z y).2.hom.charZero
  have h₂ (σ : 𝓞 F →+* ℂ) (y : CxPts (i ≫ V.p) σ) :
      logNorm (((fnB u hu hc).restr i).φ σ) (fun _ => 1) y = -(1 / 2) * u σ (Points.PtsOver.map i rfl _ y) := by
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
    have e₄ := ((fnB u hu hc).φ σ).pull_φ i rfl (CxPts.pick (((fnB u hu hc).restr i).φ σ).isLB y) y
    rw [logNorm, Units.val_one, e, norm_one, Real.log_one]
    refine (congrArg (fun b => 0 - b / 2) e₄).trans ?_
    change 0 - u σ _ / 2 = _
    ring
  have h₃ (σ : 𝓞 F →+* ℂ) : ∑ᶠ y : CxPts (i ≫ V.p) σ, logNorm (((fnB u hu hc).restr i).φ σ) (fun _ => 1) y =
      -(1 / 2) * ∑ᶠ y ∈ {y : CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y := by
    rw [finsum_congr (h₂ σ), ← mul_finsum, ← finsum_subtype_eq_finsum_cond]
    congr 1
    refine finsum_eq_of_bijective (fun y => ⟨Points.PtsOver.map i rfl _ y,
      (Scheme.Hom.comp_apply _ _ _).trans ((congrArg i (hgen y.1)).trans hi)⟩) ⟨fun a b hab => ?_, ?_⟩ fun _ => rfl
    · apply Subtype.ext
      rw [← cancel_mono i]
      exact congrArg (fun t => t.1.1) hab
    · rintro ⟨⟨y, hy⟩, hyx⟩
      obtain ⟨y', hy'⟩ := ClosurePts.lift_closed i (genericPoint Z) y (hyx.trans hi.symm)
      exact ⟨⟨y', by rw [← Category.assoc, hy']; exact hy⟩, Subtype.ext (Subtype.ext hy')⟩
  unfold HermLB.curveDeg at hdeg
  rw [finsum_congr h₃, ← mul_finsum, hi] at hdeg
  simp only [h₁, Int.cast_zero, zero_mul, finsum_zero] at hdeg
  rw [hdeg]
  ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y)
    (u : ∀ σ : 𝓞 F →+* ℂ, GlobalTheory.CxPts V.p σ → ℝ) (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun (u σ)).IsConj (GlobalTheory.Weight.ofFun (u σ'))) (w : V.G), IsClosed ({w} : Set V.G) →
    GlobalTheory.Published.ArExists →
    IsPtHt (fnB u hu hc) (V.j w)
      ((∑ᶠ σ, ∑ᶠ y ∈ {y : GlobalTheory.CxPts V.p σ | y.1 (IsLocalRing.closedPoint ℂ) = V.j w}, u σ y) /
        (2 * (Nat.card (V.X.residueField (V.j w) →+* ℂ) : ℝ))) := by
  intro F _ _ Y V u hu hc w hw HE
  obtain ⟨h, H⟩ := (HE _ V.X V.p _ V.ar).1 (fnB u hu hc)
  refine ⟨h, H, ?_⟩
  have := card_ne_zero V w hw
  rw [height_eq V hw H]
  field_simp

end GlobalTheory.Mean4O.WeightHt
