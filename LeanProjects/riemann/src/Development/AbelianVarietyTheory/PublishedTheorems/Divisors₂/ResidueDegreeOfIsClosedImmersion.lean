import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k}

theorem refines_pull_pull (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = t)
    (h : (g ≫ f) ≫ p = t) :
    Refines ((L.pull f hf).pull g hg) (L.pull (g ≫ f) h) (fun c => c PUnit.unit) 0 where
  le c y hy := mem_iInter.2 fun a => mem_iInter.1 (mem_iInter.1 hy PUnit.unit) a
  g W r z c c' hc hc' := by
    have h₁ := mem_iInter.1 hc PUnit.unit
    have h₂ := mem_iInter.1 hc' PUnit.unit
    refine (gm_pull_g _ g r z c c' hc hc').trans ((gm_pull_g _ f (r ≫ g) z _ _ h₁ h₂).trans ?_)
    refine Eq.trans ?_ (gm_pull_g _ (g ≫ f) r z (c PUnit.unit) (c' PUnit.unit)
      (mem_iInter.2 fun a => mem_iInter.1 h₁ a) (mem_iInter.2 fun a => mem_iInter.1 h₂ a)).symm
    rw [Category.assoc]
  φ σ c y hy := by
    refine (((L.pull f hf).φ σ).pull_φ g hg c y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
    refine Eq.trans ?_ (((L.φ σ).pull_φ (g ≫ f) h (c PUnit.unit) y).symm.trans (add_zero _).symm)
    exact congrArg _ (Subtype.ext (Category.assoc _ _ _))

theorem refines_pull_comp (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = t)
    (h : (g ≫ f) ≫ p = t) :
    Refines (L.pull (g ≫ f) h) ((L.pull f hf).pull g hg) (fun c _ => c) 0 where
  le c y hy := mem_iInter.2 fun _ => mem_iInter.2 fun a => mem_iInter.1 hy a
  g W r z c c' hc hc' := by
    have h₁ : (r ≫ g) z ∈ (L.B.pull f).U c := mem_iInter.2 fun a => mem_iInter.1 hc a
    have h₂ : (r ≫ g) z ∈ (L.B.pull f).U c' := mem_iInter.2 fun a => mem_iInter.1 hc' a
    have h₃ : r z ∈ ((L.B.pull f).pull g).U fun _ => c := mem_iInter.2 fun _ => h₁
    have h₄ : r z ∈ ((L.B.pull f).pull g).U fun _ => c' := mem_iInter.2 fun _ => h₂
    have e₁ := gm_pull_g (L.B.pull f) g r z (fun _ => c) (fun _ => c') h₃ h₄
    have e₂ := gm_pull_g L.B f (r ≫ g) z c c' h₁ h₂
    have e₃ := gm_pull_g L.B (g ≫ f) r z c c' hc hc'
    rw [← Category.assoc] at e₃
    exact e₃.trans (e₁.trans e₂).symm
  φ σ c y hy := by
    refine ((L.φ σ).pull_φ (g ≫ f) h c y).trans (Eq.symm ((add_zero _).trans ?_))
    refine (((L.pull f hf).φ σ).pull_φ g hg (fun _ => c) y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
    exact congrArg _ (Subtype.ext (Category.assoc _ _ _))

variable {L : HermLB p} {h : X → ℝ} {D : ℕ}

theorem IsArithHeight.restrict (hX : IsArithVar p D) (H : L.IsArithHeight h) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q) : (L.pull i hi).IsArithHeight fun y => h (i y) where
  vertical Z j _ _ κ _ _ _ d hd := (H.vertical Z (j ≫ i) κ d hd).trans (congrArg (fun n : ℤ => (n : ℝ) * _)
    (topSelf_congr κ (L.restr (j ≫ i)).isLB ((L.pull i hi).restr j).isLB
      (L.refines_pull_comp i hi j rfl (by rw [Category.assoc, hi])).lbIso d))
  point Z j _ _ _ hc hd r hr := by
    have key (t : Z ⟶ Sp k) (ht : (j ≫ i) ≫ p = t) (r) (hr : IsRatSec (L.pull (j ≫ i) ht).B r) :
        h (i (j (genericPoint Z))) = (L.pull (j ≫ i) ht).curveDeg hr ∧ IsArithVar t 0 := by
      subst ht
      exact ⟨H.point Z (j ≫ i) hc hd r hr, hX.of_isClosedImmersion (j ≫ i) hc hd⟩
    have e : (j ≫ i) ≫ p = j ≫ q := by rw [Category.assoc, hi]
    have h' := L.refines_pull_comp i hi j rfl e
    obtain ⟨h₁, h₂⟩ := key _ e _ (h'.isRatSec hr)
    refine h₁.trans ?_
    rw [HermLB.curveDeg, HermLB.curveDeg, h'.div hr]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h'.logNorm hr (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint h₂ y]
    exact CartierDiv.genericPoint_notMem_supp _
  recursion Z j _ _ _ hc e he hd m r hr := by
    have key (t : Z ⟶ Sp k) (ht : (j ≫ i) ≫ p = t) (r) (hr : IsRatSec ((L.pull (j ≫ i) ht).pow m).B r) :
        (L.pull (j ≫ i) ht).ArchIntegrable ((L.pull (j ≫ i) ht).pow m) e hr ∧
        m * h (i (j (genericPoint Z))) =
          ∑ᶠ z, ((((L.pull (j ≫ i) ht).pow m).div hr).mult z : ℝ) * h (i (j z)) -
            (L.pull (j ≫ i) ht).archInt ((L.pull (j ≫ i) ht).pow m) e hr := by
      subst ht
      exact H.recursion Z (j ≫ i) hc e he hd m r hr
    have e' : (j ≫ i) ≫ p = j ≫ q := by rw [Category.assoc, hi]
    have h' := L.refines_pull_comp i hi j rfl e'
    have h'' := h'.pow m
    obtain ⟨h₁, h₂⟩ := key _ e' _ (h''.isRatSec hr)
    unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [h'.chernPart] at h₁
    refine ⟨fun σ => Weight.ChernIntegrableOn.congr (h₁ σ) (isOpen_offSupp _).measurableSet
      fun y hy => h''.logNorm hr hy, h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
    rw [h'.chernInt]
    exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h''.logNorm hr hy

theorem IsArithHeight.isSelfInter_restrict (hX : IsArithVar p D) (H : L.IsArithHeight h) [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ p = q) : (L.pull i hi).IsSelfInter (h (i (genericPoint Y))) :=
  ⟨_, H.restrict hX i hi, rfl⟩

end GlobalTheory.HermLB

namespace GlobalTheory.Published

def HeightProjection : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D e : ℕ),
    IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
      topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) →
      π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h →
        (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))

def CycleHeights : Prop := ArExists ∧ ArMix ∧ HeightProjection

theorem residueDegree_of_isClosedImmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have h : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective _, fun a => by
      obtain ⟨b, rfl⟩ := X.residue_surjective x a
      obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
      exact ⟨Y.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩⟩
  exact (LinearEquiv.ofBijective (Algebra.linearMap _ _) h).finrank_eq.symm.trans (CommSemiring.finrank_self _)

theorem heightProjection_of_arProj (H : ArProj) : HeightProjection := by
  intro k _ X Y _ p q D e hX hY π hπ hd hm L h hh
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (π (genericPoint Y))
  have hr : range i = closure {π (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ Z, g ≫ i = π := ⟨inv (Limits.pullback.snd i π) ≫ Limits.pullback.fst i π, by
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint Z := i.isClosedEmbedding.injective hi.symm
  have hdeg : (g ≫ i).residueDegree (genericPoint Y) = g.residueDegree (genericPoint Y) := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion i, one_mul]
  have hc : CharZero Γ(Z, ⊤) := have := hY.charZero; g.appTop.hom.charZero
  have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc
    ((topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr).symm.trans hd)
  have hq : g ≫ i ≫ p = q := (Category.assoc _ _ _).symm.trans hπ
  obtain ⟨f, hf, e₁⟩ := (H k Z Y (i ≫ p) q e hZ hY g hq hg (hdeg ▸ hm)).1 _ _ (hh.isSelfInter_restrict hX i rfl)
  exact ⟨f, (L.refines_pull_pull i rfl g hq hπ).isArithHeight hY hf, by rw [e₁, hdeg, hi]⟩

theorem cycleHeights_of_arCalc (H : ArCalc) : CycleHeights :=
  ⟨H.arExists, H.arMix, heightProjection_of_arProj H.arProj⟩

namespace CycleHeights

theorem arExists (H : CycleHeights) : ArExists := H.1

theorem arMix (H : CycleHeights) : ArMix := H.2.1

theorem heightProjection (H : CycleHeights) : HeightProjection := H.2.2

theorem arChange (H : CycleHeights) : ArChange := arChange_of_arMix H.1 H.2.1

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D e : ℕ}

theorem existsUnique (H : CycleHeights) (hX : IsArithVar p D) (L : HermLB p) : ∃! h, L.IsArithHeight h :=
  have := hX.isIntegral
  have ⟨h, hh⟩ := (H.1 k X p D hX).1 L
  ⟨h, hh, fun _ h' => h'.unique hX hh⟩

theorem height_pull (H : CycleHeights) (hX : IsArithVar p D) (hY : IsArithVar q e) (π : Y ⟶ X) (hπ : π ≫ p = q)
    {L : HermLB p} {h : X → ℝ} {h' : Y → ℝ} (hh : L.IsArithHeight h) (hh' : (L.pull π hπ).IsArithHeight h')
    {W : Scheme.{0}} [IsIntegral W] (j : W ⟶ Y) [IsClosedImmersion j] (hc : CharZero Γ(W, ⊤)) {d : ℕ}
    (hd : topologicalKrullDim W = (d + 1 : ℕ))
    (hd' : topologicalKrullDim (closure ({π (j (genericPoint W))} : Set X)) = (d + 1 : ℕ))
    (hm : π.residueDegree (j (genericPoint W)) ≠ 0) :
    h' (j (genericPoint W)) = π.residueDegree (j (genericPoint W)) * h (π (j (genericPoint W))) := by
  have hW := hY.of_isClosedImmersion j hc hd
  have e₁ : (j ≫ π) ≫ p = j ≫ q := by rw [Category.assoc, hπ]
  have hdeg : (j ≫ π).residueDegree (genericPoint W) = π.residueDegree (j (genericPoint W)) := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion j, mul_one]
  obtain ⟨f, hf, e₂⟩ := H.2.2 k X W p _ D d hX hW (j ≫ π) e₁ hd' (hdeg ▸ hm) L h hh
  rw [hdeg] at e₂
  exact (hh'.isSelfInter_restrict hY j rfl).unique hW
    ⟨f, (L.refines_pull_comp π hπ j rfl e₁).isArithHeight hW hf, e₂⟩

theorem isSelfInter_pull_of_isIso_restrict (H : CycleHeights) [IsIntegral X] [IsIntegral Y] (hX : IsArithVar p D)
    (hY : IsArithVar q D) (π : Y ⟶ X) (hπ : π ≫ p = q) (U : X.Opens) (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)]
    {L : HermLB p} {a : ℝ} (ha : L.IsSelfInter a) : (L.pull π hπ).IsSelfInter a := by
  obtain ⟨h₁, h₂⟩ := generic_of_isIso_restrict π U hU
  obtain ⟨h, hh, rfl⟩ := ha
  have := H.2.2 k X Y p q D D hX hY π hπ (by
    rw [h₁, (genericPoint_spec X).def]
    exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans hX.dim_eq)
    (by rw [h₂]; exact one_ne_zero) L h hh
  rwa [h₂, h₁, Nat.cast_one, one_mul] at this

theorem isSelfInter_shift (H : CycleHeights) [IsIntegral X] (hX : IsArithVar p D) {L : HermLB p} {a : ℝ}
    (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (ha : L.IsSelfInter a) :
    (L.shift t ht).IsSelfInter (a + ((D : ℝ) + 1) * ∑ᶠ σ, t σ * (L.φ σ).chernInt D univ fun _ => 1) :=
  TwistTop.isSelfInter_shift H.1 H.arChange k X p D hX L a t ht ha

end CycleHeights

example (t : ℝ) : IsArithVar (𝟙 (Sp ℤ)) 0 ∧
    topologicalKrullDim (closure ({genericPoint (Sp ℤ)} : Set (Sp ℤ))) = (0 + 1 : ℕ) ∧
    (𝟙 (Sp ℤ) : _ ⟶ _).residueDegree (genericPoint _) = 1 ∧
    ((ArithBase.trivShift t).pull (𝟙 _) (Category.id_comp _)).IsSelfInter t := by
  obtain ⟨h, hh, e⟩ := ArithBase.isSelfInter_trivShift t
  refine ⟨ArithBase.isArithVar_int, ?_, Scheme.Hom.residueDegree_id _,
    e ▸ hh.isSelfInter_restrict ArithBase.isArithVar_int (𝟙 _) (Category.id_comp _)⟩
  rw [(genericPoint_spec (Sp ℤ)).def]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans
    ArithBase.isArithVar_int.dim_eq

end GlobalTheory.Published
