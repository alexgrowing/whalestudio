import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsSecNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR IsLocalRing

noncomputable section
namespace GlobalTheory.SpanBall
open TWM TWO SectionScalarValuation

section Gen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] (S : ValuationSubring F) (g : V →+* S)
  (hg : (algebraMap S F).comp g = algVF (F := F) (V := V))

abbrev TS : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom g))

abbrev ιT : TF (R := V) F ⟶ TS S g :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap S F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap S F)) ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp])

abbrev jT : DegPre.BF D.toPre F ⟶ TS S g ⊗ D.toPre.P.A := ιT S g hg ▷ D.toPre.P.A

theorem jT_snd : (jT S g hg (D := D)).left ≫ (snd (TS S g) D.toPre.P.A).left = (DegPre.prB D.toPre F).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem jT_fst : (jT S g hg (D := D)).left ≫ (fst (TS S g) D.toPre.P.A).left =
    (fst (TF (R := V) F) D.toPre.P.A).left ≫ (ιT S g hg).left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]

abbrev ιs (r : Γ(Spec (CommRingCat.of S), ⊤)) : F :=
  algebraMap S F ((Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom r)

theorem gs_jT {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (r : Γ(Spec (CommRingCat.of S), ⊤)) :
    gs (ρ ≫ (jT S g hg (D := D)).left) z ⊤ ((fst (TS S g) D.toPre.P.A).left.appTop.hom r) =
      gs ρ z ⊤ (gF D.toPre F (ιs S r)) := by
  have e1 : gs (ρ ≫ (jT S g hg (D := D)).left) z ⊤ ((fst (TS S g) D.toPre.P.A).left.appTop.hom r) =
      gs ((ρ ≫ (jT S g hg (D := D)).left) ≫ (fst (TS S g) D.toPre.P.A).left) z ⊤ r := gs_pull _ _ z ⊤ trivial r
  rw [e1, Category.assoc, jT_fst, ← Category.assoc]
  have e2 : gs ((ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ (ιT S g hg).left) z ⊤ r =
      gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤ ((ιT S g hg).left.appTop.hom r) :=
    (gs_pull _ _ z ⊤ trivial r).symm
  have e3 : gs ρ z ⊤ (gF D.toPre F (ιs S r)) = gs (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) z ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (ιs S r)) := gs_pull _ _ z ⊤ trivial _
  rw [e2, e3, show (ιT S g hg).left = Spec.map (CommRingCat.ofHom (algebraMap S F)) from rfl, appTop_specMap]
  rfl

theorem isPullback_jT : IsPullback (jT S g hg (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TS S g) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap S F))) := by
  have H₁ : IsPullback (snd (TS S g) D.toPre.P.A).left (fst (TS S g) D.toPre.P.A).left D.toPre.P.A.hom
      (TS S g).hom := (IsPullback.of_hasPullback (TS S g).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jT_snd S g hg, ← Over.w (ιT S g hg)] at H₀
  exact H₀.of_right (jT_fst S g hg) H₁

include hg in

theorem span_gen (hloc : IsLocalHom g) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) :
    ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.toPre.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (σF i) (D.toPre.famφB α)
        (DegPre.famε k) (σ i) (DegPre.prB D.toPre F).left 1) ∧
      ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (σF i).f j := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TS S g) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TS S g).hom D.toPre.P.A.hom))
  have : CompactSpace (TS S g).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of S)))
  have : QuasiSeparatedSpace (TS S g).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of S)))
  have : CompactSpace (TS S g ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TS S g) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TS S g ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TS S g) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jT_snd S g hg, Category.assoc]) s
  obtain ⟨t, ht, S₀, hS₀⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors S) (isPullback_jT S g hg (D := D)) hL
    (fun i => (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := GlobalTheory.TwistSpanExample.span_holds V D.toPre k hk α S g hloc S₀
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  refine ⟨n, fun i => (t : F)⁻¹ * ιs S (rr i), σ, σF, hσF, fun j => ?_⟩
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιs S (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιs S (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S₀ (𝟙 _ ≫ (jT S g hg (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S₀ (𝟙 _ ≫ (jT S g hg (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS₀ _ (𝟙 _) y _ (hJ.mem (fun a => (jT S g hg (D := D)).left ≫
      (snd (TS S g) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jT S g hg (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t)
    rw [show ιs S ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom t) = (t : F) by simp [ιs]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TS S g) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TS S g) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jT S g hg).left) y hJ
  have g' : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g', inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g', gs_jT, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jT_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]

end Gen

theorem isLocalHom_ball {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {C : Type} [NontriviallyNormedField C] [Algebra (FractionRing V) C]
    (hC : CExt V (maximalIdeal V) C) (S : ValuationSubring C) (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) :
    IsLocalHom ((algVF (F := C) (V := V)).codRestrict S.toSubring fun x => (hS _).2 (hC.1 x)) where
  map_nonunit x hx := by
    by_contra hxu
    have hm : x ∈ maximalIdeal V := (mem_maximalIdeal x).2 hxu
    have h1 : ‖algVF (F := C) (V := V) x‖ < 1 := hC.2 x hm
    obtain ⟨u, hu⟩ := hx
    have a1 : ‖((u : S) : C)‖ ≤ 1 := (hS _).1 (u : S).2
    have a2 : ‖(((u⁻¹ : Sˣ) : S) : C)‖ ≤ 1 := (hS _).1 ((u⁻¹ : Sˣ) : S).2
    have e : ((u : S) : C) * (((u⁻¹ : Sˣ) : S) : C) = 1 := by
      rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
    have e' : ‖((u : S) : C)‖ * ‖(((u⁻¹ : Sˣ) : S) : C)‖ = 1 := by rw [← norm_mul, e, norm_one]
    have hux : ((u : S) : C) = algVF (F := C) (V := V) x := by rw [hu]; rfl
    rw [← hux] at h1
    nlinarith [mul_le_mul_of_nonneg_left a2 (norm_nonneg ((u : S) : C)), norm_nonneg (((u⁻¹ : Sˣ) : S) : C)]

theorem span_ball : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (k : ℕ), 1 ≤ k → ∀ (β : D.toPre.X) (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), ∃ (n : ℕ) (a : Fin n → C) (σ : Fin n → D.toPre.SecB k β) (σF : Fin n → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k))), (∀ i, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C β) (DegPre.famε k) (σF i) (D.toPre.famφB β) (DegPre.famε k) (σ i) (DegPre.prB D.toPre C).left 1) ∧ ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre C (a i) _ * (σF i).f j := by
  intro V _ _ _ D C _ _ hC S hS k hk β s
  exact span_gen (D := D) S _ rfl (isLocalHom_ball hC S hS) hk s

end GlobalTheory.SpanBall
end
