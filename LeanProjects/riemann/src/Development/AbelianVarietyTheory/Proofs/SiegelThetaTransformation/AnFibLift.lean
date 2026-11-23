import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLiftOfProjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Lift

section Val

variable {X Y : Scheme.{0}}

theorem val_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (res h u).val = valAt' x U u.val :=
  valAt'_map x (homOfLE h).op u.val hV

theorem val_pullU (x : Sp ℂ ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (u : Γ(X, U)ˣ) :
    valAt' x (f ⁻¹ᵁ U) (pullU f U u).val = valAt' (x ≫ f) U u.val :=
  valAt'_comp x f U u.val

theorem mem_wchart (x : Sp ℂ ⟶ Y) (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [top_le_preimage_comp, top_le_preimage_iff_mem]
  exact Set.mem_iInter

theorem exists_chart (x : Sp ℂ ⟶ X) (L : LB X) (hL : L.IsLB) : ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
  have h : x (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  exact ⟨j, (top_le_preimage_iff_mem x _).2 hj⟩

theorem val_g_self (x : Sp ℂ ⟶ X) (L : LB X) (hL : L.IsLB) (j : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  rw [← val_res x (le_inf le_rfl le_rfl : L.U j ≤ L.U j ⊓ L.U j) _ h, hL.g_self, Units.val_one, valAt'_one x h]

theorem val_pull_g (x : Sp ℂ ⟶ Y) (L : LB X) (φ : Y ⟶ X) (a b : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull φ).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b))) :
    valAt' x ((L.pull φ).U (fun _ => a) ⊓ (L.pull φ).U (fun _ => b)) ((L.pull φ).g (fun _ => a) (fun _ => b)).val =
      valAt' (x ≫ φ) (L.U a ⊓ L.U b) (L.g a b).val := by
  refine (valAt'_units_prod x h _ _).trans ?_
  rw [Fintype.prod_unique]
  refine (valAt'_units_zpow x h _ 1).trans ?_
  rw [zpow_one]
  exact (val_res x _ _ h).trans (val_pullU x φ (L.U a ⊓ L.U b) (L.g a b))

theorem val_linCombIso {L M : LB X} {K : Type} [Fintype K] [Unique K] (w : LB.Iso L M) (φ : Y ⟶ X)
    (x : Sp ℂ ⟶ Y) (a : M.ι) (j : L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart M (fun _ : K => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => j))) :
    valAt' x (LB.wchart M (fun _ : K => φ) (fun _ => a) ⊓ LB.wchart L (fun _ : K => φ) (fun _ => j))
      ((LB.linCombIso w (K := K) (fun _ => φ) (fun _ => 1)).s (fun _ => a, fun _ => j)).val =
      valAt' (x ≫ φ) (M.U a ⊓ L.U j) (w.s (a, j)).val := by
  refine (valAt'_units_prod x h _ _).trans ?_
  rw [Fintype.prod_unique]
  refine (valAt'_units_zpow x h _ 1).trans ?_
  rw [zpow_one]
  exact (val_res x _ _ h).trans (val_pullU x φ (M.U a ⊓ L.U j) (w.s (a, j)))

noncomputable def wv {L : LB X} {L' : LB Y} {φ : Y ⟶ X} (w : LB.Iso L' (L.pull φ)) (x : Sp ℂ ⟶ Y)
    (a : L.ι) (j : L'.ι) : ℂ :=
  valAt' x ((L.pull φ).U (fun _ => a) ⊓ L'.U j) (w.s (fun _ => a, j)).val

theorem mem_both {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {x : Sp ℂ ⟶ Y} {a : L.ι} {j : L'.ι}
    (ha : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U a) (hj : ⊤ ≤ x ⁻¹ᵁ L'.U j) :
    ⊤ ≤ x ⁻¹ᵁ ((L.pull φ).U (fun _ => a) ⊓ L'.U j) :=
  (top_le_preimage_inf _ _ _).2 ⟨(mem_wchart x L _ _).2 fun _ => ha, hj⟩

theorem wv_ne {L : LB X} {L' : LB Y} {φ : Y ⟶ X} (w : LB.Iso L' (L.pull φ)) {x : Sp ℂ ⟶ Y} {a : L.ι} {j : L'.ι}
    (ha : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U a) (hj : ⊤ ≤ x ⁻¹ᵁ L'.U j) : wv w x a j ≠ 0 :=
  valAt'_unit_ne_zero x (mem_both ha hj) _

theorem wv_change {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) {x : Sp ℂ ⟶ Y}
    {a b : L.ι} {j k : L'.ι} (ha : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U a) (hb : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U b)
    (hj : ⊤ ≤ x ⁻¹ᵁ L'.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L'.U k) :
    wv w x a j = valAt' (x ≫ φ) (L.U a ⊓ L.U b) (L.g a b).val *
      (valAt' x (L'.U j ⊓ L'.U k) (L'.g j k).val)⁻¹ * wv w x b k := by
  have h : ⊤ ≤ x ⁻¹ᵁ (((L.pull φ).U (fun _ => a) ⊓ L'.U j) ⊓ ((L.pull φ).U (fun _ => b) ⊓ L'.U k)) :=
    (top_le_preimage_inf _ _ _).2 ⟨mem_both ha hj, mem_both hb hk⟩
  have e := congrArg (fun u => valAt' x _ (Units.val u)) (hw (fun _ => a, j) (fun _ => b, k))
  refine ((val_res x _ _ h).symm.trans e).trans ?_
  refine (valAt'_mul x _ _ _).trans (congrArg₂ (· * ·) ?_ (val_res x _ _ h))
  refine (valAt'_mul x _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)
  · refine (val_res x _ _ h).trans (val_pull_g x L φ a b ?_)
    exact (top_le_preimage_inf _ _ _).2 ⟨(mem_wchart x L _ _).2 fun _ => ha, (mem_wchart x L _ _).2 fun _ => hb⟩
  · exact (valAt'_units_inv x h _).trans (congrArg (·⁻¹) (val_res x _ _ h))

theorem exists_frame {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : LB X} {L' : LB Y} (hL : L.IsLB)
    (hL' : L'.IsLB) {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) (e : V → (Sp ℂ ⟶ Y))
    (hol : IsHolTo Set.univ e) (fr : L.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j})
    (fr_ne : ∀ j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) :
    ∃ fr' : L'.ι → V → ℂ, (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ e z ⁻¹ᵁ L'.U j}) ∧
      (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr' j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L'.U j ⊓ L'.U j') →
        fr' j z = valAt' (e z) (L'.U j ⊓ L'.U j') (L'.g j j').val * fr' j' z) ∧
      ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr a z = wv w (e z) a j * fr' j z := by
  choose ch hch using fun z => exists_chart (e z ≫ φ) L hL
  have key : ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j →
      fr a z = wv w (e z) a j * (fr (ch z) z / wv w (e z) (ch z) j) := by
    intro a j z ha hj
    have h1 := wv_ne w (hch z) hj
    rw [wv_change hw ha (hch z) hj hj, val_g_self _ L' hL' j hj,
      fr_g a (ch z) z ((top_le_preimage_inf _ _ _).2 ⟨ha, hch z⟩)]
    field_simp
  refine ⟨fun j z => fr (ch z) z / wv w (e z) (ch z) j, fun j z₀ hz₀ => ?_, fun j z hj => ?_,
    fun j j' z h => ?_, key⟩
  · have hN := (hol ((L.pull φ).U (fun _ => ch z₀) ⊓ L'.U j) (w.s (fun _ => ch z₀, j)).val)
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, mem_both (hch z₀) hz₀⟩
    have hsub : ∀ z, ⊤ ≤ e z ⁻¹ᵁ ((L.pull φ).U (fun _ => ch z₀) ⊓ L'.U j) →
        ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U (ch z₀) ∧ ⊤ ≤ e z ⁻¹ᵁ L'.U j := fun z hz =>
      ⟨(mem_wchart (e z) L _ _).1 ((top_le_preimage_inf _ _ _).1 hz).1 ⟨⟩, ((top_le_preimage_inf _ _ _).1 hz).2⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => (hsub z hz.2).1)
    have d2 : DifferentiableAt ℂ (fun z => wv w (e z) (ch z₀) j) z₀ := hN.2.differentiableAt hm
    refine ((d1.mul (d2.inv (wv_ne w (hch z₀) hz₀))).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    have h1 := wv_ne w (hsub z hz.2).1 (hsub z hz.2).2
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [key (ch z₀) j z (hsub z hz.2).1 (hsub z hz.2).2, mul_comm (wv w (e z) (ch z₀) j), mul_inv_cancel_right₀ h1]
  · exact div_ne_zero (fr_ne _ z (hch z)) (wv_ne w (hch z) hj)
  · obtain ⟨hj, hj'⟩ := (top_le_preimage_inf _ _ _).1 h
    have h1 := wv_ne w (hch z) hj'
    have h2 := valAt'_unit_ne_zero (e z) h (L'.g j j')
    simp only []
    rw [wv_change hw (hch z) (hch z) hj hj', val_g_self _ L hL _ (hch z)]
    field_simp

end Val

section Grp

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']

theorem exists_mulEquiv {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Scheme.{0}}
    (x' : T ⟶ S') (x : T ⟶ S) (hx : x' ≫ f = x) :
    ∃ Φ : (Over.mk x' ⟶ G') ≃* (Over.mk x ⟶ G), ∀ a, (Φ a).left = a.left ≫ φ := by
  subst hx
  let F : (Over.mk x' ⟶ G') → (Over.mk (x' ≫ f) ⟶ G) := fun a =>
    Over.homMk (a.left ≫ φ) (by
      change (a.left ≫ φ) ≫ G.hom = x' ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w a]
      rfl)
  let I : (Over.mk (x' ≫ f) ⟶ G) → (Over.mk x' ⟶ G') := fun y =>
    Over.homMk (h.1.lift y.left x' (Over.w y)) (h.1.lift_snd _ _ _)
  have hF : ∀ x, (F x).left = x.left ≫ φ := fun _ => rfl
  refine ⟨⟨⟨F, I, fun x => ?_, fun y => ?_⟩, fun x y => ?_⟩, hF⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
  · apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  · apply Over.OverMorphism.ext
    exact (h.2 (Over.mk x') x y (F x) (F y) rfl rfl).symm

theorem toUnit_left {T : Scheme.{0}} (x : T ⟶ S) : (toUnit (Over.mk x)).left = x := by
  have := Over.w (toUnit (Over.mk x))
  simpa using this

theorem one_left {T : Scheme.{0}} (x : T ⟶ S) : (1 : Over.mk x ⟶ G).left = x ≫ eSec G := by
  rw [Hom.one_def, Over.comp_left, toUnit_left]
  rfl

theorem val_rig [IsCommMonObj G] [IsCommMonObj G'] (m : CubeMap G' G) (L : RigLB G) (L' : RigLB G')
    (w : LB.Iso L'.L (L.L.pull m.F))
    (hw : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (m.rigPull L.L L.rig))
    (x' : Sp ℂ ⟶ (𝟙_ (Over S')).left) (a : L.L.ι) (j : L'.L.ι)
    (ha : ⊤ ≤ ((x' ≫ eSec G') ≫ m.F) ⁻¹ᵁ L.L.U a) (hj : ⊤ ≤ (x' ≫ eSec G') ⁻¹ᵁ L'.L.U j) :
    valAt' (x' ≫ m.e) ((L.L.pull (eSec G)).U (fun _ => a)) (L.rig.s (fun _ => a)).val =
      wv w (x' ≫ eSec G') a j * valAt' x' ((L'.L.pull (eSec G')).U (fun _ => j)) (L'.rig.s (fun _ => j)).val := by
  have h1 : ⊤ ≤ x' ⁻¹ᵁ LB.wchart (L.L.pull m.F) (fun _ : PUnit => eSec G') (fun _ _ => a) :=
    (mem_wchart x' _ _ _).2 fun _ => (mem_wchart _ _ _ _).2 fun _ => ha
  have h : ⊤ ≤ x' ⁻¹ᵁ (LB.wchart (L.L.pull m.F) (fun _ : PUnit => eSec G') (fun _ _ => a) ⊓
      LB.wchart L'.L (fun _ : PUnit => eSec G') (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨h1, (mem_wchart x' _ _ _).2 fun _ => hj⟩
  have e := congrArg (fun u => valAt' x' _ (Units.val u)) (hw (fun _ _ => a, fun _ => j))
  refine Eq.trans ?_ (e.trans ((valAt'_mul x' _ _ _).trans (congrArg₂ (· * ·) ?_ (val_res x' _ _ h))))
  · exact ((val_res x' _ _ h).trans ((val_res x' _ _ h1).trans (val_pullU x' m.e _ _))).symm
  · exact val_linCombIso (K := PUnit) w (eSec G') x' (fun _ => a) j h

end Grp

theorem val_secMaps {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} (w : LB.Iso L' (L.pull φ)) (q : Z ⟶ Y)
    (s : LB.Sec (LB.LinComb L' (K := Fin 1) (fun _ => q) (fun _ => 1)))
    (t : LB.Sec (LB.LinComb (L.pull φ) (K := Fin 1) (fun _ => q) (fun _ => 1)))
    (hst : Formalism.L2.Pj.SecMaps (LB.linCombIso w (K := Fin 1) (fun _ => q) (fun _ => 1)) s t)
    (x : Sp ℂ ⟶ Z) (a : L.ι) (j : L'.ι) (ha : ⊤ ≤ ((x ≫ q) ≫ φ) ⁻¹ᵁ L.U a) (hj : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L'.U j) :
    valAt' x (LB.wchart (L.pull φ) (fun _ : Fin 1 => q) (fun _ _ => a)) (t.f (fun _ _ => a)) =
      wv w (x ≫ q) a j * valAt' x (LB.wchart L' (fun _ : Fin 1 => q) (fun _ => j)) (s.f (fun _ => j)) := by
  have h1 : ⊤ ≤ x ⁻¹ᵁ LB.wchart (L.pull φ) (fun _ : Fin 1 => q) (fun _ _ => a) :=
    (mem_wchart x _ _ _).2 fun _ => (mem_wchart _ _ _ _).2 fun _ => ha
  have h : ⊤ ≤ x ⁻¹ᵁ (LB.wchart (L.pull φ) (fun _ : Fin 1 => q) (fun _ _ => a) ⊓
      LB.wchart L' (fun _ : Fin 1 => q) (fun _ => j)) :=
    (top_le_preimage_inf _ _ _).2 ⟨h1, (mem_wchart x _ _ _).2 fun _ => hj⟩
  have e := congrArg (valAt' x _) (hst (fun _ _ => a, fun _ => j))
  refine Eq.trans ?_ (e.trans ((valAt'_mul x _ _ _).trans (congrArg₂ (· * ·) ?_ (valAt'_map x _ _ h))))
  · exact (valAt'_map x _ _ h).symm
  · exact val_linCombIso (K := Fin 1) w q x (fun _ => a) j h

theorem anFib_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, FrOver d y₂ y → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → ∃ A₂ : AnFib X bas idx e x L y₂, (∀ θ, A.Reads 1 y.s θ → A₂.Reads 1 y₂.s θ) ∧ ∃ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk₂ ∧ A₂.Marked mk₂ ∧ MarkOver l d.l₂ L mk mk₂ := by
  intro E _ _ _ H Dw l Xo c n d _ _ _ hlev r g X bas idx e x L y A hsym hx hL y₂ hover mk hmk
  obtain ⟨hb, hu, w, pm, t, hw, hrig, pm1, pm2, hst, hpm⟩ := hover
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv d.m.cart y₂.x y.x hb
  let ex : (Fin g → ℂ) → (ptO d.Xo₂ y₂.x ⟶ d.Xo₂.univ.t.G) := fun z => Φ.symm (A.ex z)
  have hex : ∀ z, (ex z).left ≫ d.m.φ = (A.ex z).left := fun z => by
    rw [← hΦ]
    exact congrArg _ (Φ.apply_symm_apply _)
  have hbase : ∀ z, (ex z).left ≫ d.Xo₂.univ.t.G.hom = y₂.x := fun z => Over.w (ex z)
  have hol : IsHolTo Set.univ (fun z => (ex z).left) := by
    refine HolFibre.isHolTo_of_isPullback d.m.cart.1 ?_ ?_
    · exact (funext hex).symm ▸ A.hol
    · exact (funext hbase).symm ▸ HolFibre.isHolTo_const isOpen_univ _
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_frame Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB hw
    (fun z => (ex z).left) hol A.fr (by simpa only [hex] using A.fr_hol) (by simpa only [hex] using A.fr_ne)
    (by simpa only [hex] using A.fr_g)
  have hch : ∀ z, ∃ a, ⊤ ≤ ((ex z).left ≫ d.m.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U a :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hadd : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => by
    simp only [ex, A.ex_add, map_mul]
  have hker : ∀ z, ex z = 1 ↔ ∃ v ∈ L, z = pv X idx x v := fun z => by
    rw [← A.ex_ker]
    exact Φ.symm.map_eq_one_iff
  have hpv0 : (0 : Fin g → ℂ) = pv X idx x 0 := by
    have := (hx_laws E r X g bas idx 0 hsym Even.zero x hx).2.2.2.2.1 0 0
    rw [zero_smul] at this
    rw [this]
    funext j
    simp
  have hex0 : (ex 0).left = y₂.x ≫ eSec d.Xo₂.univ.t.G := by
    rw [(hker 0).2 ⟨0, L.zero_mem, hpv0⟩]
    exact one_left _
  let A₂ : AnFib X bas idx e x L y₂ :=
    { ex := ex
      ex_add := hadd
      ex_onto := Φ.symm.surjective.comp A.ex_onto
      ex_ker := hker
      ex_lin := fun a z => by
        apply Φ.injective
        apply Over.OverMorphism.ext
        rw [hΦ, hΦ, hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, d.m.act, ← Category.assoc, hex]
      hol := hol
      der := fun ℓ => by
        obtain ⟨v, hv⟩ := VerticalDeriv.exists_isDerivAt0 hol (Pi.single (e.symm ℓ) 1)
        have h1 := FibreDeriv.isDerivAt0_comp hv d.m.φ
        simp only [hex] at h1
        have h2 := VerticalDeriv.isDerivAt0_unique h1 (A.der ℓ)
        have h3 := VerticalDeriv.isDerivAt0_vertical _ _ hbase hv
        have : v = y₂.u ℓ.1 ℓ.2 := d.m.cart.1.hom_ext (h2.trans (hu _ _).symm) (h3.trans (y₂.tan _ _).1.symm)
        exact this ▸ hv
      fr := fr
      fr_hol := fr_hol
      fr_ne := fr_ne
      fr_g := fr_g
      fr_0 := fun j hj => by
        obtain ⟨a, ha⟩ := hch 0
        have h1 := key a j 0 ha hj
        have h2 := A.fr_0 a (hex 0 ▸ ha)
        have h3 := val_rig d.m.cm Xo.univ.t.PP d.Xo₂.univ.t.PP w hrig y₂.x a j (hex0 ▸ ha) (hex0 ▸ hj)
        have h4 : y₂.x ≫ d.m.cm.e = y.x := by rw [d.m.base]; exact hb
        have h5 := wv_ne w ha hj
        erw [h4, ← h2, h1, ← hex0] at h3
        exact mul_left_cancel₀ h5 h3
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv j z hj => by
        obtain ⟨a, ha⟩ := hch z
        have hz : ex (z + pv X idx x v) = ex z := by rw [hadd, (hker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h1 := key a j z ha hj
        have h2 := key a j (z + pv X idx x v) (hz ▸ ha) (hz ▸ hj)
        have h3 := A.fr_per v hv a z (hex z ▸ ha)
        simp only [hz] at h2
        rw [h1, h2] at h3
        apply mul_left_cancel₀ (wv_ne w ha hj)
        rw [h3]
        ring }
  refine ⟨A₂, fun θ hθ j z pt hp1 hp2 hj => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hch z
    have hp1' : pt ≫ (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left = (ex z).left := hp1
    have hq1 : (pt ≫ pm) ≫ gxFst y.x = (A.ex z).left := by
      rw [Category.assoc, gxFst, pm1, ← Category.assoc, hp1', hex]
    have hq2 : (pt ≫ pm) ≫ gxSnd y.x = 𝟙 _ := by
      rw [Category.assoc, gxSnd, pm2]
      exact hp2
    have h1 := hθ a z (pt ≫ pm) hq1 hq2 (hex z ▸ ha)
    have h2 := val_secMaps w _ y₂.s t hst pt a j (hp1' ▸ ha) (hp1' ▸ hj)
    have hle : (LB.LinComb (Xo.univ.t.PP.L.pull d.m.φ) (K := Fin 1)
        (fun _ => (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left) (fun _ => 1)).U (fun _ _ => a) ≤
          pm ⁻¹ᵁ (PPx y.x).U (fun _ => a) := by
      intro p hp
      have h3 : ((snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left ≫ d.m.φ) p ∈ Xo.univ.t.PP.L.U a :=
        Set.mem_iInter.1 (Set.mem_iInter.1 hp 0) ⟨⟩
      rw [← pm1] at h3
      exact Set.mem_iInter.2 fun _ => h3
    have h3 := hpm (fun _ => a) hle
    have hm : ⊤ ≤ pt ⁻¹ᵁ LB.wchart (Xo.univ.t.PP.L.pull d.m.φ)
        (fun _ : Fin 1 => (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left) (fun _ _ => a) :=
      (mem_wchart pt _ _ _).2 fun _ => (mem_wchart _ _ _ _).2 fun _ => hp1' ▸ ha
    have h4 := valAt'_appLE pt pm _ _ hle (y.s.f (fun _ => a)) hm
    have h5 := (h2.symm.trans ((congrArg (valAt' pt _) h3).symm.trans h4)).trans h1
    rw [hp1', key a j z ha hj, zpow_one] at h5
    apply mul_left_cancel₀ (wv_ne w ha hj)
    refine h5.trans ?_
    change _ = _ * (θ z * fr j z ^ (1 : ℤ))
    rw [zpow_one]
    ring
  · obtain ⟨mk₂, h₁, h₂⟩ := GlobalTheory.Dict.exists_mark E H Dw d.l₂ d.Xo₂ d.c₂ r g X bas idx e x L y₂ A₂ hsym hx hL
    refine ⟨mk₂, h₁, h₂, fun a ha => ?_⟩
    obtain ⟨hdvd, hM, hcop, -, -, heta, -⟩ := hlev
    obtain ⟨-, -, -, -, hsm, hinj, -⟩ := hx_laws E r X g bas idx 0 hsym Even.zero x hx
    have ha' : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) :=
      Submodule.smul_mono_left (Ideal.map_mono hdvd.2.1) ha
    have hM0 : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
    have hp0 : (d.pd : E) ≠ 0 := Nat.cast_ne_zero.2 (by
      intro h0
      have := d.l₂.three_le
      rw [hM, h0] at this
      omega)
    have hpadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
      rw [pv, per_add]
      rfl
    have hpow : ∀ (k : ℕ) v, A.ex (pv X idx x ((k : E) • v)) = A.ex (pv X idx x v) ^ k := fun k v => by
      induction k with
      | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact (A.ex_ker _).2 ⟨0, L.zero_mem, rfl⟩
      | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, hpadd, A.ex_add, ih, pow_succ]
    have e1 : Φ (levPt d.Xo₂ y₂.x a) ^ d.pd = levPt Xo y.x a := by
      apply Over.OverMorphism.ext
      rw [← map_pow, hΦ, levPt, levPt, ← MonObj.comp_pow, Over.comp_left, Over.comp_left, Category.assoc, heta.1,
        toUnit_left, toUnit_left, ← hb]
      exact (Category.assoc _ _ _).symm
    have e2 : Φ (levPt d.Xo₂ y₂.x a) = A.ex (pv X idx x (((d.l₂.M : E)⁻¹) • mk₂ a)) := by
      rw [h₂ a ha]
      exact Φ.apply_symm_apply _
    rw [e2, ← hpow, hmk a ha', smul_smul, hM, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ hp0,
      _root_.mul_one] at e1
    have e3 : A.ex (pv X idx x ((l.M : E)⁻¹ • mk₂ a - (l.M : E)⁻¹ • mk a)) = 1 := by
      apply mul_right_cancel (b := A.ex (pv X idx x ((l.M : E)⁻¹ • mk a)))
      rw [← A.ex_add, ← hpadd, sub_add_cancel, _root_.one_mul, e1]
    obtain ⟨u, hu', e4⟩ := (A.ex_ker _).1 e3
    refine ⟨u, hu', ?_⟩
    rw [← hinj e4, ← Nat.cast_smul_eq_nsmul E, ← smul_sub, smul_smul, mul_inv_cancel₀ hM0, one_smul, add_sub_cancel]

end GlobalTheory.Dict.Lift
