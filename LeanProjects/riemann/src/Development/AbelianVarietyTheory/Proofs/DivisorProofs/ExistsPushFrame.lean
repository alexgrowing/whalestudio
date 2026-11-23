import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000

namespace GlobalTheory.AnMove

open GlobalTheory.Dict.Lift
open scoped MonObj

theorem exists_push_frame {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}} {L : LB Y}
    (hL : L.IsLB) (φ : Y ⟶ Y) (O : L.ι → L.ι → Y.Opens) (ω : ∀ i j, Γ(Y, O i j))
    (hO : ∀ i j (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ φ) ⁻¹ᵁ L.U i ∧ ⊤ ≤ p ⁻¹ᵁ L.U j))
    (hne : ∀ i j (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0)
    (hg : ∀ i j i' j' (p : Sp ℂ ⟶ Y), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' →
      valAt' p (O i j) (ω i j) * valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
        valAt' (p ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * valAt' p (O i' j') (ω i' j'))
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') →
      fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ i, DifferentiableOn ℂ (fr' i) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i}) ∧
      (∀ i z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → fr' i z ≠ 0) ∧
      (∀ i i' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U i ⊓ L.U i') →
        fr' i z = valAt' (e z ≫ φ) (L.U i ⊓ L.U i') (L.g i i').val * fr' i' z) ∧
      ∀ i j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ e z ⁻¹ᵁ L.U j →
        fr' i z = valAt' (e z) (O i j) (ω i j) * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L hL
  have key : ∀ i j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U i → ⊤ ≤ e z ⁻¹ᵁ L.U j →
      valAt' (e z) (O i (ch z)) (ω i (ch z)) * fr (ch z) z = valAt' (e z) (O i j) (ω i j) * fr j z := by
    intro i j z hi hj
    have h1 := hg i (ch z) i j (e z) ((hO _ _ _).2 ⟨hi, hch z⟩) ((hO _ _ _).2 ⟨hi, hj⟩)
    rw [val_g_self _ L hL i hi, _root_.one_mul] at h1
    rw [fr_g (ch z) j z ((top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩), ← mul_assoc, h1]
  refine ⟨fun i z => valAt' (e z) (O i (ch z)) (ω i (ch z)) * fr (ch z) z, fun i z₀ hz₀ => ?_, fun i z hi => ?_,
    fun i i' z h => ?_, key⟩
  · have hN := hol (O i (ch z₀)) (ω i (ch z₀))
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, (hO _ _ _).2 ⟨hz₀, hch z₀⟩⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => ((hO _ _ _).1 hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => valAt' (e z) (O i (ch z₀)) (ω i (ch z₀))) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key i (ch z₀) z ((hO _ _ _).1 hz.2).1 ((hO _ _ _).1 hz.2).2
  · exact mul_ne_zero (hne _ _ _ ((hO _ _ _).2 ⟨hi, hch z⟩)) (fr_ne _ z (hch z))
  · obtain ⟨hi, hi'⟩ := (top_le_preimage_inf _ _ _).1 h
    have h1 := hg i (ch z) i' (ch z) (e z) ((hO _ _ _).2 ⟨hi, hch z⟩) ((hO _ _ _).2 ⟨hi', hch z⟩)
    rw [val_g_self _ L hL _ (hch z), _root_.mul_one] at h1
    simp only []
    rw [h1, mul_assoc]

theorem anFib_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ gM gA : Dw.La →ₗ[𝓞 E] Dw.La, levR (gM, gA) y y' → ∃ A' : AnFib X bas idx e x L y', (∀ θ, A.Reads 1 y.s θ → A'.Reads 1 y'.s θ) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  intro E _ _ _ H Dw l Xo c inst r g X bas idx e x L y y' A hsym hx hL gM gA hR
  obtain ⟨σ, rfl⟩ : ∃ σ : c.F →+* ℂ, inst = σ.toAlgebra :=
    ⟨algebraMap c.F ℂ, Algebra.algebra_ext _ _ fun _ => rfl⟩
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨ρ, ν, -, ⟨-, heta, -⟩, hmv⟩ := hR
  obtain ⟨O, ω, hO, hne, hg, hrig, hs⟩ := GlobalTheory.MoveValues.frMove_values E H Dw l Xo c σ ρ ν y y' hmv
  obtain ⟨hb, hu, -⟩ := hmv
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  have hexf : (fun z => (ex z).left) = fun z => (A.ex z).left ≫ ν.φ := funext hex
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_push_frame Xo.univ.t.PP.isLB ν.φ O ω hO hne hg
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ a, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U a :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := fun z z' => by simp only [ex, A.ex_add, map_mul]
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := hexf ▸ ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        rw [hexf, hu]
        exact FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun i hi => by
        obtain ⟨j, hj⟩ := hch 0
        rw [hex] at hi
        rw [key i j 0 hi hj, A.fr_0 j hj, hb]
        exact (hrig i j y.x _ hex0 ((hO _ _ _).2 ⟨hi, hj⟩)).symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv i z hi => by
        obtain ⟨j, hj⟩ := hch z
        rw [hex] at hi
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h2 := key i j (z + pv X idx x v) (hz ▸ hi) (hz ▸ hj)
        simp only [hz] at h2
        rw [key i j z hi hj, h2, A.fr_per v hv j z hj]
        ring }
  refine ⟨A', fun θ hθ i z pt' hp1 hp2 hi => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have hi' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i := hex z ▸ hi
    let pt : Sp ℂ ⟶ Gx y.x := (CartesianMonoidalCategory.lift (𝟙 (Over.mk y.x)) (A.ex z)).left
    have hq1 : pt ≫ Formalism.L2.PjFree.gxFst y.x = (A.ex z).left :=
      congrArg (·.left) (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk y.x)) (A.ex z))
    have hq2 : pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 _ :=
      congrArg (·.left) (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk y.x)) (A.ex z))
    have h1 := hθ j z pt hq1 hq2 hj
    have h2 := hs i j pt pt' _ hq1 hq2 (hp1.trans (hex z)) hp2 ((hO _ _ _).2 ⟨hi', hj⟩)
    refine h2.trans ((congrArg (_ * ·) h1).trans ?_)
    change _ = θ z * fr i z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key i j z hi' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x (((l.M : E)⁻¹) • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, heta, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.AnMove
