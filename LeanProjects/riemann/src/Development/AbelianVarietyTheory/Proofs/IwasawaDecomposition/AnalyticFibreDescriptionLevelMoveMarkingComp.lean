import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPairA

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Dict.Lift

namespace GlobalTheory.Dict.FibreMove

theorem exists_frame_push {X Y : Scheme.{0}} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : LB X}
    {L' : LB Y} (hL : L.IsLB) (hL' : L'.IsLB) {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen)
    (e : V → (Sp ℂ ⟶ Y)) (hol : IsHolTo Set.univ e) (fr : L'.ι → V → ℂ)
    (fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L'.U j})
    (fr_ne : ∀ j z, ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr j z ≠ 0)
    (fr_g : ∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L'.U j ⊓ L'.U j') →
      fr j z = valAt' (e z) (L'.U j ⊓ L'.U j') (L'.g j j').val * fr j' z) :
    ∃ fr' : L.ι → V → ℂ, (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j}) ∧
      (∀ j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U j → fr' j z ≠ 0) ∧
      (∀ j j' z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ (L.U j ⊓ L.U j') →
        fr' j z = valAt' (e z ≫ φ) (L.U j ⊓ L.U j') (L.g j j').val * fr' j' z) ∧
      ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j → fr' a z = wv w (e z) a j * fr j z := by
  choose ch hch using fun z => exists_chart (e z) L' hL'
  have key : ∀ a j z, ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a → ⊤ ≤ e z ⁻¹ᵁ L'.U j →
      wv w (e z) a (ch z) * fr (ch z) z = wv w (e z) a j * fr j z := by
    intro a j z ha hj
    have h0 := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have h2 := valAt'_unit_ne_zero (e z) h0 (L'.g (ch z) j)
    rw [wv_change hw ha ha (hch z) hj, val_g_self _ L hL a ha, fr_g (ch z) j z h0]
    field_simp
  refine ⟨fun a z => wv w (e z) a (ch z) * fr (ch z) z, fun a z₀ hz₀ => ?_, fun a z ha => ?_,
    fun a a' z h => ?_, key⟩
  · have hN := (hol ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) (w.s (fun _ => a, ch z₀)).val)
    have hm := hN.1.mem_nhds (x := z₀) ⟨trivial, mem_both hz₀ (hch z₀)⟩
    have hsub : ∀ z, ⊤ ≤ e z ⁻¹ᵁ ((L.pull φ).U (fun _ => a) ⊓ L'.U (ch z₀)) →
        ⊤ ≤ (e z ≫ φ) ⁻¹ᵁ L.U a ∧ ⊤ ≤ e z ⁻¹ᵁ L'.U (ch z₀) := fun z hz =>
      ⟨(mem_wchart (e z) L _ _).1 ((top_le_preimage_inf _ _ _).1 hz).1 ⟨⟩, ((top_le_preimage_inf _ _ _).1 hz).2⟩
    have d1 : DifferentiableAt ℂ (fr (ch z₀)) z₀ :=
      (fr_hol (ch z₀)).differentiableAt (Filter.mem_of_superset hm fun z hz => (hsub z hz.2).2)
    have d2 : DifferentiableAt ℂ (fun z => wv w (e z) a (ch z₀)) z₀ := hN.2.differentiableAt hm
    refine ((d2.mul d1).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hm] with z hz
    exact key a (ch z₀) z (hsub z hz.2).1 (hsub z hz.2).2
  · exact mul_ne_zero (wv_ne w ha (hch z)) (fr_ne _ z (hch z))
  · obtain ⟨ha, ha'⟩ := (top_le_preimage_inf _ _ _).1 h
    simp only []
    rw [wv_change hw ha ha' (hch z) (hch z), val_g_self _ L' hL' _ (hch z)]
    ring

theorem anFib_levR {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La} {y y' : FrPt Xo c ℂ} (h : levR (gM, gA) y y')
    (A : AnFib X bas idx e x L y) :
    ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧
      ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  obtain ⟨ρ, ν, -, hν, hmv⟩ := h
  obtain ⟨hb, hu, pm, w, hf, hs, hcub, hc⟩ := MoveCalc.frMove_iff_carry.1 hmv
  obtain ⟨hw, hrig, -⟩ := hcub
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv ν.cart y.x y'.x hb.symm
  let ex : (Fin g → ℂ) → (ptO Xo y'.x ⟶ Xo.univ.t.G) := fun z => Φ (A.ex z)
  have hex : ∀ z, (ex z).left = (A.ex z).left ≫ ν.φ := fun z => hΦ _
  obtain ⟨fr, fr_hol, fr_ne, fr_g, key⟩ := exists_frame_push Xo.univ.t.PP.isLB Xo.univ.t.PP.isLB hw
    (fun z => (A.ex z).left) A.hol A.fr A.fr_hol A.fr_ne A.fr_g
  have hch : ∀ z, ∃ j, ⊤ ≤ (A.ex z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j :=
    fun z => exists_chart _ _ Xo.univ.t.PP.isLB
  have hadd : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => by
    simp only [ex, A.ex_add, map_mul]
  have hex0 : (A.ex 0).left = y.x ≫ eSec Xo.univ.t.G := by
    have h0 : A.ex 0 = 1 := by
      have := A.ex_add 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [h0]
    exact one_left _
  let A' : AnFib X bas idx e x L y' :=
    { ex := ex
      ex_add := hadd
      ex_onto := Φ.surjective.comp A.ex_onto
      ex_ker := fun z => by
        rw [← A.ex_ker]
        exact Φ.map_eq_one_iff
      ex_lin := fun a z => by
        apply Over.OverMorphism.ext
        rw [hex, A.ex_lin, Over.comp_left, Over.comp_left, Category.assoc, ν.act, ← Category.assoc, hex]
      hol := (funext hex).symm ▸ PullbackSections.isHolTo_comp A.hol ν.φ
      der := fun ℓ => by
        have h1 := FibreDeriv.isDerivAt0_comp (A.der ℓ) ν.φ
        rw [hu]
        exact (funext hex).symm ▸ h1
      fr := fr
      fr_hol := by simpa only [hex] using fr_hol
      fr_ne := by simpa only [hex] using fr_ne
      fr_g := by simpa only [hex] using fr_g
      fr_0 := fun a ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch 0
        have h1 := key a j 0 ha hj
        have h2 := A.fr_0 j hj
        have h3 := val_rig ν.cm Xo.univ.t.PP Xo.univ.t.PP w hrig y.x a j (hex0 ▸ ha) (hex0 ▸ hj)
        have h4 : y.x ≫ ν.cm.e = y'.x := by rw [ν.base]; exact hb.symm
        erw [h4, ← h2, ← hex0] at h3
        exact h1.trans h3.symm
      χ := A.χ
      χ_norm := A.χ_norm
      fr_per := fun v hv a z ha => by
        rw [hex] at ha
        obtain ⟨j, hj⟩ := hch z
        have hz : A.ex (z + pv X idx x v) = A.ex z := by
          rw [A.ex_add, (A.ex_ker _).2 ⟨v, hv, rfl⟩, _root_.mul_one]
        have h1 := key a j z ha hj
        have h2 := key a j (z + pv X idx x v) (hz ▸ ha) (hz ▸ hj)
        have h3 := A.fr_per v hv j z hj
        simp only [hz] at h2
        rw [h1, h2, h3]
        ring }
  refine ⟨A', fun θ hθ a z pt' hp1 hp2 ha => ?_, fun mk hmk a ha => ?_⟩
  · obtain ⟨j, hj⟩ := hch z
    have ha' : ⊤ ≤ ((A.ex z).left ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U a := hex z ▸ ha
    let pt : Sp ℂ ⟶ Gx y.x := pullback.lift (𝟙 _) (A.ex z).left (by
      rw [Category.id_comp]; exact (Over.w (A.ex z)).symm)
    have e₁ : pt ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (A.ex z).left := pullback.lift_snd _ _ _
    have e₂ : pt ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ := pullback.lift_fst _ _ _
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact hp2.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · refine (hp1.trans (hex z)).trans ?_
        rw [← e₁]
        exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm
    have h1 := hθ j z pt e₁ e₂ hj
    have h2 := MoveValues.val_carry hs hc pt (i := a) (j := j)
      (by rw [e₁]; exact (MoveValues.mem_iff ((A.ex z).left ≫ ν.φ) _).2 ha')
      (by rw [e₁]; exact (MoveValues.mem_iff _ _).2 hj)
    refine h2.trans ?_
    rw [e₁]
    refine (congrArg (wv w (A.ex z).left a j * ·) h1).trans ?_
    change _ = θ z * fr a z ^ (1 : ℤ)
    rw [zpow_one, zpow_one, key a j z ha' hj]
    ring
  · have ha' : gM a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := gM) ha
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    change _ = Φ (A.ex (pv X idx x ((l.M : E)⁻¹ • mk (gM a))))
    rw [← hmk _ ha']
    apply Over.OverMorphism.ext
    rw [hΦ, levPt, levPt, Over.comp_left, Over.comp_left, Category.assoc, hν.2.1, toUnit_left, toUnit_left, hb]
    exact Category.assoc _ _ _

end GlobalTheory.Dict.FibreMove

theorem GlobalTheory.Dict.FibreMove.anFib_levR_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h A => GlobalTheory.Dict.FibreMove.anFib_levR h A
