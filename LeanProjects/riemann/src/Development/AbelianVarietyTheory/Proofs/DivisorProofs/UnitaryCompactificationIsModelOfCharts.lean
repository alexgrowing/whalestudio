import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleOnDescendedGroupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChart

theorem exists_model_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∃ (Y : Model Xo c (RingHom.id c.F)) (ε : Y.X ≅ S), Y.j ≫ ε.hom = j ∧ Y.s = ε.hom ≫ π ≫ zs ∧ ∀ {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → ∀ ξ : Sp (ChartRing k m e) ⟶ S, C.y ≫ j = jK _ ≫ ξ → Nonempty (SABMap C.t Y.t (ξ ≫ ε.inv)) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hsi Z zs i OZ N d J S π j _ BD hU hSep hPre
  obtain ⟨oF, ⟨m0⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ
    (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  obtain ⟨G, _, _, e, hGs, hGp, hGab, hGc⟩ := GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap
  obtain ⟨t, htab, ⟨mt⟩, htc⟩ := GlobalTheory.T.exists_triple_on_descended_group Xo c φ hpq hfan hsi zs i OZ N d J π j BD hU hSep hPre oF.t m0.toSABMap G e hGs hGp hGc
  obtain ⟨⟨-, -, -, -, hiz, -, -⟩, -, -, -, ⟨hNB, hproj, -, hjd, hji, -, -, -⟩, -⟩ := hU
  have eid : spMap (RingHom.id c.F) = 𝟙 _ := by simp [spMap]
  have hid : IsIso (spMap (RingHom.id c.F)) := by rw [eid]; infer_instance
  let g := pullback.fst (π ≫ zs) (spMap (RingHom.id c.F))
  have hg : IsIso g := inferInstance
  let jQ : Xo.XF c ⟶ pullback (π ≫ zs) (spMap (RingHom.id c.F)) := j ≫ inv g
  have hjQ : jQ ≫ g = j := by simp [jQ]
  have hab : abLocus t.G = Set.range j := htab.trans hGab
  let Y : Model Xo c (RingHom.id c.F) :=
    { X := S
      s := π ≫ zs
      normal := (GlobalTheory.isNormalScheme_iff S).1 hNB.1
      proj := hproj
      flat := inferInstance
      jQ := jQ
      jQ_over := by
        rw [← cancel_mono (spMap (RingHom.id c.F)), Category.assoc, ← pullback.condition, ← Category.assoc, hjQ,
          ← Category.assoc, hji, hiz, eid, Category.comp_id]
      jQ_open := inferInstance
      jQ_dense := by
        have hc : (⇑jQ) = (⇑(inv g)) ∘ ⇑j := by
          funext x
          simp [jQ]
        have h1 : DenseRange (⇑(inv g)) := (inv g).surjective.denseRange
        show DenseRange (⇑jQ)
        rw [hc]
        exact h1.comp hjd (inv g).continuous
      t := t
      oF := oF
      m0 := m0
      m := hjQ ▸ mt
      ab_gen := by
        show g ⁻¹' abLocus t.G = Set.range jQ
        rw [hab]
        ext x
        constructor
        · rintro ⟨y, hy⟩
          refine ⟨y, ?_⟩
          have h2 : (inv g) (g x) = x := by
            rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
          rw [← h2, ← hy]
          simp [jQ]
        · rintro ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          rw [← Scheme.Hom.comp_apply, hjQ] }
  refine ⟨Y, Iso.refl S, ?_, ?_, ?_⟩
  · show (jQ ≫ g) ≫ 𝟙 S = j
    rw [hjQ, Category.comp_id]
  · show π ≫ zs = 𝟙 S ≫ π ≫ zs
    rw [Category.id_comp]
  · intro k _ m n C hC ξ hξ
    have := htc C hC ξ hξ
    simpa using this

end GlobalTheory.UChart
